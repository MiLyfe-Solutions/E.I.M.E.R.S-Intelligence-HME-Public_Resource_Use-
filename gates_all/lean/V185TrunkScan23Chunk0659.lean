import V185TrunkScan23Chunk0658

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3895725 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3895725 : Nat := 118140960795 + 3895725 * 2 ^ 59
def prefixEnd_3895725 : Nat := 4983230072969 + 3 ^ 40 * 3895725 * 2
def baseEnd_3895725 : Nat := 2000379422736875691721393

theorem tailTrace_3895725 : CollatzResearch.WordTrace tailWord_3895725 prefixEnd_3895725 2000379422736875691721393 := by
  unfold tailWord_3895725
  simp only [CollatzResearch.WordTrace]
  refine ⟨142088763811461136704936629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94725842540974091136624419 142088763811461136704936629)
  ·
    refine ⟨13320821607324481566087809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142088763811461136704936629 13320821607324481566087809)
    ·
      refine ⟨9990616205493361174565857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13320821607324481566087809 9990616205493361174565857)
      ·
        refine ⟨7492962154120020880924393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9990616205493361174565857 7492962154120020880924393)
        ·
          refine ⟨5619721615590015660693295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7492962154120020880924393 5619721615590015660693295)
          ·
            refine ⟨8429582423385023491039943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619721615590015660693295 8429582423385023491039943)
            ·
              refine ⟨12644373635077535236559915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429582423385023491039943 12644373635077535236559915)
              ·
                refine ⟨18966560452616302854839873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12644373635077535236559915 18966560452616302854839873)
                ·
                  refine ⟨14224920339462227141129905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18966560452616302854839873 14224920339462227141129905)
                  ·
                    refine ⟨10668690254596670355847429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14224920339462227141129905 10668690254596670355847429)
                    ·
                      refine ⟨2000379422736875691721393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10668690254596670355847429 2000379422736875691721393)
                      ·
                        rfl

theorem cell23_3895725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3895725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895725 prefixEnd_3895725 := by exact prefixLift 3895725
  have htrace : WordTrace (prefixWord ++ tailWord_3895725) baseStart_3895725 baseEnd_3895725 := by
    simpa [prefixWord, tailWord_3895725, baseEnd_3895725] using wordTrace_append hprefix tailTrace_3895725
  have hstable : (prefixWord ++ tailWord_3895725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895725).length < 2 ^ (prefixWord ++ tailWord_3895725).sum := by decide
  have hdescent : baseEnd_3895725 < baseStart_3895725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895798 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3895798 : Nat := 118140960795 + 3895798 * 2 ^ 59
def prefixEnd_3895798 : Nat := 4983230072969 + 3 ^ 40 * 3895798 * 2
def baseEnd_3895798 : Nat := 2000416906824653906108557

theorem tailTrace_3895798 : CollatzResearch.WordTrace tailWord_3895798 prefixEnd_3895798 2000416906824653906108557 := by
  unfold tailWord_3895798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880714146262291885771503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94727617560131113448229365 8880714146262291885771503)
  ·
    refine ⟨13321071219393437828657255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880714146262291885771503 13321071219393437828657255)
    ·
      refine ⟨19981606829090156742985883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321071219393437828657255 19981606829090156742985883)
      ·
        refine ⟨29972410243635235114478825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19981606829090156742985883 29972410243635235114478825)
        ·
          refine ⟨22479307682726426335859119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29972410243635235114478825 22479307682726426335859119)
          ·
            refine ⟨33718961524089639503788679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22479307682726426335859119 33718961524089639503788679)
            ·
              refine ⟨50578442286134459255683019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33718961524089639503788679 50578442286134459255683019)
              ·
                refine ⟨75867663429201688883524529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50578442286134459255683019 75867663429201688883524529)
                ·
                  refine ⟨56900747571901266662643397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75867663429201688883524529 56900747571901266662643397)
                  ·
                    refine ⟨10668890169731487499245637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56900747571901266662643397 10668890169731487499245637)
                    ·
                      refine ⟨2000416906824653906108557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10668890169731487499245637 2000416906824653906108557)
                      ·
                        rfl

theorem cell23_3895798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3895798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895798 prefixEnd_3895798 := by exact prefixLift 3895798
  have htrace : WordTrace (prefixWord ++ tailWord_3895798) baseStart_3895798 baseEnd_3895798 := by
    simpa [prefixWord, tailWord_3895798, baseEnd_3895798] using wordTrace_append hprefix tailTrace_3895798
  have hstable : (prefixWord ++ tailWord_3895798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895798).length < 2 ^ (prefixWord ++ tailWord_3895798).sum := by decide
  have hdescent : baseEnd_3895798 < baseStart_3895798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895851 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 6]
def baseStart_3895851 : Nat := 118140960795 + 3895851 * 2 ^ 59
def prefixEnd_3895851 : Nat := 4983230072969 + 3 ^ 40 * 3895851 * 2
def baseEnd_3895851 : Nat := 666814707099780732915271

theorem tailTrace_3895851 : CollatzResearch.WordTrace tailWord_3895851 prefixEnd_3895851 666814707099780732915271 := by
  unfold tailWord_3895851
  simp only [CollatzResearch.WordTrace]
  refine ⟨142093359409004660224023407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94728906272669773482682271 142093359409004660224023407)
  ·
    refine ⟨213140039113506990336035111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142093359409004660224023407 213140039113506990336035111)
    ·
      refine ⟨319710058670260485504052667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213140039113506990336035111 319710058670260485504052667)
      ·
        refine ⟨479565088005390728256079001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319710058670260485504052667 479565088005390728256079001)
        ·
          refine ⟨359673816004043046192059251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479565088005390728256079001 359673816004043046192059251)
          ·
            refine ⟨539510724006064569288088877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359673816004043046192059251 539510724006064569288088877)
            ·
              refine ⟨202316521502274213483033329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539510724006064569288088877 202316521502274213483033329)
              ·
                refine ⟨151737391126705660112274997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202316521502274213483033329 151737391126705660112274997)
                ·
                  refine ⟨14225380418128655635525781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151737391126705660112274997 14225380418128655635525781)
                  ·
                    refine ⟨666814707099780732915271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14225380418128655635525781 666814707099780732915271)
                    ·
                      rfl

theorem cell23_3895851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_3895851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895851 prefixEnd_3895851 := by exact prefixLift 3895851
  have htrace : WordTrace (prefixWord ++ tailWord_3895851) baseStart_3895851 baseEnd_3895851 := by
    simpa [prefixWord, tailWord_3895851, baseEnd_3895851] using wordTrace_append hprefix tailTrace_3895851
  have hstable : (prefixWord ++ tailWord_3895851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895851).length < 2 ^ (prefixWord ++ tailWord_3895851).sum := by decide
  have hdescent : baseEnd_3895851 < baseStart_3895851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895868 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3895868 : Nat := 118140960795 + 3895868 * 2 ^ 59
def prefixEnd_3895868 : Nat := 4983230072969 + 3 ^ 40 * 3895868 * 2
def baseEnd_3895868 : Nat := 666817616823489544077745

theorem tailTrace_3895868 : CollatzResearch.WordTrace tailWord_3895868 prefixEnd_3895868 666817616823489544077745 := by
  unfold tailWord_3895868
  simp only [CollatzResearch.WordTrace]
  refine ⟨71046989724971536063696129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94729319633295381418261505 71046989724971536063696129)
  ·
    refine ⟨53285242293728652047772097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71046989724971536063696129 53285242293728652047772097)
    ·
      refine ⟨39963931720296489035829073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53285242293728652047772097 39963931720296489035829073)
      ·
        refine ⟨29972948790222366776871805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39963931720296489035829073 29972948790222366776871805)
        ·
          refine ⟨11239855796333387541326927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29972948790222366776871805 11239855796333387541326927)
          ·
            refine ⟨16859783694500081311990391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11239855796333387541326927 16859783694500081311990391)
            ·
              refine ⟨25289675541750121967985587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16859783694500081311990391 25289675541750121967985587)
              ·
                refine ⟨37934513312625182951978381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25289675541750121967985587 37934513312625182951978381)
                ·
                  refine ⟨14225442492234443606991893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37934513312625182951978381 14225442492234443606991893)
                  ·
                    refine ⟨666817616823489544077745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14225442492234443606991893 666817616823489544077745)
                    ·
                      rfl

theorem cell23_3895868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3895868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895868 prefixEnd_3895868 := by exact prefixLift 3895868
  have htrace : WordTrace (prefixWord ++ tailWord_3895868) baseStart_3895868 baseEnd_3895868 := by
    simpa [prefixWord, tailWord_3895868, baseEnd_3895868] using wordTrace_append hprefix tailTrace_3895868
  have hstable : (prefixWord ++ tailWord_3895868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895868).length < 2 ^ (prefixWord ++ tailWord_3895868).sum := by decide
  have hdescent : baseEnd_3895868 < baseStart_3895868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895905 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3895905 : Nat := 118140960795 + 3895905 * 2 ^ 59
def prefixEnd_3895905 : Nat := 4983230072969 + 3 ^ 40 * 3895905 * 2
def baseEnd_3895905 : Nat := 2000471849254684987470565

theorem tailTrace_3895905 : CollatzResearch.WordTrace tailWord_3895905 prefixEnd_3895905 2000471849254684987470565 := by
  unfold tailWord_3895905
  simp only [CollatzResearch.WordTrace]
  refine ⟨142095328950809027446489169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94730219300539351630992779 142095328950809027446489169)
  ·
    refine ⟨106571496713106770584866877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142095328950809027446489169 106571496713106770584866877)
    ·
      refine ⟨39964311267415038969325079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106571496713106770584866877 39964311267415038969325079)
      ·
        refine ⟨59946466901122558453987619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39964311267415038969325079 59946466901122558453987619)
        ·
          refine ⟨89919700351683837680981429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59946466901122558453987619 89919700351683837680981429)
          ·
            refine ⟨8429971907970359782592009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89919700351683837680981429 8429971907970359782592009)
            ·
              refine ⟨6322478930977769836944007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8429971907970359782592009 6322478930977769836944007)
              ·
                refine ⟨9483718396466654755416011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322478930977769836944007 9483718396466654755416011)
                ·
                  refine ⟨14225577594699982133124017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9483718396466654755416011 14225577594699982133124017)
                  ·
                    refine ⟨10669183196024986599843013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14225577594699982133124017 10669183196024986599843013)
                    ·
                      refine ⟨2000471849254684987470565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10669183196024986599843013 2000471849254684987470565)
                      ·
                        rfl

theorem cell23_3895905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3895905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895905 prefixEnd_3895905 := by exact prefixLift 3895905
  have htrace : WordTrace (prefixWord ++ tailWord_3895905) baseStart_3895905 baseEnd_3895905 := by
    simpa [prefixWord, tailWord_3895905, baseEnd_3895905] using wordTrace_append hprefix tailTrace_3895905
  have hstable : (prefixWord ++ tailWord_3895905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895905).length < 2 ^ (prefixWord ++ tailWord_3895905).sum := by decide
  have hdescent : baseEnd_3895905 < baseStart_3895905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895909 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_3895909 : Nat := 118140960795 + 3895909 * 2 ^ 59
def prefixEnd_3895909 : Nat := 4983230072969 + 3 ^ 40 * 3895909 * 2
def baseEnd_3895909 : Nat := 2000473903177302971820547

theorem tailTrace_3895909 : CollatzResearch.WordTrace tailWord_3895909 prefixEnd_3895909 2000473903177302971820547 := by
  unfold tailWord_3895909
  simp only [CollatzResearch.WordTrace]
  refine ⟨142095474842794536129634781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94730316561863024086423187 142095474842794536129634781)
  ·
    refine ⟨53285803066047951048613043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142095474842794536129634781 53285803066047951048613043)
    ·
      refine ⟨79928704599071926572919565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53285803066047951048613043 79928704599071926572919565)
      ·
        refine ⟨29973264224651972464844837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79928704599071926572919565 29973264224651972464844837)
        ·
          refine ⟨5619987042122244837158407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29973264224651972464844837 5619987042122244837158407)
          ·
            refine ⟨8429980563183367255737611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5619987042122244837158407 8429980563183367255737611)
            ·
              refine ⟨12644970844775050883606417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8429980563183367255737611 12644970844775050883606417)
              ·
                refine ⟨9483728133581288162704813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12644970844775050883606417 9483728133581288162704813)
                ·
                  refine ⟨3556398050092983061014305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9483728133581288162704813 3556398050092983061014305)
                  ·
                    refine ⟨2667298537569737295760729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3556398050092983061014305 2667298537569737295760729)
                    ·
                      refine ⟨2000473903177302971820547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667298537569737295760729 2000473903177302971820547)
                      ·
                        rfl

theorem cell23_3895909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_3895909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895909 prefixEnd_3895909 := by exact prefixLift 3895909
  have htrace : WordTrace (prefixWord ++ tailWord_3895909) baseStart_3895909 baseEnd_3895909 := by
    simpa [prefixWord, tailWord_3895909, baseEnd_3895909] using wordTrace_append hprefix tailTrace_3895909
  have hstable : (prefixWord ++ tailWord_3895909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895909).length < 2 ^ (prefixWord ++ tailWord_3895909).sum := by decide
  have hdescent : baseEnd_3895909 < baseStart_3895909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895926 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3895926 : Nat := 118140960795 + 3895926 * 2 ^ 59
def prefixEnd_3895926 : Nat := 4983230072969 + 3 ^ 40 * 3895926 * 2
def baseEnd_3895926 : Nat := 2000482632348429405307969

theorem tailTrace_3895926 : CollatzResearch.WordTrace tailWord_3895926 prefixEnd_3895926 2000482632348429405307969 := by
  unfold tailWord_3895926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881005930233309252062727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94730729922488632022002421 8881005930233309252062727)
  ·
    refine ⟨13321508895349963878094091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8881005930233309252062727 13321508895349963878094091)
    ·
      refine ⟨19982263343024945817141137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321508895349963878094091 19982263343024945817141137)
      ·
        refine ⟨14986697507268709362855853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19982263343024945817141137 14986697507268709362855853)
        ·
          refine ⟨5620011565225766011070945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14986697507268709362855853 5620011565225766011070945)
          ·
            refine ⟨4215008673919324508303209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5620011565225766011070945 4215008673919324508303209)
            ·
              refine ⟨3161256505439493381227407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215008673919324508303209 3161256505439493381227407)
              ·
                refine ⟨4741884758159240071841111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161256505439493381227407 4741884758159240071841111)
                ·
                  refine ⟨7112827137238860107761667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741884758159240071841111 7112827137238860107761667)
                  ·
                    refine ⟨10669240705858290161642501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7112827137238860107761667 10669240705858290161642501)
                    ·
                      refine ⟨2000482632348429405307969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10669240705858290161642501 2000482632348429405307969)
                      ·
                        rfl

theorem cell23_3895926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3895926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895926 prefixEnd_3895926 := by exact prefixLift 3895926
  have htrace : WordTrace (prefixWord ++ tailWord_3895926) baseStart_3895926 baseEnd_3895926 := by
    simpa [prefixWord, tailWord_3895926, baseEnd_3895926] using wordTrace_append hprefix tailTrace_3895926
  have hstable : (prefixWord ++ tailWord_3895926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895926).length < 2 ^ (prefixWord ++ tailWord_3895926).sum := by decide
  have hdescent : baseEnd_3895926 < baseStart_3895926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895929 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 1, 2, 3]
def baseStart_3895929 : Nat := 118140960795 + 3895929 * 2 ^ 59
def prefixEnd_3895929 : Nat := 4983230072969 + 3 ^ 40 * 3895929 * 2
def baseEnd_3895929 : Nat := 2000484172790392893570455

theorem tailTrace_3895929 : CollatzResearch.WordTrace tailWord_3895929 prefixEnd_3895929 2000484172790392893570455 := by
  unfold tailWord_3895929
  simp only [CollatzResearch.WordTrace]
  refine ⟨142096204302722079545362841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94730802868481386363575227 142096204302722079545362841)
  ·
    refine ⟨106572153227041559659022131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142096204302722079545362841 106572153227041559659022131)
    ·
      refine ⟨159858229840562339488533197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106572153227041559659022131 159858229840562339488533197)
      ·
        refine ⟨59946836190210877308199949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159858229840562339488533197 59946836190210877308199949)
        ·
          refine ⟨22480063571329078990574981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59946836190210877308199949 22480063571329078990574981)
          ·
            refine ⟨4215011919624202310732809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22480063571329078990574981 4215011919624202310732809)
            ·
              refine ⟨3161258939718151733049607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215011919624202310732809 3161258939718151733049607)
              ·
                refine ⟨4741888409577227599574411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161258939718151733049607 4741888409577227599574411)
                ·
                  refine ⟨7112832614365841399361617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4741888409577227599574411 7112832614365841399361617)
                  ·
                    refine ⟨5334624460774381049521213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7112832614365841399361617 5334624460774381049521213)
                    ·
                      refine ⟨2000484172790392893570455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334624460774381049521213 2000484172790392893570455)
                      ·
                        rfl

theorem cell23_3895929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_3895929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895929 prefixEnd_3895929 := by exact prefixLift 3895929
  have htrace : WordTrace (prefixWord ++ tailWord_3895929) baseStart_3895929 baseEnd_3895929 := by
    simpa [prefixWord, tailWord_3895929, baseEnd_3895929] using wordTrace_append hprefix tailTrace_3895929
  have hstable : (prefixWord ++ tailWord_3895929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895929).length < 2 ^ (prefixWord ++ tailWord_3895929).sum := by decide
  have hdescent : baseEnd_3895929 < baseStart_3895929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895935 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 5, 3, 2]
def baseStart_3895935 : Nat := 118140960795 + 3895935 * 2 ^ 59
def prefixEnd_3895935 : Nat := 4983230072969 + 3 ^ 40 * 3895935 * 2
def baseEnd_3895935 : Nat := 2000487253674319870095427

theorem tailTrace_3895935 : CollatzResearch.WordTrace tailWord_3895935 prefixEnd_3895935 2000487253674319870095427 := by
  unfold tailWord_3895935
  simp only [CollatzResearch.WordTrace]
  refine ⟨142096423140700342570081259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94730948760466895046720839 142096423140700342570081259)
  ·
    refine ⟨213144634711050513855121889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142096423140700342570081259 213144634711050513855121889)
    ·
      refine ⟨159858476033287885391341417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213144634711050513855121889 159858476033287885391341417)
      ·
        refine ⟨119893857024965914043506063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159858476033287885391341417 119893857024965914043506063)
        ·
          refine ⟨179840785537448871065259095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119893857024965914043506063 179840785537448871065259095)
          ·
            refine ⟨269761178306173306597888643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179840785537448871065259095 269761178306173306597888643)
            ·
              refine ⟨404641767459259959896832965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269761178306173306597888643 404641767459259959896832965)
              ·
                refine ⟨75870331398611242480656181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404641767459259959896832965 75870331398611242480656181)
                ·
                  refine ⟨7112843568619803982561517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75870331398611242480656181 7112843568619803982561517)
                  ·
                    refine ⟨2667316338232426493460569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7112843568619803982561517 2667316338232426493460569)
                    ·
                      refine ⟨2000487253674319870095427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667316338232426493460569 2000487253674319870095427)
                      ·
                        rfl

theorem cell23_3895935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_3895935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895935 prefixEnd_3895935 := by exact prefixLift 3895935
  have htrace : WordTrace (prefixWord ++ tailWord_3895935) baseStart_3895935 baseEnd_3895935 := by
    simpa [prefixWord, tailWord_3895935, baseEnd_3895935] using wordTrace_append hprefix tailTrace_3895935
  have hstable : (prefixWord ++ tailWord_3895935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895935).length < 2 ^ (prefixWord ++ tailWord_3895935).sum := by decide
  have hdescent : baseEnd_3895935 < baseStart_3895935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895948 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3895948 : Nat := 118140960795 + 3895948 * 2 ^ 59
def prefixEnd_3895948 : Nat := 4983230072969 + 3 ^ 40 * 3895948 * 2
def baseEnd_3895948 : Nat := 2000493928922828319232867

theorem tailTrace_3895948 : CollatzResearch.WordTrace tailWord_3895948 prefixEnd_3895948 2000493928922828319232867 := by
  unfold tailWord_3895948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71048448644826622895152249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94731264859768830526869665 71048448644826622895152249)
  ·
    refine ⟨53286336483619967171364187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71048448644826622895152249 53286336483619967171364187)
    ·
      refine ⟨79929504725429950757046281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53286336483619967171364187 79929504725429950757046281)
      ·
        refine ⟨59947128544072463067784711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79929504725429950757046281 59947128544072463067784711)
        ·
          refine ⟨89920692816108694601677067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59947128544072463067784711 89920692816108694601677067)
          ·
            refine ⟨134881039224163041902515601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89920692816108694601677067 134881039224163041902515601)
            ·
              refine ⟨101160779418122281426886701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134881039224163041902515601 101160779418122281426886701)
              ·
                refine ⟨37935292281795855535082513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101160779418122281426886701 37935292281795855535082513)
                ·
                  refine ⟨28451469211346891651311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37935292281795855535082513 28451469211346891651311885)
                  ·
                    refine ⟨10669300954255084369241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28451469211346891651311885 10669300954255084369241957)
                    ·
                      refine ⟨2000493928922828319232867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10669300954255084369241957 2000493928922828319232867)
                      ·
                        rfl

theorem cell23_3895948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3895948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895948 prefixEnd_3895948 := by exact prefixLift 3895948
  have htrace : WordTrace (prefixWord ++ tailWord_3895948) baseStart_3895948 baseEnd_3895948 := by
    simpa [prefixWord, tailWord_3895948, baseEnd_3895948] using wordTrace_append hprefix tailTrace_3895948
  have hstable : (prefixWord ++ tailWord_3895948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895948).length < 2 ^ (prefixWord ++ tailWord_3895948).sum := by decide
  have hdescent : baseEnd_3895948 < baseStart_3895948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895959 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3895959 : Nat := 118140960795 + 3895959 * 2 ^ 59
def prefixEnd_3895959 : Nat := 4983230072969 + 3 ^ 40 * 3895959 * 2
def baseEnd_3895959 : Nat := 2000499577210027776195317

theorem tailTrace_3895959 : CollatzResearch.WordTrace tailWord_3895959 prefixEnd_3895959 2000499577210027776195317 := by
  unfold tailWord_3895959
  simp only [CollatzResearch.WordTrace]
  refine ⟨142097298492613394668954931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94731532328408929779303287 142097298492613394668954931)
  ·
    refine ⟨213145947738920092003432397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142097298492613394668954931 213145947738920092003432397)
    ·
      refine ⟨79929730402095034501287149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213145947738920092003432397 79929730402095034501287149)
      ·
        refine ⟨29973648900785637937982681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79929730402095034501287149 29973648900785637937982681)
        ·
          refine ⟨22480236675589228453487011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29973648900785637937982681 22480236675589228453487011)
          ·
            refine ⟨33720355013383842680230517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22480236675589228453487011 33720355013383842680230517)
            ·
              refine ⟨3161283282504735251271611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33720355013383842680230517 3161283282504735251271611)
              ·
                refine ⟨4741924923757102876907417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3161283282504735251271611 4741924923757102876907417)
                ·
                  refine ⟨3556443692817827157680563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4741924923757102876907417 3556443692817827157680563)
                  ·
                    refine ⟨5334665539226740736520845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3556443692817827157680563 5334665539226740736520845)
                    ·
                      refine ⟨2000499577210027776195317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334665539226740736520845 2000499577210027776195317)
                      ·
                        rfl

theorem cell23_3895959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3895959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3895959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3895959 prefixEnd_3895959 := by exact prefixLift 3895959
  have htrace : WordTrace (prefixWord ++ tailWord_3895959) baseStart_3895959 baseEnd_3895959 := by
    simpa [prefixWord, tailWord_3895959, baseEnd_3895959] using wordTrace_append hprefix tailTrace_3895959
  have hstable : (prefixWord ++ tailWord_3895959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895959).length < 2 ^ (prefixWord ++ tailWord_3895959).sum := by decide
  have hdescent : baseEnd_3895959 < baseStart_3895959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896045 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3896045 : Nat := 118140960795 + 3896045 * 2 ^ 59
def prefixEnd_3896045 : Nat := 4983230072969 + 3 ^ 40 * 3896045 * 2
def baseEnd_3896045 : Nat := 2000543736546314439719921

theorem tailTrace_3896045 : CollatzResearch.WordTrace tailWord_3896045 prefixEnd_3896045 2000543736546314439719921 := by
  unfold tailWord_3896045
  simp only [CollatzResearch.WordTrace]
  refine ⟨142100435170301831356585589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94733623446867887571057059 142100435170301831356585589)
  ·
    refine ⟨13321915797215796689679899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142100435170301831356585589 13321915797215796689679899)
    ·
      refine ⟨19982873695823695034519849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321915797215796689679899 19982873695823695034519849)
      ·
        refine ⟨14987155271867771275889887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19982873695823695034519849 14987155271867771275889887)
        ·
          refine ⟨22480732907801656913834831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14987155271867771275889887 22480732907801656913834831)
          ·
            refine ⟨33721099361702485370752247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22480732907801656913834831 33721099361702485370752247)
            ·
              refine ⟨50581649042553728056128371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33721099361702485370752247 50581649042553728056128371)
              ·
                refine ⟨75872473563830592084192557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50581649042553728056128371 75872473563830592084192557)
                ·
                  refine ⟨28452177586436472031572209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75872473563830592084192557 28452177586436472031572209)
                  ·
                    refine ⟨21339133189827354023679157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28452177586436472031572209 21339133189827354023679157)
                    ·
                      refine ⟨2000543736546314439719921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21339133189827354023679157 2000543736546314439719921)
                      ·
                        rfl

theorem cell23_3896045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3896045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896045 prefixEnd_3896045 := by exact prefixLift 3896045
  have htrace : WordTrace (prefixWord ++ tailWord_3896045) baseStart_3896045 baseEnd_3896045 := by
    simpa [prefixWord, tailWord_3896045, baseEnd_3896045] using wordTrace_append hprefix tailTrace_3896045
  have hstable : (prefixWord ++ tailWord_3896045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896045).length < 2 ^ (prefixWord ++ tailWord_3896045).sum := by decide
  have hdescent : baseEnd_3896045 < baseStart_3896045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896062 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3896062 : Nat := 118140960795 + 3896062 * 2 ^ 59
def prefixEnd_3896062 : Nat := 4983230072969 + 3 ^ 40 * 3896062 * 2
def baseEnd_3896062 : Nat := 2000552465717440873207343

theorem tailTrace_3896062 : CollatzResearch.WordTrace tailWord_3896062 prefixEnd_3896062 2000552465717440873207343 := by
  unfold tailWord_3896062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17762631901405030407494305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94734036807493495506636293 17762631901405030407494305)
  ·
    refine ⟨13321973926053772805620729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17762631901405030407494305 13321973926053772805620729)
    ·
      refine ⟨9991480444540329604215547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13321973926053772805620729 9991480444540329604215547)
      ·
        refine ⟨14987220666810494406323321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9991480444540329604215547 14987220666810494406323321)
        ·
          refine ⟨11240415500107870804742491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14987220666810494406323321 11240415500107870804742491)
          ·
            refine ⟨16860623250161806207113737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240415500107870804742491 16860623250161806207113737)
            ·
              refine ⟨12645467437621354655335303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16860623250161806207113737 12645467437621354655335303)
              ·
                refine ⟨18968201156432031983002955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12645467437621354655335303 18968201156432031983002955)
                ·
                  refine ⟨28452301734648047974504433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18968201156432031983002955 28452301734648047974504433)
                  ·
                    refine ⟨21339226300986035980878325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28452301734648047974504433 21339226300986035980878325)
                    ·
                      refine ⟨2000552465717440873207343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21339226300986035980878325 2000552465717440873207343)
                      ·
                        rfl

theorem cell23_3896062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3896062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896062 prefixEnd_3896062 := by exact prefixLift 3896062
  have htrace : WordTrace (prefixWord ++ tailWord_3896062) baseStart_3896062 baseEnd_3896062 := by
    simpa [prefixWord, tailWord_3896062, baseEnd_3896062] using wordTrace_append hprefix tailTrace_3896062
  have hstable : (prefixWord ++ tailWord_3896062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896062).length < 2 ^ (prefixWord ++ tailWord_3896062).sum := by decide
  have hdescent : baseEnd_3896062 < baseStart_3896062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896072 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_3896072 : Nat := 118140960795 + 3896072 * 2 ^ 59
def prefixEnd_3896072 : Nat := 4983230072969 + 3 ^ 40 * 3896072 * 2
def baseEnd_3896072 : Nat := 2000557600523985834082297

theorem tailTrace_3896072 : CollatzResearch.WordTrace tailWord_3896072 prefixEnd_3896072 2000557600523985834082297 := by
  unfold tailWord_3896072
  simp only [CollatzResearch.WordTrace]
  refine ⟨71050709970602007483909235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94734279960802676645212313 71050709970602007483909235)
  ·
    refine ⟨106576064955903011225863853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71050709970602007483909235 106576064955903011225863853)
    ·
      refine ⟨39966024358463629209698945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106576064955903011225863853 39966024358463629209698945)
      ·
        refine ⟨29974518268847721907274209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39966024358463629209698945 29974518268847721907274209)
        ·
          refine ⟨22480888701635791430455657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29974518268847721907274209 22480888701635791430455657)
          ·
            refine ⟨16860666526226843572841743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22480888701635791430455657 16860666526226843572841743)
            ·
              refine ⟨25290999789340265359262615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860666526226843572841743 25290999789340265359262615)
              ·
                refine ⟨37936499684010398038893923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25290999789340265359262615 37936499684010398038893923)
                ·
                  refine ⟨56904749526015597058340885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37936499684010398038893923 56904749526015597058340885)
                  ·
                    refine ⟨2667410134031981112109729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56904749526015597058340885 2667410134031981112109729)
                    ·
                      refine ⟨2000557600523985834082297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667410134031981112109729 2000557600523985834082297)
                      ·
                        rfl

theorem cell23_3896072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_3896072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896072 prefixEnd_3896072 := by exact prefixLift 3896072
  have htrace : WordTrace (prefixWord ++ tailWord_3896072) baseStart_3896072 baseEnd_3896072 := by
    simpa [prefixWord, tailWord_3896072, baseEnd_3896072] using wordTrace_append hprefix tailTrace_3896072
  have hstable : (prefixWord ++ tailWord_3896072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896072).length < 2 ^ (prefixWord ++ tailWord_3896072).sum := by decide
  have hdescent : baseEnd_3896072 < baseStart_3896072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896075 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3]
def baseStart_3896075 : Nat := 118140960795 + 3896075 * 2 ^ 59
def prefixEnd_3896075 : Nat := 4983230072969 + 3 ^ 40 * 3896075 * 2
def baseEnd_3896075 : Nat := 2000559140965949322344783

theorem tailTrace_3896075 : CollatzResearch.WordTrace tailWord_3896075 prefixEnd_3896075 2000559140965949322344783 := by
  unfold tailWord_3896075
  simp only [CollatzResearch.WordTrace]
  refine ⟨142101529360193146480177679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94734352906795430986785119 142101529360193146480177679)
  ·
    refine ⟨213152294040289719720266519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142101529360193146480177679 213152294040289719720266519)
    ·
      refine ⟨319728441060434579580399779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213152294040289719720266519 319728441060434579580399779)
      ·
        refine ⟨479592661590651869370599669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319728441060434579580399779 479592661590651869370599669)
        ·
          refine ⟨44961812024123612753493719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479592661590651869370599669 44961812024123612753493719)
          ·
            refine ⟨67442718036185419130240579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44961812024123612753493719 67442718036185419130240579)
            ·
              refine ⟨101164077054278128695360869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67442718036185419130240579 101164077054278128695360869)
              ·
                refine ⟨18968264447677149130380163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101164077054278128695360869 18968264447677149130380163)
                ·
                  refine ⟨28452396671515723695570245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18968264447677149130380163 28452396671515723695570245)
                  ·
                    refine ⟨5334824375909198192919421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28452396671515723695570245 5334824375909198192919421)
                    ·
                      refine ⟨2000559140965949322344783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334824375909198192919421 2000559140965949322344783)
                      ·
                        rfl

theorem cell23_3896075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 3].length) (baseStart_3896075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896075 prefixEnd_3896075 := by exact prefixLift 3896075
  have htrace : WordTrace (prefixWord ++ tailWord_3896075) baseStart_3896075 baseEnd_3896075 := by
    simpa [prefixWord, tailWord_3896075, baseEnd_3896075] using wordTrace_append hprefix tailTrace_3896075
  have hstable : (prefixWord ++ tailWord_3896075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896075).length < 2 ^ (prefixWord ++ tailWord_3896075).sum := by decide
  have hdescent : baseEnd_3896075 < baseStart_3896075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896092 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3896092 : Nat := 118140960795 + 3896092 * 2 ^ 59
def prefixEnd_3896092 : Nat := 4983230072969 + 3 ^ 40 * 3896092 * 2
def baseEnd_3896092 : Nat := 2000567870137075755832205

theorem tailTrace_3896092 : CollatzResearch.WordTrace tailWord_3896092 prefixEnd_3896092 2000567870137075755832205 := by
  unfold tailWord_3896092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71051074700565779191773265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94734766267421038922364353 71051074700565779191773265)
  ·
    refine ⟨53288306025424334393829949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71051074700565779191773265 53288306025424334393829949)
    ·
      refine ⟨19983114759534125397686231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53288306025424334393829949 19983114759534125397686231)
      ·
        refine ⟨29974672139301188096529347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19983114759534125397686231 29974672139301188096529347)
        ·
          refine ⟨44962008208951782144794021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29974672139301188096529347 44962008208951782144794021)
          ·
            refine ⟨8430376539178459152148879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44962008208951782144794021 8430376539178459152148879)
            ·
              refine ⟨12645564808767688728223319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430376539178459152148879 12645564808767688728223319)
              ·
                refine ⟨18968347213151533092334979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12645564808767688728223319 18968347213151533092334979)
                ·
                  refine ⟨28452520819727299638502469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18968347213151533092334979 28452520819727299638502469)
                  ·
                    refine ⟨5334847653698868682219213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28452520819727299638502469 5334847653698868682219213)
                    ·
                      refine ⟨2000567870137075755832205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334847653698868682219213 2000567870137075755832205)
                      ·
                        rfl

theorem cell23_3896092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3896092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896092 prefixEnd_3896092 := by exact prefixLift 3896092
  have htrace : WordTrace (prefixWord ++ tailWord_3896092) baseStart_3896092 baseEnd_3896092 := by
    simpa [prefixWord, tailWord_3896092, baseEnd_3896092] using wordTrace_append hprefix tailTrace_3896092
  have hstable : (prefixWord ++ tailWord_3896092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896092).length < 2 ^ (prefixWord ++ tailWord_3896092).sum := by decide
  have hdescent : baseEnd_3896092 < baseStart_3896092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896115 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_3896115 : Nat := 118140960795 + 3896115 * 2 ^ 59
def prefixEnd_3896115 : Nat := 4983230072969 + 3 ^ 40 * 3896115 * 2
def baseEnd_3896115 : Nat := 2000579680192129165844599

theorem tailTrace_3896115 : CollatzResearch.WordTrace tailWord_3896115 prefixEnd_3896115 2000579680192129165844599 := by
  unfold tailWord_3896115
  simp only [CollatzResearch.WordTrace]
  refine ⟨142102988280048233311633799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94735325520032155541089199 142102988280048233311633799)
  ·
    refine ⟨213154482420072349967450699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142102988280048233311633799 213154482420072349967450699)
    ·
      refine ⟨319731723630108524951176049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213154482420072349967450699 319731723630108524951176049)
      ·
        refine ⟨239798792722581393713382037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319731723630108524951176049 239798792722581393713382037)
        ·
          refine ⟨11240568408871002830314783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239798792722581393713382037 11240568408871002830314783)
          ·
            refine ⟨16860852613306504245472175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240568408871002830314783 16860852613306504245472175)
            ·
              refine ⟨25291278919959756368208263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16860852613306504245472175 25291278919959756368208263)
              ·
                refine ⟨37936918379939634552312395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25291278919959756368208263 37936918379939634552312395)
                ·
                  refine ⟨56905377569909451828468593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37936918379939634552312395 56905377569909451828468593)
                  ·
                    refine ⟨42679033177432088871351445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56905377569909451828468593 42679033177432088871351445)
                    ·
                      refine ⟨2000579680192129165844599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42679033177432088871351445 2000579680192129165844599)
                      ·
                        rfl

theorem cell23_3896115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_3896115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896115 prefixEnd_3896115 := by exact prefixLift 3896115
  have htrace : WordTrace (prefixWord ++ tailWord_3896115) baseStart_3896115 baseEnd_3896115 := by
    simpa [prefixWord, tailWord_3896115, baseEnd_3896115] using wordTrace_append hprefix tailTrace_3896115
  have hstable : (prefixWord ++ tailWord_3896115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896115).length < 2 ^ (prefixWord ++ tailWord_3896115).sum := by decide
  have hdescent : baseEnd_3896115 < baseStart_3896115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896116 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3896116 : Nat := 118140960795 + 3896116 * 2 ^ 59
def prefixEnd_3896116 : Nat := 4983230072969 + 3 ^ 40 * 3896116 * 2
def baseEnd_3896116 : Nat := 666860064557594553977365

theorem tailTrace_3896116 : CollatzResearch.WordTrace tailWord_3896116 prefixEnd_3896116 666860064557594553977365 := by
  unfold tailWord_3896116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71051512376522305241210101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94735349835363073654946801 71051512376522305241210101)
  ·
    refine ⟨6661079285298966116363447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71051512376522305241210101 6661079285298966116363447)
    ·
      refine ⟨9991618927948449174545171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661079285298966116363447 9991618927948449174545171)
      ·
        refine ⟨14987428391922673761817757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9991618927948449174545171 14987428391922673761817757)
        ·
          refine ⟨5620285646971002660681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14987428391922673761817757 5620285646971002660681659)
          ·
            refine ⟨8430428470456503991022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620285646971002660681659 8430428470456503991022489)
            ·
              refine ⟨6322821352842377993266867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8430428470456503991022489 6322821352842377993266867)
              ·
                refine ⟨9484232029263566989900301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6322821352842377993266867 9484232029263566989900301)
                ·
                  refine ⟨3556587010973837621212613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9484232029263566989900301 3556587010973837621212613)
                  ·
                    refine ⟨666860064557594553977365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556587010973837621212613 666860064557594553977365)
                    ·
                      rfl

theorem cell23_3896116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3896116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896116 prefixEnd_3896116 := by exact prefixLift 3896116
  have htrace : WordTrace (prefixWord ++ tailWord_3896116) baseStart_3896116 baseEnd_3896116 := by
    simpa [prefixWord, tailWord_3896116, baseEnd_3896116] using wordTrace_append hprefix tailTrace_3896116
  have hstable : (prefixWord ++ tailWord_3896116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896116).length < 2 ^ (prefixWord ++ tailWord_3896116).sum := by decide
  have hdescent : baseEnd_3896116 < baseStart_3896116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896149 : List Nat := [1, 3, 2, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3896149 : Nat := 118140960795 + 3896149 * 2 ^ 59
def prefixEnd_3896149 : Nat := 4983230072969 + 3 ^ 40 * 3896149 * 2
def baseEnd_3896149 : Nat := 2000597138534382032819443

theorem tailTrace_3896149 : CollatzResearch.WordTrace tailWord_3896149 prefixEnd_3896149 2000597138534382032819443 := by
  unfold tailWord_3896149
  simp only [CollatzResearch.WordTrace]
  refine ⟨142104228361925057118371501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94736152241283371412247667 142104228361925057118371501)
  ·
    refine ⟨53289085635721896419389313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142104228361925057118371501 53289085635721896419389313)
    ·
      refine ⟨39966814226791422314541985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53289085635721896419389313 39966814226791422314541985)
      ·
        refine ⟨29975110670093566735906489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39966814226791422314541985 29975110670093566735906489)
        ·
          refine ⟨22481333002570175051929867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29975110670093566735906489 22481333002570175051929867)
          ·
            refine ⟨33721999503855262577894801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22481333002570175051929867 33721999503855262577894801)
            ·
              refine ⟨25291499627891446933421101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33721999503855262577894801 25291499627891446933421101)
              ·
                refine ⟨9484312360459292600032913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25291499627891446933421101 9484312360459292600032913)
                ·
                  refine ⟨7113234270344469450024685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9484312360459292600032913 7113234270344469450024685)
                  ·
                    refine ⟨2667462851379176043759257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7113234270344469450024685 2667462851379176043759257)
                    ·
                      refine ⟨2000597138534382032819443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667462851379176043759257 2000597138534382032819443)
                      ·
                        rfl

theorem cell23_3896149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3896149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896149 prefixEnd_3896149 := by exact prefixLift 3896149
  have htrace : WordTrace (prefixWord ++ tailWord_3896149) baseStart_3896149 baseEnd_3896149 := by
    simpa [prefixWord, tailWord_3896149, baseEnd_3896149] using wordTrace_append hprefix tailTrace_3896149
  have hstable : (prefixWord ++ tailWord_3896149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896149).length < 2 ^ (prefixWord ++ tailWord_3896149).sum := by decide
  have hdescent : baseEnd_3896149 < baseStart_3896149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896172 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_3896172 : Nat := 118140960795 + 3896172 * 2 ^ 59
def prefixEnd_3896172 : Nat := 4983230072969 + 3 ^ 40 * 3896172 * 2
def baseEnd_3896172 : Nat := 666869649529811814277279

theorem tailTrace_3896172 : CollatzResearch.WordTrace tailWord_3896172 prefixEnd_3896172 666869649529811814277279 := by
  unfold tailWord_3896172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71052533620420866023229385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94736711493894488030972513 71052533620420866023229385)
  ·
    refine ⟨53289400215315649517422039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71052533620420866023229385 53289400215315649517422039)
    ·
      refine ⟨79934100322973474276133059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53289400215315649517422039 79934100322973474276133059)
      ·
        refine ⟨119901150484460211414199589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79934100322973474276133059 119901150484460211414199589)
        ·
          refine ⟨22481465715836289640162423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119901150484460211414199589 22481465715836289640162423)
          ·
            refine ⟨33722198573754434460243635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22481465715836289640162423 33722198573754434460243635)
            ·
              refine ⟨50583297860631651690365453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33722198573754434460243635 50583297860631651690365453)
              ·
                refine ⟨18968736697736869383887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50583297860631651690365453 18968736697736869383887045)
                ·
                  refine ⟨3556638130825663009478821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18968736697736869383887045 3556638130825663009478821)
                  ·
                    refine ⟨666869649529811814277279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556638130825663009478821 666869649529811814277279)
                    ·
                      rfl

theorem cell23_3896172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_3896172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896172 prefixEnd_3896172 := by exact prefixLift 3896172
  have htrace : WordTrace (prefixWord ++ tailWord_3896172) baseStart_3896172 baseEnd_3896172 := by
    simpa [prefixWord, tailWord_3896172, baseEnd_3896172] using wordTrace_append hprefix tailTrace_3896172
  have hstable : (prefixWord ++ tailWord_3896172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896172).length < 2 ^ (prefixWord ++ tailWord_3896172).sum := by decide
  have hdescent : baseEnd_3896172 < baseStart_3896172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896185 : List Nat := [1, 2, 1, 3, 2, 3, 1, 10]
def baseStart_3896185 : Nat := 118140960795 + 3896185 * 2 ^ 59
def prefixEnd_3896185 : Nat := 4983230072969 + 3 ^ 40 * 3896185 * 2
def baseEnd_3896185 : Nat := 74096874956960884887751

theorem tailTrace_3896185 : CollatzResearch.WordTrace tailWord_3896185 prefixEnd_3896185 74096874956960884887751 := by
  unfold tailWord_3896185
  simp only [CollatzResearch.WordTrace]
  refine ⟨142105541389794635266682009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94737027593196423511121339 142105541389794635266682009)
  ·
    refine ⟨106579156042345976450011507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142105541389794635266682009 106579156042345976450011507)
    ·
      refine ⟨159868734063518964675017261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106579156042345976450011507 159868734063518964675017261)
      ·
        refine ⟨59950775273819611753131473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159868734063518964675017261 59950775273819611753131473)
        ·
          refine ⟨44963081455364708814848605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59950775273819611753131473 44963081455364708814848605)
          ·
            refine ⟨16861155545761765805568227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44963081455364708814848605 16861155545761765805568227)
            ·
              refine ⟨25291733318642648708352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16861155545761765805568227 25291733318642648708352341)
              ·
                refine ⟨74096874956960884887751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25291733318642648708352341 74096874956960884887751)
                ·
                  rfl

theorem cell23_3896185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 10].length) (baseStart_3896185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896185 prefixEnd_3896185 := by exact prefixLift 3896185
  have htrace : WordTrace (prefixWord ++ tailWord_3896185) baseStart_3896185 baseEnd_3896185 := by
    simpa [prefixWord, tailWord_3896185, baseEnd_3896185] using wordTrace_append hprefix tailTrace_3896185
  have hstable : (prefixWord ++ tailWord_3896185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896185).length < 2 ^ (prefixWord ++ tailWord_3896185).sum := by decide
  have hdescent : baseEnd_3896185 < baseStart_3896185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896199 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3896199 : Nat := 118140960795 + 3896199 * 2 ^ 59
def prefixEnd_3896199 : Nat := 4983230072969 + 3 ^ 40 * 3896199 * 2
def baseEnd_3896199 : Nat := 2000622812567106837194213

theorem tailTrace_3896199 : CollatzResearch.WordTrace tailWord_3896199 prefixEnd_3896199 2000622812567106837194213 := by
  unfold tailWord_3896199
  simp only [CollatzResearch.WordTrace]
  refine ⟨142106052011743915657691651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94737368007829277105127767 142106052011743915657691651)
  ·
    refine ⟨213159078017615873486537477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142106052011743915657691651 213159078017615873486537477)
    ·
      refine ⟨39967327128302976278725777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213159078017615873486537477 39967327128302976278725777)
      ·
        refine ⟨29975495346227232209044333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39967327128302976278725777 29975495346227232209044333)
        ·
          refine ⟨11240810754835212078391625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29975495346227232209044333 11240810754835212078391625)
          ·
            refine ⟨8430608066126409058793719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11240810754835212078391625 8430608066126409058793719)
            ·
              refine ⟨12645912099189613588190579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8430608066126409058793719 12645912099189613588190579)
              ·
                refine ⟨18968868148784420382285869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12645912099189613588190579 18968868148784420382285869)
                ·
                  refine ⟨7113325555794157643357201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18968868148784420382285869 7113325555794157643357201)
                  ·
                    refine ⟨5334994166845618232517901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7113325555794157643357201 5334994166845618232517901)
                    ·
                      refine ⟨2000622812567106837194213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5334994166845618232517901 2000622812567106837194213)
                      ·
                        rfl

theorem cell23_3896199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3896199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896199 prefixEnd_3896199 := by exact prefixLift 3896199
  have htrace : WordTrace (prefixWord ++ tailWord_3896199) baseStart_3896199 baseEnd_3896199 := by
    simpa [prefixWord, tailWord_3896199, baseEnd_3896199] using wordTrace_append hprefix tailTrace_3896199
  have hstable : (prefixWord ++ tailWord_3896199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896199).length < 2 ^ (prefixWord ++ tailWord_3896199).sum := by decide
  have hdescent : baseEnd_3896199 < baseStart_3896199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896202 : List Nat := [3, 1, 2, 4, 1, 1, 2, 9]
def baseStart_3896202 : Nat := 118140960795 + 3896202 * 2 ^ 59
def prefixEnd_3896202 : Nat := 4983230072969 + 3 ^ 40 * 3896202 * 2
def baseEnd_3896202 : Nat := 74097198259595197239137

theorem tailTrace_3896202 : CollatzResearch.WordTrace tailWord_3896202 prefixEnd_3896202 74097198259595197239137 := by
  unfold tailWord_3896202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35526540357683261792512715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94737440953822031446700573 35526540357683261792512715)
  ·
    refine ⟨53289810536524892688769073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35526540357683261792512715 53289810536524892688769073)
    ·
      refine ⟨39967357902393669516576805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53289810536524892688769073 39967357902393669516576805)
      ·
        refine ⟨7493879606698813034358151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39967357902393669516576805 7493879606698813034358151)
        ·
          refine ⟨11240819410048219551537227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7493879606698813034358151 11240819410048219551537227)
          ·
            refine ⟨16861229115072329327305841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11240819410048219551537227 16861229115072329327305841)
            ·
              refine ⟨12645921836304246995479381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16861229115072329327305841 12645921836304246995479381)
              ·
                refine ⟨74097198259595197239137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12645921836304246995479381 74097198259595197239137)
                ·
                  rfl

theorem cell23_3896202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_3896202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896202 prefixEnd_3896202 := by exact prefixLift 3896202
  have htrace : WordTrace (prefixWord ++ tailWord_3896202) baseStart_3896202 baseEnd_3896202 := by
    simpa [prefixWord, tailWord_3896202, baseEnd_3896202] using wordTrace_append hprefix tailTrace_3896202
  have hstable : (prefixWord ++ tailWord_3896202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896202).length < 2 ^ (prefixWord ++ tailWord_3896202).sum := by decide
  have hdescent : baseEnd_3896202 < baseStart_3896202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896343 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 5]
def baseStart_3896343 : Nat := 118140960795 + 3896343 * 2 ^ 59
def prefixEnd_3896343 : Nat := 4983230072969 + 3 ^ 40 * 3896343 * 2
def baseEnd_3896343 : Nat := 222299639309039363754839

theorem tailTrace_3896343 : CollatzResearch.WordTrace tailWord_3896343 prefixEnd_3896343 222299639309039363754839 := by
  unfold tailWord_3896343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142111304123222228250933683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94740869415481485500622455 142111304123222228250933683)
  ·
    refine ⟨213166956184833342376400525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142111304123222228250933683 213166956184833342376400525)
    ·
      refine ⟨79937608569312503391150197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213166956184833342376400525 79937608569312503391150197)
      ·
        refine ⟨7494150803373047192920331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79937608569312503391150197 7494150803373047192920331)
        ·
          refine ⟨11241226205059570789380497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7494150803373047192920331 11241226205059570789380497)
          ·
            refine ⟨8430919653794678092035373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241226205059570789380497 8430919653794678092035373)
            ·
              refine ⟨3161594870173004284513265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8430919653794678092035373 3161594870173004284513265)
              ·
                refine ⟨2371196152629753213384949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161594870173004284513265 2371196152629753213384949)
                ·
                  refine ⟨222299639309039363754839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2371196152629753213384949 222299639309039363754839)
                  ·
                    rfl

theorem cell23_3896343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 5].length) (baseStart_3896343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896343 prefixEnd_3896343 := by exact prefixLift 3896343
  have htrace : WordTrace (prefixWord ++ tailWord_3896343) baseStart_3896343 baseEnd_3896343 := by
    simpa [prefixWord, tailWord_3896343, baseEnd_3896343] using wordTrace_append hprefix tailTrace_3896343
  have hstable : (prefixWord ++ tailWord_3896343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896343).length < 2 ^ (prefixWord ++ tailWord_3896343).sum := by decide
  have hdescent : baseEnd_3896343 < baseStart_3896343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896369 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_3896369 : Nat := 118140960795 + 3896369 * 2 ^ 59
def prefixEnd_3896369 : Nat := 4983230072969 + 3 ^ 40 * 3896369 * 2
def baseEnd_3896369 : Nat := 666903368092790390689477

theorem tailTrace_3896369 : CollatzResearch.WordTrace tailWord_3896369 prefixEnd_3896369 666903368092790390689477 := by
  unfold tailWord_3896369
  simp only [CollatzResearch.WordTrace]
  refine ⟨142112252421128034691380161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94741501614085356460920107 142112252421128034691380161)
  ·
    refine ⟨106584189315846026018535121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142112252421128034691380161 106584189315846026018535121)
    ·
      refine ⟨79938141986884519513901341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106584189315846026018535121 79938141986884519513901341)
      ·
        refine ⟨29976803245081694817713003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79938141986884519513901341 29976803245081694817713003)
        ·
          refine ⟨44965204867622542226569505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29976803245081694817713003 44965204867622542226569505)
          ·
            refine ⟨33723903650716906669927129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44965204867622542226569505 33723903650716906669927129)
            ·
              refine ⟨25292927738037680002445347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33723903650716906669927129 25292927738037680002445347)
              ·
                refine ⟨37939391607056520003668021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25292927738037680002445347 37939391607056520003668021)
                ·
                  refine ⟨3556817963161548750343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37939391607056520003668021 3556817963161548750343877)
                  ·
                    refine ⟨666903368092790390689477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556817963161548750343877 666903368092790390689477)
                    ·
                      rfl

theorem cell23_3896369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_3896369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896369 prefixEnd_3896369 := by exact prefixLift 3896369
  have htrace : WordTrace (prefixWord ++ tailWord_3896369) baseStart_3896369 baseEnd_3896369 := by
    simpa [prefixWord, tailWord_3896369, baseEnd_3896369] using wordTrace_append hprefix tailTrace_3896369
  have hstable : (prefixWord ++ tailWord_3896369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896369).length < 2 ^ (prefixWord ++ tailWord_3896369).sum := by decide
  have hdescent : baseEnd_3896369 < baseStart_3896369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896376 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_3896376 : Nat := 118140960795 + 3896376 * 2 ^ 59
def prefixEnd_3896376 : Nat := 4983230072969 + 3 ^ 40 * 3896376 * 2
def baseEnd_3896376 : Nat := 2000713698642952644680899

theorem tailTrace_3896376 : CollatzResearch.WordTrace tailWord_3896376 prefixEnd_3896376 2000713698642952644680899 := by
  unfold tailWord_3896376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71056253866051337443442491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94741671821401783257923321 71056253866051337443442491)
  ·
    refine ⟨106584380799077006165163737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71056253866051337443442491 106584380799077006165163737)
    ·
      refine ⟨79938285599307754623872803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106584380799077006165163737 79938285599307754623872803)
      ·
        refine ⟨119907428398961631935809205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79938285599307754623872803 119907428398961631935809205)
        ·
          refine ⟨11241321412402652993982113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119907428398961631935809205 11241321412402652993982113)
          ·
            refine ⟨8430991059301989745486585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11241321412402652993982113 8430991059301989745486585)
            ·
              refine ⟨6323243294476492309114939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8430991059301989745486585 6323243294476492309114939)
              ·
                refine ⟨9484864941714738463672409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323243294476492309114939 9484864941714738463672409)
                ·
                  refine ⟨7113648706286053847754307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9484864941714738463672409 7113648706286053847754307)
                  ·
                    refine ⟨10670473059429080771631461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7113648706286053847754307 10670473059429080771631461)
                    ·
                      refine ⟨2000713698642952644680899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10670473059429080771631461 2000713698642952644680899)
                      ·
                        rfl

theorem cell23_3896376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_3896376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896376 prefixEnd_3896376 := by exact prefixLift 3896376
  have htrace : WordTrace (prefixWord ++ tailWord_3896376) baseStart_3896376 baseEnd_3896376 := by
    simpa [prefixWord, tailWord_3896376, baseEnd_3896376] using wordTrace_append hprefix tailTrace_3896376
  have hstable : (prefixWord ++ tailWord_3896376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896376).length < 2 ^ (prefixWord ++ tailWord_3896376).sum := by decide
  have hdescent : baseEnd_3896376 < baseStart_3896376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896437 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3896437 : Nat := 118140960795 + 3896437 * 2 ^ 59
def prefixEnd_3896437 : Nat := 4983230072969 + 3 ^ 40 * 3896437 * 2
def baseEnd_3896437 : Nat := 666915006987625635339373

theorem tailTrace_3896437 : CollatzResearch.WordTrace tailWord_3896437 prefixEnd_3896437 666915006987625635339373 := by
  unfold tailWord_3896437
  simp only [CollatzResearch.WordTrace]
  refine ⟨142114732584881682304855565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94743155056587788203237043 142114732584881682304855565)
  ·
    refine ⟨53293024719330630864320837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142114732584881682304855565 53293024719330630864320837)
    ·
      refine ⟨9992442134874493287060157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53293024719330630864320837 9992442134874493287060157)
      ·
        refine ⟨3747165800577934982647559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9992442134874493287060157 3747165800577934982647559)
        ·
          refine ⟨5620748700866902473971339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747165800577934982647559 5620748700866902473971339)
          ·
            refine ⟨8431123051300353710957009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5620748700866902473971339 8431123051300353710957009)
            ·
              refine ⟨6323342288475265283217757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431123051300353710957009 6323342288475265283217757)
              ·
                refine ⟨2371253358178224481206659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6323342288475265283217757 2371253358178224481206659)
                ·
                  refine ⟨3556880037267336721809989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371253358178224481206659 3556880037267336721809989)
                  ·
                    refine ⟨666915006987625635339373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3556880037267336721809989 666915006987625635339373)
                    ·
                      rfl

theorem cell23_3896437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3896437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896437 prefixEnd_3896437 := by exact prefixLift 3896437
  have htrace : WordTrace (prefixWord ++ tailWord_3896437) baseStart_3896437 baseEnd_3896437 := by
    simpa [prefixWord, tailWord_3896437, baseEnd_3896437] using wordTrace_append hprefix tailTrace_3896437
  have hstable : (prefixWord ++ tailWord_3896437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896437).length < 2 ^ (prefixWord ++ tailWord_3896437).sum := by decide
  have hdescent : baseEnd_3896437 < baseStart_3896437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896469 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3896469 : Nat := 118140960795 + 3896469 * 2 ^ 59
def prefixEnd_3896469 : Nat := 4983230072969 + 3 ^ 40 * 3896469 * 2
def baseEnd_3896469 : Nat := 2000761452343820780817971

theorem tailTrace_3896469 : CollatzResearch.WordTrace tailWord_3896469 prefixEnd_3896469 2000761452343820780817971 := by
  unfold tailWord_3896469
  simp only [CollatzResearch.WordTrace]
  refine ⟨142115899720765751770020461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94743933147177167846680307 142115899720765751770020461)
  ·
    refine ⟨53293462395287156913757673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142115899720765751770020461 53293462395287156913757673)
    ·
      refine ⟨39970096796465367685318255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53293462395287156913757673 39970096796465367685318255)
      ·
        refine ⟨59955145194698051527977383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39970096796465367685318255 59955145194698051527977383)
        ·
          refine ⟨89932717792047077291966075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59955145194698051527977383 89932717792047077291966075)
          ·
            refine ⟨134899076688070615937949113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89932717792047077291966075 134899076688070615937949113)
            ·
              refine ⟨101174307516052961953461835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134899076688070615937949113 101174307516052961953461835)
              ·
                refine ⟨151761461274079442930192753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101174307516052961953461835 151761461274079442930192753)
                ·
                  refine ⟨113821095955559582197644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151761461274079442930192753 113821095955559582197644565)
                  ·
                    refine ⟨5335363872916855415514589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113821095955559582197644565 5335363872916855415514589)
                    ·
                      refine ⟨2000761452343820780817971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5335363872916855415514589 2000761452343820780817971)
                      ·
                        rfl

theorem cell23_3896469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3896469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896469 prefixEnd_3896469 := by exact prefixLift 3896469
  have htrace : WordTrace (prefixWord ++ tailWord_3896469) baseStart_3896469 baseEnd_3896469 := by
    simpa [prefixWord, tailWord_3896469, baseEnd_3896469] using wordTrace_append hprefix tailTrace_3896469
  have hstable : (prefixWord ++ tailWord_3896469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896469).length < 2 ^ (prefixWord ++ tailWord_3896469).sum := by decide
  have hdescent : baseEnd_3896469 < baseStart_3896469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896476 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3896476 : Nat := 118140960795 + 3896476 * 2 ^ 59
def prefixEnd_3896476 : Nat := 4983230072969 + 3 ^ 40 * 3896476 * 2
def baseEnd_3896476 : Nat := 666921682236134084476813

theorem tailTrace_3896476 : CollatzResearch.WordTrace tailWord_3896476 prefixEnd_3896476 666921682236134084476813 := by
  unfold tailWord_3896476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71058077515870195982762641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94744103354493594643683521 71058077515870195982762641)
  ·
    refine ⟨53293558136902646987071981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71058077515870195982762641 53293558136902646987071981)
    ·
      refine ⟨19985084301338492620151993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53293558136902646987071981 19985084301338492620151993)
      ·
        refine ⟨14988813226003869465113995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19985084301338492620151993 14988813226003869465113995)
        ·
          refine ⟨22483219839005804197670993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14988813226003869465113995 22483219839005804197670993)
          ·
            refine ⟨16862414879254353148253245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22483219839005804197670993 16862414879254353148253245)
            ·
              refine ⟨6323405579720382430594967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16862414879254353148253245 6323405579720382430594967)
              ·
                refine ⟨9485108369580573645892451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323405579720382430594967 9485108369580573645892451)
                ·
                  refine ⟨14227662554370860468838677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485108369580573645892451 14227662554370860468838677)
                  ·
                    refine ⟨666921682236134084476813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14227662554370860468838677 666921682236134084476813)
                    ·
                      rfl

theorem cell23_3896476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3896476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896476 prefixEnd_3896476 := by exact prefixLift 3896476
  have htrace : WordTrace (prefixWord ++ tailWord_3896476) baseStart_3896476 baseEnd_3896476 := by
    simpa [prefixWord, tailWord_3896476, baseEnd_3896476] using wordTrace_append hprefix tailTrace_3896476
  have hstable : (prefixWord ++ tailWord_3896476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896476).length < 2 ^ (prefixWord ++ tailWord_3896476).sum := by decide
  have hdescent : baseEnd_3896476 < baseStart_3896476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896534 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3896534 : Nat := 118140960795 + 3896534 * 2 ^ 59
def prefixEnd_3896534 : Nat := 4983230072969 + 3 ^ 40 * 3896534 * 2
def baseEnd_3896534 : Nat := 2000794828586363026505173

theorem tailTrace_3896534 : CollatzResearch.WordTrace tailWord_3896534 prefixEnd_3896534 2000794828586363026505173 := by
  unfold tailWord_3896534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882391904095641741946041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94745513643686845247424437 8882391904095641741946041)
  ·
    refine ⟨6661793928071731306459531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8882391904095641741946041 6661793928071731306459531)
    ·
      refine ⟨9992690892107596959689297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661793928071731306459531 9992690892107596959689297)
      ·
        refine ⟨7494518169080697719766973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9992690892107596959689297 7494518169080697719766973)
        ·
          refine ⟨2810444313405261644912615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7494518169080697719766973 2810444313405261644912615)
          ·
            refine ⟨4215666470107892467368923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810444313405261644912615 4215666470107892467368923)
            ·
              refine ⟨6323499705161838701053385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215666470107892467368923 6323499705161838701053385)
              ·
                refine ⟨4742624778871379025790039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323499705161838701053385 4742624778871379025790039)
                ·
                  refine ⟨7113937168307068538685059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4742624778871379025790039 7113937168307068538685059)
                  ·
                    refine ⟨10670905752460602808027589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7113937168307068538685059 10670905752460602808027589)
                    ·
                      refine ⟨2000794828586363026505173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10670905752460602808027589 2000794828586363026505173)
                      ·
                        rfl

theorem cell23_3896534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3896534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896534 prefixEnd_3896534 := by exact prefixLift 3896534
  have htrace : WordTrace (prefixWord ++ tailWord_3896534) baseStart_3896534 baseEnd_3896534 := by
    simpa [prefixWord, tailWord_3896534, baseEnd_3896534] using wordTrace_append hprefix tailTrace_3896534
  have hstable : (prefixWord ++ tailWord_3896534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896534).length < 2 ^ (prefixWord ++ tailWord_3896534).sum := by decide
  have hdescent : baseEnd_3896534 < baseStart_3896534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896566 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3896566 : Nat := 118140960795 + 3896566 * 2 ^ 59
def prefixEnd_3896566 : Nat := 4983230072969 + 3 ^ 40 * 3896566 * 2
def baseEnd_3896566 : Nat := 666937086655768967101675

theorem tailTrace_3896566 : CollatzResearch.WordTrace tailWord_3896566 prefixEnd_3896566 666937086655768967101675 := by
  unfold tailWord_3896566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882464850088396083518847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94746291734276224890867701 8882464850088396083518847)
  ·
    refine ⟨13323697275132594125278271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8882464850088396083518847 13323697275132594125278271)
    ·
      refine ⟨19985545912698891187917407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13323697275132594125278271 19985545912698891187917407)
      ·
        refine ⟨29978318869048336781876111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19985545912698891187917407 29978318869048336781876111)
        ·
          refine ⟨44967478303572505172814167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29978318869048336781876111 44967478303572505172814167)
          ·
            refine ⟨67451217455358757759221251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44967478303572505172814167 67451217455358757759221251)
            ·
              refine ⟨101176826183038136638831877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67451217455358757759221251 101176826183038136638831877)
              ·
                refine ⟨18970654909319650619780977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101176826183038136638831877 18970654909319650619780977)
                ·
                  refine ⟨14227991181989737964835733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18970654909319650619780977 14227991181989737964835733)
                  ·
                    refine ⟨666937086655768967101675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14227991181989737964835733 666937086655768967101675)
                    ·
                      rfl

theorem cell23_3896566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3896566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896566 prefixEnd_3896566 := by exact prefixLift 3896566
  have htrace : WordTrace (prefixWord ++ tailWord_3896566) baseStart_3896566 baseEnd_3896566 := by
    simpa [prefixWord, tailWord_3896566, baseEnd_3896566] using wordTrace_append hprefix tailTrace_3896566
  have hstable : (prefixWord ++ tailWord_3896566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896566).length < 2 ^ (prefixWord ++ tailWord_3896566).sum := by decide
  have hdescent : baseEnd_3896566 < baseStart_3896566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896590 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3896590 : Nat := 118140960795 + 3896590 * 2 ^ 59
def prefixEnd_3896590 : Nat := 4983230072969 + 3 ^ 40 * 3896590 * 2
def baseEnd_3896590 : Nat := 2000823583503014807404915

theorem tailTrace_3896590 : CollatzResearch.WordTrace tailWord_3896590 prefixEnd_3896590 2000823583503014807404915 := by
  unfold tailWord_3896590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17765039119165923679396903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94746875302218259623450149 17765039119165923679396903)
  ·
    refine ⟨26647558678748885519095355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17765039119165923679396903 26647558678748885519095355)
    ·
      refine ⟨39971338018123328278643033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26647558678748885519095355 39971338018123328278643033)
      ·
        refine ⟨29978503513592496208982275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39971338018123328278643033 29978503513592496208982275)
        ·
          refine ⟨44967755270388744313473413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29978503513592496208982275 44967755270388744313473413)
          ·
            refine ⟨8431454113197889558776265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44967755270388744313473413 8431454113197889558776265)
            ·
              refine ⟨6323590584898417169082199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8431454113197889558776265 6323590584898417169082199)
              ·
                refine ⟨9485385877347625753623299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6323590584898417169082199 9485385877347625753623299)
                ·
                  refine ⟨14228078816021438630434949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485385877347625753623299 14228078816021438630434949)
                  ·
                    refine ⟨2667764778004019743206553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14228078816021438630434949 2667764778004019743206553)
                    ·
                      refine ⟨2000823583503014807404915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2667764778004019743206553 2000823583503014807404915)
                      ·
                        rfl

theorem cell23_3896590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3896590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896590 prefixEnd_3896590 := by exact prefixLift 3896590
  have htrace : WordTrace (prefixWord ++ tailWord_3896590) baseStart_3896590 baseEnd_3896590 := by
    simpa [prefixWord, tailWord_3896590, baseEnd_3896590] using wordTrace_append hprefix tailTrace_3896590
  have hstable : (prefixWord ++ tailWord_3896590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896590).length < 2 ^ (prefixWord ++ tailWord_3896590).sum := by decide
  have hdescent : baseEnd_3896590 < baseStart_3896590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896613 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 5]
def baseStart_3896613 : Nat := 118140960795 + 3896613 * 2 ^ 59
def prefixEnd_3896613 : Nat := 4983230072969 + 3 ^ 40 * 3896613 * 2
def baseEnd_3896613 : Nat := 222315043728674246379701

theorem tailTrace_3896613 : CollatzResearch.WordTrace tailWord_3896613 prefixEnd_3896613 222315043728674246379701 := by
  unfold tailWord_3896613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142121151832244064363262493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94747434554829376242174995 142121151832244064363262493)
  ·
    refine ⟨53295431937091524136223435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142121151832244064363262493 53295431937091524136223435)
    ·
      refine ⟨79943147905637286204335153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53295431937091524136223435 79943147905637286204335153)
      ·
        refine ⟨59957360929227964653251365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79943147905637286204335153 59957360929227964653251365)
        ·
          refine ⟨11242005174230243372484631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59957360929227964653251365 11242005174230243372484631)
          ·
            refine ⟨16863007761345365058726947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11242005174230243372484631 16863007761345365058726947)
            ·
              refine ⟨25294511642018047588090421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16863007761345365058726947 25294511642018047588090421)
              ·
                refine ⟨2371360466439191961383477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25294511642018047588090421 2371360466439191961383477)
                ·
                  refine ⟨222315043728674246379701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2371360466439191961383477 222315043728674246379701)
                  ·
                    rfl

theorem cell23_3896613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_3896613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896613 prefixEnd_3896613 := by exact prefixLift 3896613
  have htrace : WordTrace (prefixWord ++ tailWord_3896613) baseStart_3896613 baseEnd_3896613 := by
    simpa [prefixWord, tailWord_3896613, baseEnd_3896613] using wordTrace_append hprefix tailTrace_3896613
  have hstable : (prefixWord ++ tailWord_3896613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896613).length < 2 ^ (prefixWord ++ tailWord_3896613).sum := by decide
  have hdescent : baseEnd_3896613 < baseStart_3896613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896619 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_3896619 : Nat := 118140960795 + 3896619 * 2 ^ 59
def prefixEnd_3896619 : Nat := 4983230072969 + 3 ^ 40 * 3896619 * 2
def baseEnd_3896619 : Nat := 2000838474441995193942281

theorem tailTrace_3896619 : CollatzResearch.WordTrace tailWord_3896619 prefixEnd_3896619 2000838474441995193942281 := by
  unfold tailWord_3896619
  simp only [CollatzResearch.WordTrace]
  refine ⟨142121370670222327387980911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94747580446814884925320607 142121370670222327387980911)
  ·
    refine ⟨213182056005333491081971367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142121370670222327387980911 213182056005333491081971367)
    ·
      refine ⟨319773084008000236622957051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213182056005333491081971367 319773084008000236622957051)
      ·
        refine ⟨479659626012000354934435577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319773084008000236622957051 479659626012000354934435577)
        ·
          refine ⟨359744719509000266200826683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479659626012000354934435577 359744719509000266200826683)
          ·
            refine ⟨539617079263500399301240025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359744719509000266200826683 539617079263500399301240025)
            ·
              refine ⟨404712809447625299475930019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539617079263500399301240025 404712809447625299475930019)
              ·
                refine ⟨607069214171437949213895029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404712809447625299475930019 607069214171437949213895029)
                ·
                  refine ⟨56912738828572307738802659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 607069214171437949213895029 56912738828572307738802659)
                  ·
                    refine ⟨85369108242858461608203989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56912738828572307738802659 85369108242858461608203989)
                    ·
                      refine ⟨2000838474441995193942281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85369108242858461608203989 2000838474441995193942281)
                      ·
                        rfl

theorem cell23_3896619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_3896619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896619 prefixEnd_3896619 := by exact prefixLift 3896619
  have htrace : WordTrace (prefixWord ++ tailWord_3896619) baseStart_3896619 baseEnd_3896619 := by
    simpa [prefixWord, tailWord_3896619, baseEnd_3896619] using wordTrace_append hprefix tailTrace_3896619
  have hstable : (prefixWord ++ tailWord_3896619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896619).length < 2 ^ (prefixWord ++ tailWord_3896619).sum := by decide
  have hdescent : baseEnd_3896619 < baseStart_3896619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896680 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3896680 : Nat := 118140960795 + 3896680 * 2 ^ 59
def prefixEnd_3896680 : Nat := 4983230072969 + 3 ^ 40 * 3896680 * 2
def baseEnd_3896680 : Nat := 2000869796761919455279501

theorem tailTrace_3896680 : CollatzResearch.WordTrace tailWord_3896680 prefixEnd_3896680 2000869796761919455279501 := by
  unfold tailWord_3896680
  simp only [CollatzResearch.WordTrace]
  refine ⟨71061797761500667402975747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94749063682000889870634329 71061797761500667402975747)
  ·
    refine ⟨106592696642251001104463621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71061797761500667402975747 106592696642251001104463621)
    ·
      refine ⟨19986130620422062707086929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106592696642251001104463621 19986130620422062707086929)
      ·
        refine ⟨14989597965316547030315197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19986130620422062707086929 14989597965316547030315197)
        ·
          refine ⟨5621099236993705136368199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14989597965316547030315197 5621099236993705136368199)
          ·
            refine ⟨8431648855490557704552299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621099236993705136368199 8431648855490557704552299)
            ·
              refine ⟨12647473283235836556828449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8431648855490557704552299 12647473283235836556828449)
              ·
                refine ⟨9485604962426877417621337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12647473283235836556828449 9485604962426877417621337)
                ·
                  refine ⟨7114203721820158063216003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9485604962426877417621337 7114203721820158063216003)
                  ·
                    refine ⟨10671305582730237094824005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114203721820158063216003 10671305582730237094824005)
                    ·
                      refine ⟨2000869796761919455279501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10671305582730237094824005 2000869796761919455279501)
                      ·
                        rfl

theorem cell23_3896680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3896680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896680 prefixEnd_3896680 := by exact prefixLift 3896680
  have htrace : WordTrace (prefixWord ++ tailWord_3896680) baseStart_3896680 baseEnd_3896680 := by
    simpa [prefixWord, tailWord_3896680, baseEnd_3896680] using wordTrace_append hprefix tailTrace_3896680
  have hstable : (prefixWord ++ tailWord_3896680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896680).length < 2 ^ (prefixWord ++ tailWord_3896680).sum := by decide
  have hdescent : baseEnd_3896680 < baseStart_3896680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896753 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3896753 : Nat := 118140960795 + 3896753 * 2 ^ 59
def prefixEnd_3896753 : Nat := 4983230072969 + 3 ^ 40 * 3896753 * 2
def baseEnd_3896753 : Nat := 2000907280849697669666665

theorem tailTrace_3896753 : CollatzResearch.WordTrace tailWord_3896753 prefixEnd_3896753 2000907280849697669666665 := by
  unfold tailWord_3896753
  simp only [CollatzResearch.WordTrace]
  refine ⟨142126258051736868273358913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94750838701157912182239275 142126258051736868273358913)
  ·
    refine ⟨106594693538802651205019185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142126258051736868273358913 106594693538802651205019185)
    ·
      refine ⟨79946020154101988403764389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106594693538802651205019185 79946020154101988403764389)
      ·
        refine ⟨14989878778894122825705823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79946020154101988403764389 14989878778894122825705823)
        ·
          refine ⟨22484818168341184238558735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14989878778894122825705823 22484818168341184238558735)
          ·
            refine ⟨33727227252511776357838103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484818168341184238558735 33727227252511776357838103)
            ·
              refine ⟨50590840878767664536757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33727227252511776357838103 50590840878767664536757155)
              ·
                refine ⟨75886261318151496805135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50590840878767664536757155 75886261318151496805135733)
                ·
                  refine ⟨7114336998576702825481475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75886261318151496805135733 7114336998576702825481475)
                  ·
                    refine ⟨10671505497865054238222213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7114336998576702825481475 10671505497865054238222213)
                    ·
                      refine ⟨2000907280849697669666665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10671505497865054238222213 2000907280849697669666665)
                      ·
                        rfl

theorem cell23_3896753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3896753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896753 prefixEnd_3896753 := by exact prefixLift 3896753
  have htrace : WordTrace (prefixWord ++ tailWord_3896753) baseStart_3896753 baseEnd_3896753 := by
    simpa [prefixWord, tailWord_3896753, baseEnd_3896753] using wordTrace_append hprefix tailTrace_3896753
  have hstable : (prefixWord ++ tailWord_3896753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896753).length < 2 ^ (prefixWord ++ tailWord_3896753).sum := by decide
  have hdescent : baseEnd_3896753 < baseStart_3896753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896783 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_3896783 : Nat := 118140960795 + 3896783 * 2 ^ 59
def prefixEnd_3896783 : Nat := 4983230072969 + 3 ^ 40 * 3896783 * 2
def baseEnd_3896783 : Nat := 2000922685269332552291527

theorem tailTrace_3896783 : CollatzResearch.WordTrace tailWord_3896783 prefixEnd_3896783 2000922685269332552291527 := by
  unfold tailWord_3896783
  simp only [CollatzResearch.WordTrace]
  refine ⟨142127352241628183396951003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94751568161085455597967335 142127352241628183396951003)
  ·
    refine ⟨213191028362442275095426505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142127352241628183396951003 213191028362442275095426505)
    ·
      refine ⟨159893271271831706321569879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213191028362442275095426505 159893271271831706321569879)
      ·
        refine ⟨239839906907747559482354819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159893271271831706321569879 239839906907747559482354819)
        ·
          refine ⟨359759860361621339223532229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239839906907747559482354819 359759860361621339223532229)
          ·
            refine ⟨67454973817804001104412293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359759860361621339223532229 67454973817804001104412293)
            ·
              refine ⟨12647807590838250207077305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67454973817804001104412293 12647807590838250207077305)
              ·
                refine ⟨9485855693128687655307979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12647807590838250207077305 9485855693128687655307979)
                ·
                  refine ⟨14228783539693031482961969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9485855693128687655307979 14228783539693031482961969)
                  ·
                    refine ⟨10671587654769773612221477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14228783539693031482961969 10671587654769773612221477)
                    ·
                      refine ⟨2000922685269332552291527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10671587654769773612221477 2000922685269332552291527)
                      ·
                        rfl

theorem cell23_3896783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_3896783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896783 prefixEnd_3896783 := by exact prefixLift 3896783
  have htrace : WordTrace (prefixWord ++ tailWord_3896783) baseStart_3896783 baseEnd_3896783 := by
    simpa [prefixWord, tailWord_3896783, baseEnd_3896783] using wordTrace_append hprefix tailTrace_3896783
  have hstable : (prefixWord ++ tailWord_3896783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896783).length < 2 ^ (prefixWord ++ tailWord_3896783).sum := by decide
  have hdescent : baseEnd_3896783 < baseStart_3896783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896797 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3896797 : Nat := 118140960795 + 3896797 * 2 ^ 59
def prefixEnd_3896797 : Nat := 4983230072969 + 3 ^ 40 * 3896797 * 2
def baseEnd_3896797 : Nat := 666976624666165165838821

theorem tailTrace_3896797 : CollatzResearch.WordTrace tailWord_3896797 prefixEnd_3896797 666976624666165165838821 := by
  unfold tailWord_3896797
  simp only [CollatzResearch.WordTrace]
  refine ⟨142127862863577463787960645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94751908575718309191973763 142127862863577463787960645)
  ·
    refine ⟨26648974286920774460242621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142127862863577463787960645 26648974286920774460242621)
    ·
      refine ⟨9993365357595290422590983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26648974286920774460242621 9993365357595290422590983)
      ·
        refine ⟨14990048036392935633886475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9993365357595290422590983 14990048036392935633886475)
        ·
          refine ⟨22485072054589403450829713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14990048036392935633886475 22485072054589403450829713)
          ·
            refine ⟨16863804040942052588122285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22485072054589403450829713 16863804040942052588122285)
            ·
              refine ⟨6323926515353269720545857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16863804040942052588122285 6323926515353269720545857)
              ·
                refine ⟨4742944886514952290409393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6323926515353269720545857 4742944886514952290409393)
                ·
                  refine ⟨3557208664886214217807045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4742944886514952290409393 3557208664886214217807045)
                  ·
                    refine ⟨666976624666165165838821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557208664886214217807045 666976624666165165838821)
                    ·
                      rfl

theorem cell23_3896797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3896797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896797 prefixEnd_3896797 := by exact prefixLift 3896797
  have htrace : WordTrace (prefixWord ++ tailWord_3896797) baseStart_3896797 baseEnd_3896797 := by
    simpa [prefixWord, tailWord_3896797, baseEnd_3896797] using wordTrace_append hprefix tailTrace_3896797
  have hstable : (prefixWord ++ tailWord_3896797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896797).length < 2 ^ (prefixWord ++ tailWord_3896797).sum := by decide
  have hdescent : baseEnd_3896797 < baseStart_3896797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896910 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3896910 : Nat := 118140960795 + 3896910 * 2 ^ 59
def prefixEnd_3896910 : Nat := 4983230072969 + 3 ^ 40 * 3896910 * 2
def baseEnd_3896910 : Nat := 2000987897312453555403443

theorem tailTrace_3896910 : CollatzResearch.WordTrace tailWord_3896910 prefixEnd_3896910 2000987897312453555403443 := by
  unfold tailWord_3896910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17766498039021010510853023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94754656208112056057882789 17766498039021010510853023)
  ·
    refine ⟨26649747058531515766279535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17766498039021010510853023 26649747058531515766279535)
    ·
      refine ⟨39974620587797273649419303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26649747058531515766279535 39974620587797273649419303)
      ·
        refine ⟨59961930881695910474128955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39974620587797273649419303 59961930881695910474128955)
        ·
          refine ⟨89942896322543865711193433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59961930881695910474128955 89942896322543865711193433)
          ·
            refine ⟨67457172241907899283395075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89942896322543865711193433 67457172241907899283395075)
            ·
              refine ⟨101185758362861848925092613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67457172241907899283395075 101185758362861848925092613)
              ·
                refine ⟨18972329693036596673454865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101185758362861848925092613 18972329693036596673454865)
                ·
                  refine ⟨14229247269777447505091149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18972329693036596673454865 14229247269777447505091149)
                  ·
                    refine ⟨5335967726166542814409181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14229247269777447505091149 5335967726166542814409181)
                    ·
                      refine ⟨2000987897312453555403443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5335967726166542814409181 2000987897312453555403443)
                      ·
                        rfl

theorem cell23_3896910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3896910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896910 prefixEnd_3896910 := by exact prefixLift 3896910
  have htrace : WordTrace (prefixWord ++ tailWord_3896910) baseStart_3896910 baseEnd_3896910 := by
    simpa [prefixWord, tailWord_3896910, baseEnd_3896910] using wordTrace_append hprefix tailTrace_3896910
  have hstable : (prefixWord ++ tailWord_3896910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896910).length < 2 ^ (prefixWord ++ tailWord_3896910).sum := by decide
  have hdescent : baseEnd_3896910 < baseStart_3896910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896960 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_3896960 : Nat := 118140960795 + 3896960 * 2 ^ 59
def prefixEnd_3896960 : Nat := 4983230072969 + 3 ^ 40 * 3896960 * 2
def baseEnd_3896960 : Nat := 667004523781726119926071

theorem tailTrace_3896960 : CollatzResearch.WordTrace tailWord_3896960 prefixEnd_3896960 667004523781726119926071 := by
  unfold tailWord_3896960
  simp only [CollatzResearch.WordTrace]
  refine ⟨71066903980993471313072167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94755871974657961750762889 71066903980993471313072167)
  ·
    refine ⟨106600355971490206969608251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71066903980993471313072167 106600355971490206969608251)
    ·
      refine ⟨159900533957235310454412377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106600355971490206969608251 159900533957235310454412377)
      ·
        refine ⟨119925400467926482840809283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159900533957235310454412377 119925400467926482840809283)
        ·
          refine ⟨179888100701889724261213925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119925400467926482840809283 179888100701889724261213925)
          ·
            refine ⟨33729018881604323298977611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179888100701889724261213925 33729018881604323298977611)
            ·
              refine ⟨50593528322406484948466417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33729018881604323298977611 50593528322406484948466417)
              ·
                refine ⟨37945146241804863711349813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50593528322406484948466417 37945146241804863711349813)
                ·
                  refine ⟨3557357460169205972939045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37945146241804863711349813 3557357460169205972939045)
                  ·
                    refine ⟨667004523781726119926071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557357460169205972939045 667004523781726119926071)
                    ·
                      rfl

theorem cell23_3896960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_3896960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896960 prefixEnd_3896960 := by exact prefixLift 3896960
  have htrace : WordTrace (prefixWord ++ tailWord_3896960) baseStart_3896960 baseEnd_3896960 := by
    simpa [prefixWord, tailWord_3896960, baseEnd_3896960] using wordTrace_append hprefix tailTrace_3896960
  have hstable : (prefixWord ++ tailWord_3896960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896960).length < 2 ^ (prefixWord ++ tailWord_3896960).sum := by decide
  have hdescent : baseEnd_3896960 < baseStart_3896960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3896967 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_3896967 : Nat := 118140960795 + 3896967 * 2 ^ 59
def prefixEnd_3896967 : Nat := 4983230072969 + 3 ^ 40 * 3896967 * 2
def baseEnd_3896967 : Nat := 2001017165709759832390681

theorem tailTrace_3896967 : CollatzResearch.WordTrace tailWord_3896967 prefixEnd_3896967 2001017165709759832390681 := by
  unfold tailWord_3896967
  simp only [CollatzResearch.WordTrace]
  refine ⟨142134063272961582821649155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94756042181974388547766103 142134063272961582821649155)
  ·
    refine ⟨213201094909442374232473733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142134063272961582821649155 213201094909442374232473733)
    ·
      refine ⟨39975205295520445168588825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213201094909442374232473733 39975205295520445168588825)
      ·
        refine ⟨29981403971640333876441619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39975205295520445168588825 29981403971640333876441619)
        ·
          refine ⟨44972105957460500814662429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29981403971640333876441619 44972105957460500814662429)
          ·
            refine ⟨16864539734047687805498411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44972105957460500814662429 16864539734047687805498411)
            ·
              refine ⟨25296809601071531708247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16864539734047687805498411 25296809601071531708247617)
              ·
                refine ⟨18972607200803648781185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25296809601071531708247617 18972607200803648781185713)
                ·
                  refine ⟨14229455400602736585889285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18972607200803648781185713 14229455400602736585889285)
                  ·
                    refine ⟨2668022887613013109854241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14229455400602736585889285 2668022887613013109854241)
                    ·
                      refine ⟨2001017165709759832390681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668022887613013109854241 2001017165709759832390681)
                      ·
                        rfl

theorem cell23_3896967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_3896967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3896967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3896967 prefixEnd_3896967 := by exact prefixLift 3896967
  have htrace : WordTrace (prefixWord ++ tailWord_3896967) baseStart_3896967 baseEnd_3896967 := by
    simpa [prefixWord, tailWord_3896967, baseEnd_3896967] using wordTrace_append hprefix tailTrace_3896967
  have hstable : (prefixWord ++ tailWord_3896967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3896967).length < 2 ^ (prefixWord ++ tailWord_3896967).sum := by decide
  have hdescent : baseEnd_3896967 < baseStart_3896967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3896967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897017 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3897017 : Nat := 118140960795 + 3897017 * 2 ^ 59
def prefixEnd_3897017 : Nat := 4983230072969 + 3 ^ 40 * 3897017 * 2
def baseEnd_3897017 : Nat := 2001042839742484636765451

theorem tailTrace_3897017 : CollatzResearch.WordTrace tailWord_3897017 prefixEnd_3897017 2001042839742484636765451 := by
  unfold tailWord_3897017
  simp only [CollatzResearch.WordTrace]
  refine ⟨142135886922780441360969305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94757257948520294240646203 142135886922780441360969305)
  ·
    refine ⟨106601915192085331020726979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142135886922780441360969305 106601915192085331020726979)
    ·
      refine ⟨159902872788127996531090469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106601915192085331020726979 159902872788127996531090469)
      ·
        refine ⟨29981788647773999349579463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159902872788127996531090469 29981788647773999349579463)
        ·
          refine ⟨44972682971660999024369195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29981788647773999349579463 44972682971660999024369195)
          ·
            refine ⟨67459024457491498536553793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44972682971660999024369195 67459024457491498536553793)
            ·
              refine ⟨50594268343118623902415345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67459024457491498536553793 50594268343118623902415345)
              ·
                refine ⟨37945701257338967926811509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50594268343118623902415345 37945701257338967926811509)
                ·
                  refine ⟨3557409492875528243138579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37945701257338967926811509 3557409492875528243138579)
                  ·
                    refine ⟨5336114239313292364707869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557409492875528243138579 5336114239313292364707869)
                    ·
                      refine ⟨2001042839742484636765451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336114239313292364707869 2001042839742484636765451)
                      ·
                        rfl

theorem cell23_3897017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3897017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897017 prefixEnd_3897017 := by exact prefixLift 3897017
  have htrace : WordTrace (prefixWord ++ tailWord_3897017) baseStart_3897017 baseEnd_3897017 := by
    simpa [prefixWord, tailWord_3897017, baseEnd_3897017] using wordTrace_append hprefix tailTrace_3897017
  have hstable : (prefixWord ++ tailWord_3897017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897017).length < 2 ^ (prefixWord ++ tailWord_3897017).sum := by decide
  have hdescent : baseEnd_3897017 < baseStart_3897017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897084 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 2, 4]
def baseStart_3897084 : Nat := 118140960795 + 3897084 * 2 ^ 59
def prefixEnd_3897084 : Nat := 4983230072969 + 3 ^ 40 * 3897084 * 2
def baseEnd_3897084 : Nat := 667025747648778624875881

theorem tailTrace_3897084 : CollatzResearch.WordTrace tailWord_3897084 prefixEnd_3897084 667025747648778624875881 := by
  unfold tailWord_3897084
  simp only [CollatzResearch.WordTrace]
  refine ⟨71069165306768855901829153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94758887075691807869105537 71069165306768855901829153)
  ·
    refine ⟨53301873980076641926371865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71069165306768855901829153 53301873980076641926371865)
    ·
      refine ⟨39976405485057481444778899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53301873980076641926371865 39976405485057481444778899)
      ·
        refine ⟨59964608227586222167168349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39976405485057481444778899 59964608227586222167168349)
        ·
          refine ⟨22486728085344833312688131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59964608227586222167168349 22486728085344833312688131)
          ·
            refine ⟨33730092128017249969032197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22486728085344833312688131 33730092128017249969032197)
            ·
              refine ⟨6324392274003234369193537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33730092128017249969032197 6324392274003234369193537)
              ·
                refine ⟨4743294205502425776895153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6324392274003234369193537 4743294205502425776895153)
                ·
                  refine ⟨3557470654126819332671365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4743294205502425776895153 3557470654126819332671365)
                  ·
                    refine ⟨667025747648778624875881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3557470654126819332671365 667025747648778624875881)
                    ·
                      rfl

theorem cell23_3897084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_3897084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897084 prefixEnd_3897084 := by exact prefixLift 3897084
  have htrace : WordTrace (prefixWord ++ tailWord_3897084) baseStart_3897084 baseEnd_3897084 := by
    simpa [prefixWord, tailWord_3897084, baseEnd_3897084] using wordTrace_append hprefix tailTrace_3897084
  have hstable : (prefixWord ++ tailWord_3897084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897084).length < 2 ^ (prefixWord ++ tailWord_3897084).sum := by decide
  have hdescent : baseEnd_3897084 < baseStart_3897084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897100 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3897100 : Nat := 118140960795 + 3897100 * 2 ^ 59
def prefixEnd_3897100 : Nat := 4983230072969 + 3 ^ 40 * 3897100 * 2
def baseEnd_3897100 : Nat := 2001085458636807812027569

theorem tailTrace_3897100 : CollatzResearch.WordTrace tailWord_3897100 prefixEnd_3897100 2001085458636807812027569 := by
  unfold tailWord_3897100
  simp only [CollatzResearch.WordTrace]
  refine ⟨71069457090739873268120377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94759276120986497690827169 71069457090739873268120377)
  ·
    refine ⟨53302092818054904951090283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71069457090739873268120377 53302092818054904951090283)
    ·
      refine ⟨79953139227082357426635425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53302092818054904951090283 79953139227082357426635425)
      ·
        refine ⟨59964854420311768069976569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79953139227082357426635425 59964854420311768069976569)
        ·
          refine ⟨44973640815233826052482427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59964854420311768069976569 44973640815233826052482427)
          ·
            refine ⟨67460461222850739078723641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44973640815233826052482427 67460461222850739078723641)
            ·
              refine ⟨50595345917138054309042731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67460461222850739078723641 50595345917138054309042731)
              ·
                refine ⟨75893018875707081463564097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50595345917138054309042731 75893018875707081463564097)
                ·
                  refine ⟨56919764156780311097673073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75893018875707081463564097 56919764156780311097673073)
                  ·
                    refine ⟨42689823117585233323254805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56919764156780311097673073 42689823117585233323254805)
                    ·
                      refine ⟨2001085458636807812027569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42689823117585233323254805 2001085458636807812027569)
                      ·
                        rfl

theorem cell23_3897100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3897100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897100 prefixEnd_3897100 := by exact prefixLift 3897100
  have htrace : WordTrace (prefixWord ++ tailWord_3897100) baseStart_3897100 baseEnd_3897100 := by
    simpa [prefixWord, tailWord_3897100, baseEnd_3897100] using wordTrace_append hprefix tailTrace_3897100
  have hstable : (prefixWord ++ tailWord_3897100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897100).length < 2 ^ (prefixWord ++ tailWord_3897100).sum := by decide
  have hdescent : baseEnd_3897100 < baseStart_3897100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897124 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3897124 : Nat := 118140960795 + 3897124 * 2 ^ 59
def prefixEnd_3897124 : Nat := 4983230072969 + 3 ^ 40 * 3897124 * 2
def baseEnd_3897124 : Nat := 2001097782172515718127459

theorem tailTrace_3897124 : CollatzResearch.WordTrace tailWord_3897124 prefixEnd_3897124 2001097782172515718127459 := by
  unfold tailWord_3897124
  simp only [CollatzResearch.WordTrace]
  refine ⟨71069894766696399317557213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94759859688928532423409617 71069894766696399317557213)
  ·
    refine ⟨26651210537511149744083955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71069894766696399317557213 26651210537511149744083955)
    ·
      refine ⟨39976815806266724616125933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26651210537511149744083955 39976815806266724616125933)
      ·
        refine ⟨14991305927350021731047225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39976815806266724616125933 14991305927350021731047225)
        ·
          refine ⟨11243479445512516298285419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991305927350021731047225 11243479445512516298285419)
          ·
            refine ⟨16865219168268774447428129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243479445512516298285419 16865219168268774447428129)
            ·
              refine ⟨12648914376201580835571097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16865219168268774447428129 12648914376201580835571097)
              ·
                refine ⟨9486685782151185626678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12648914376201580835571097 9486685782151185626678323)
                ·
                  refine ⟨14230028673226778440017485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486685782151185626678323 14230028673226778440017485)
                  ·
                    refine ⟨5336260752460041915006557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14230028673226778440017485 5336260752460041915006557)
                    ·
                      refine ⟨2001097782172515718127459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336260752460041915006557 2001097782172515718127459)
                      ·
                        rfl

theorem cell23_3897124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3897124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897124 prefixEnd_3897124 := by exact prefixLift 3897124
  have htrace : WordTrace (prefixWord ++ tailWord_3897124) baseStart_3897124 baseEnd_3897124 := by
    simpa [prefixWord, tailWord_3897124, baseEnd_3897124] using wordTrace_append hprefix tailTrace_3897124
  have hstable : (prefixWord ++ tailWord_3897124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897124).length < 2 ^ (prefixWord ++ tailWord_3897124).sum := by decide
  have hdescent : baseEnd_3897124 < baseStart_3897124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897128 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3897128 : Nat := 118140960795 + 3897128 * 2 ^ 59
def prefixEnd_3897128 : Nat := 4983230072969 + 3 ^ 40 * 3897128 * 2
def baseEnd_3897128 : Nat := 2001099836095133702477441

theorem tailTrace_3897128 : CollatzResearch.WordTrace tailWord_3897128 prefixEnd_3897128 2001099836095133702477441 := by
  unfold tailWord_3897128
  simp only [CollatzResearch.WordTrace]
  refine ⟨71069967712689153659130019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94759956950252204878840025 71069967712689153659130019)
  ·
    refine ⟨106604951569033730488695029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71069967712689153659130019 106604951569033730488695029)
    ·
      refine ⟨9994214209596912233315159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106604951569033730488695029 9994214209596912233315159)
      ·
        refine ⟨14991321314395368349972739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994214209596912233315159 14991321314395368349972739)
        ·
          refine ⟨22486981971593052524959109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14991321314395368349972739 22486981971593052524959109)
          ·
            refine ⟨4216309119673697348429833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22486981971593052524959109 4216309119673697348429833)
            ·
              refine ⟨3162231839755273011322375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216309119673697348429833 3162231839755273011322375)
              ·
                refine ⟨4743347759632909516983563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162231839755273011322375 4743347759632909516983563)
                ·
                  refine ⟨7115021639449364275475345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743347759632909516983563 7115021639449364275475345)
                  ·
                    refine ⟨5336266229587023206606509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7115021639449364275475345 5336266229587023206606509)
                    ·
                      refine ⟨2001099836095133702477441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336266229587023206606509 2001099836095133702477441)
                      ·
                        rfl

theorem cell23_3897128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3897128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897128 prefixEnd_3897128 := by exact prefixLift 3897128
  have htrace : WordTrace (prefixWord ++ tailWord_3897128) baseStart_3897128 baseEnd_3897128 := by
    simpa [prefixWord, tailWord_3897128, baseEnd_3897128] using wordTrace_append hprefix tailTrace_3897128
  have hstable : (prefixWord ++ tailWord_3897128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897128).length < 2 ^ (prefixWord ++ tailWord_3897128).sum := by decide
  have hdescent : baseEnd_3897128 < baseStart_3897128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897141 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3897141 : Nat := 118140960795 + 3897141 * 2 ^ 59
def prefixEnd_3897141 : Nat := 4983230072969 + 3 ^ 40 * 3897141 * 2
def baseEnd_3897141 : Nat := 2001106511343642151614881

theorem tailTrace_3897141 : CollatzResearch.WordTrace tailWord_3897141 prefixEnd_3897141 2001106511343642151614881 := by
  unfold tailWord_3897141
  simp only [CollatzResearch.WordTrace]
  refine ⟨142140409574331210538483277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94760273049554140358988851 142140409574331210538483277)
  ·
    refine ⟨53302653590374203951931229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142140409574331210538483277 53302653590374203951931229)
    ·
      refine ⟨19988495096390326481974211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53302653590374203951931229 19988495096390326481974211)
      ·
        refine ⟨29982742644585489722961317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19988495096390326481974211 29982742644585489722961317)
        ·
          refine ⟨5621764245859779323055247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29982742644585489722961317 5621764245859779323055247)
          ·
            refine ⟨8432646368789668984582871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621764245859779323055247 8432646368789668984582871)
            ·
              refine ⟨12648969553184503476874307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8432646368789668984582871 12648969553184503476874307)
              ·
                refine ⟨18973454329776755215311461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12648969553184503476874307 18973454329776755215311461)
                ·
                  refine ⟨3557522686833141602870899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18973454329776755215311461 3557522686833141602870899)
                  ·
                    refine ⟨5336284030249712404306349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557522686833141602870899 5336284030249712404306349)
                    ·
                      refine ⟨2001106511343642151614881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336284030249712404306349 2001106511343642151614881)
                      ·
                        rfl

theorem cell23_3897141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3897141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897141 prefixEnd_3897141 := by exact prefixLift 3897141
  have htrace : WordTrace (prefixWord ++ tailWord_3897141) baseStart_3897141 baseEnd_3897141 := by
    simpa [prefixWord, tailWord_3897141, baseEnd_3897141] using wordTrace_append hprefix tailTrace_3897141
  have hstable : (prefixWord ++ tailWord_3897141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897141).length < 2 ^ (prefixWord ++ tailWord_3897141).sum := by decide
  have hdescent : baseEnd_3897141 < baseStart_3897141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897158 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3897158 : Nat := 118140960795 + 3897158 * 2 ^ 59
def prefixEnd_3897158 : Nat := 4983230072969 + 3 ^ 40 * 3897158 * 2
def baseEnd_3897158 : Nat := 2001115240514768585102303

theorem tailTrace_3897158 : CollatzResearch.WordTrace tailWord_3897158 prefixEnd_3897158 2001115240514768585102303 := by
  unfold tailWord_3897158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441907175477175701307879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94760686410179748294568085 4441907175477175701307879)
  ·
    refine ⟨6662860763215763551961819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4441907175477175701307879 6662860763215763551961819)
    ·
      refine ⟨9994291144823645327942729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6662860763215763551961819 9994291144823645327942729)
      ·
        refine ⟨7495718358617733995957047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9994291144823645327942729 7495718358617733995957047)
        ·
          refine ⟨11243577537926600993935571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7495718358617733995957047 11243577537926600993935571)
          ·
            refine ⟨16865366306889901490903357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243577537926600993935571 16865366306889901490903357)
            ·
              refine ⟨6324512365083713059088759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16865366306889901490903357 6324512365083713059088759)
              ·
                refine ⟨9486768547625569588633139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6324512365083713059088759 9486768547625569588633139)
                ·
                  refine ⟨14230152821438354382949709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9486768547625569588633139 14230152821438354382949709)
                  ·
                    refine ⟨5336307308039382893606141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14230152821438354382949709 5336307308039382893606141)
                    ·
                      refine ⟨2001115240514768585102303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336307308039382893606141 2001115240514768585102303)
                      ·
                        rfl

theorem cell23_3897158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3897158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897158 prefixEnd_3897158 := by exact prefixLift 3897158
  have htrace : WordTrace (prefixWord ++ tailWord_3897158) baseStart_3897158 baseEnd_3897158 := by
    simpa [prefixWord, tailWord_3897158, baseEnd_3897158] using wordTrace_append hprefix tailTrace_3897158
  have hstable : (prefixWord ++ tailWord_3897158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897158).length < 2 ^ (prefixWord ++ tailWord_3897158).sum := by decide
  have hdescent : baseEnd_3897158 < baseStart_3897158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897198 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3897198 : Nat := 118140960795 + 3897198 * 2 ^ 59
def prefixEnd_3897198 : Nat := 4983230072969 + 3 ^ 40 * 3897198 * 2
def baseEnd_3897198 : Nat := 2001135779740948428602119

theorem tailTrace_3897198 : CollatzResearch.WordTrace tailWord_3897198 prefixEnd_3897198 2001135779740948428602119 := by
  unfold tailWord_3897198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767811066890588659163531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94761659023416472848872165 17767811066890588659163531)
  ·
    refine ⟨26651716600335882988745297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17767811066890588659163531 26651716600335882988745297)
    ·
      refine ⟨19988787450251912241558973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26651716600335882988745297 19988787450251912241558973)
      ·
        refine ⟨7495795293844467090584615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19988787450251912241558973 7495795293844467090584615)
        ·
          refine ⟨11243692940766700635876923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7495795293844467090584615 11243692940766700635876923)
          ·
            refine ⟨16865539411150050953815385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243692940766700635876923 16865539411150050953815385)
            ·
              refine ⟨12649154558362538215361539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16865539411150050953815385 12649154558362538215361539)
              ·
                refine ⟨18973731837543807323042309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649154558362538215361539 18973731837543807323042309)
                ·
                  refine ⟨3557574719539463873070433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18973731837543807323042309 3557574719539463873070433)
                  ·
                    refine ⟨2668181039654597904802825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3557574719539463873070433 2668181039654597904802825)
                    ·
                      refine ⟨2001135779740948428602119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668181039654597904802825 2001135779740948428602119)
                      ·
                        rfl

theorem cell23_3897198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3897198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897198 prefixEnd_3897198 := by exact prefixLift 3897198
  have htrace : WordTrace (prefixWord ++ tailWord_3897198) baseStart_3897198 baseEnd_3897198 := by
    simpa [prefixWord, tailWord_3897198, baseEnd_3897198] using wordTrace_append hprefix tailTrace_3897198
  have hstable : (prefixWord ++ tailWord_3897198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897198).length < 2 ^ (prefixWord ++ tailWord_3897198).sum := by decide
  have hdescent : baseEnd_3897198 < baseStart_3897198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897244 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3897244 : Nat := 118140960795 + 3897244 * 2 ^ 59
def prefixEnd_3897244 : Nat := 4983230072969 + 3 ^ 40 * 3897244 * 2
def baseEnd_3897244 : Nat := 2001159399851055248626907

theorem tailTrace_3897244 : CollatzResearch.WordTrace tailWord_3897244 prefixEnd_3897244 2001159399851055248626907 := by
  unfold tailWord_3897244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71072083146479029564741393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94762777528638706086321857 71072083146479029564741393)
  ·
    refine ⟨53304062359859272173556045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71072083146479029564741393 53304062359859272173556045)
    ·
      refine ⟨19989023384947227065083517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53304062359859272173556045 19989023384947227065083517)
      ·
        refine ⟨7495883769355210149406319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19989023384947227065083517 7495883769355210149406319)
        ·
          refine ⟨11243825654032815224109479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7495883769355210149406319 11243825654032815224109479)
          ·
            refine ⟨16865738481049222836164219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243825654032815224109479 16865738481049222836164219)
            ·
              refine ⟨25298607721573834254246329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16865738481049222836164219 25298607721573834254246329)
              ·
                refine ⟨18973955791180375690684747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25298607721573834254246329 18973955791180375690684747)
                ·
                  refine ⟨28460933686770563536027121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18973955791180375690684747 28460933686770563536027121)
                  ·
                    refine ⟨21345700265077922652020341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28460933686770563536027121 21345700265077922652020341)
                    ·
                      refine ⟨2001159399851055248626907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21345700265077922652020341 2001159399851055248626907)
                      ·
                        rfl

theorem cell23_3897244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3897244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897244 prefixEnd_3897244 := by exact prefixLift 3897244
  have htrace : WordTrace (prefixWord ++ tailWord_3897244) baseStart_3897244 baseEnd_3897244 := by
    simpa [prefixWord, tailWord_3897244, baseEnd_3897244] using wordTrace_append hprefix tailTrace_3897244
  have hstable : (prefixWord ++ tailWord_3897244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897244).length < 2 ^ (prefixWord ++ tailWord_3897244).sum := by decide
  have hdescent : baseEnd_3897244 < baseStart_3897244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897311 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 6]
def baseStart_3897311 : Nat := 118140960795 + 3897311 * 2 ^ 59
def prefixEnd_3897311 : Nat := 4983230072969 + 3 ^ 40 * 3897311 * 2
def baseEnd_3897311 : Nat := 222354867006100720721011

theorem tailTrace_3897311 : CollatzResearch.WordTrace tailWord_3897311 prefixEnd_3897311 222354867006100720721011 := by
  unfold tailWord_3897311
  simp only [CollatzResearch.WordTrace]
  refine ⟨142146609983715329572171787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94764406655810219714781191 142146609983715329572171787)
  ·
    refine ⟨213219914975572994358257681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142146609983715329572171787 213219914975572994358257681)
    ·
      refine ⟨159914936231679745768693261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213219914975572994358257681 159914936231679745768693261)
      ·
        refine ⟨59968101086879904663259973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159914936231679745768693261 59968101086879904663259973)
        ·
          refine ⟨11244018953789982124361245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59968101086879904663259973 11244018953789982124361245)
          ·
            refine ⟨4216507107671243296635467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11244018953789982124361245 4216507107671243296635467)
            ·
              refine ⟨6324760661506864944953201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216507107671243296635467 6324760661506864944953201)
              ·
                refine ⟨4743570496130148708714901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6324760661506864944953201 4743570496130148708714901)
                ·
                  refine ⟨222354867006100720721011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4743570496130148708714901 222354867006100720721011)
                  ·
                    rfl

theorem cell23_3897311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 6].length) (baseStart_3897311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897311 prefixEnd_3897311 := by exact prefixLift 3897311
  have htrace : WordTrace (prefixWord ++ tailWord_3897311) baseStart_3897311 baseEnd_3897311 := by
    simpa [prefixWord, tailWord_3897311, baseEnd_3897311] using wordTrace_append hprefix tailTrace_3897311
  have hstable : (prefixWord ++ tailWord_3897311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897311).length < 2 ^ (prefixWord ++ tailWord_3897311).sum := by decide
  have hdescent : baseEnd_3897311 < baseStart_3897311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897372 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3897372 : Nat := 118140960795 + 3897372 * 2 ^ 59
def prefixEnd_3897372 : Nat := 4983230072969 + 3 ^ 40 * 3897372 * 2
def baseEnd_3897372 : Nat := 2001225125374830747826319

theorem tailTrace_3897372 : CollatzResearch.WordTrace tailWord_3897372 prefixEnd_3897372 2001225125374830747826319 := by
  unfold tailWord_3897372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71074417418247168495071185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94765889890996224660094913 71074417418247168495071185)
  ·
    refine ⟨53305813063685376371303389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71074417418247168495071185 53305813063685376371303389)
    ·
      refine ⟨19989679898882016139238771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53305813063685376371303389 19989679898882016139238771)
      ·
        refine ⟨29984519848323024208858157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19989679898882016139238771 29984519848323024208858157)
        ·
          refine ⟨11244194943121134078321809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29984519848323024208858157 11244194943121134078321809)
          ·
            refine ⟨8433146207340850558741357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244194943121134078321809 8433146207340850558741357)
            ·
              refine ⟨3162429827752818959528009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8433146207340850558741357 3162429827752818959528009)
              ·
                refine ⟨2371822370814614219646007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162429827752818959528009 2371822370814614219646007)
                ·
                  refine ⟨3557733556221921329469011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371822370814614219646007 3557733556221921329469011)
                  ·
                    refine ⟨5336600334332881994203517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557733556221921329469011 5336600334332881994203517)
                    ·
                      refine ⟨2001225125374830747826319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336600334332881994203517 2001225125374830747826319)
                      ·
                        rfl

theorem cell23_3897372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3897372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897372 prefixEnd_3897372 := by exact prefixLift 3897372
  have htrace : WordTrace (prefixWord ++ tailWord_3897372) baseStart_3897372 baseEnd_3897372 := by
    simpa [prefixWord, tailWord_3897372, baseEnd_3897372] using wordTrace_append hprefix tailTrace_3897372
  have hstable : (prefixWord ++ tailWord_3897372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897372).length < 2 ^ (prefixWord ++ tailWord_3897372).sum := by decide
  have hdescent : baseEnd_3897372 < baseStart_3897372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897398 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3897398 : Nat := 118140960795 + 3897398 * 2 ^ 59
def prefixEnd_3897398 : Nat := 4983230072969 + 3 ^ 40 * 3897398 * 2
def baseEnd_3897398 : Nat := 2001238475871847646101199

theorem tailTrace_3897398 : CollatzResearch.WordTrace tailWord_3897398 prefixEnd_3897398 2001238475871847646101199 := by
  unfold tailWord_3897398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884361445900008964411803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94766522089600095620392565 8884361445900008964411803)
  ·
    refine ⟨13326542168850013446617705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8884361445900008964411803 13326542168850013446617705)
    ·
      refine ⟨9994906626637510084963279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13326542168850013446617705 9994906626637510084963279)
      ·
        refine ⟨14992359939956265127444919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994906626637510084963279 14992359939956265127444919)
        ·
          refine ⟨22488539909934397691167379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14992359939956265127444919 22488539909934397691167379)
          ·
            refine ⟨33732809864901596536751069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22488539909934397691167379 33732809864901596536751069)
            ·
              refine ⟨12649803699338098701281651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33732809864901596536751069 12649803699338098701281651)
              ·
                refine ⟨18974705549007148051922477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12649803699338098701281651 18974705549007148051922477)
                ·
                  refine ⟨7115514580877680519470929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18974705549007148051922477 7115514580877680519470929)
                  ·
                    refine ⟨5336635935658260389603197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7115514580877680519470929 5336635935658260389603197)
                    ·
                      refine ⟨2001238475871847646101199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336635935658260389603197 2001238475871847646101199)
                      ·
                        rfl

theorem cell23_3897398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3897398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897398 prefixEnd_3897398 := by exact prefixLift 3897398
  have htrace : WordTrace (prefixWord ++ tailWord_3897398) baseStart_3897398 baseEnd_3897398 := by
    simpa [prefixWord, tailWord_3897398, baseEnd_3897398] using wordTrace_append hprefix tailTrace_3897398
  have hstable : (prefixWord ++ tailWord_3897398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897398).length < 2 ^ (prefixWord ++ tailWord_3897398).sum := by decide
  have hdescent : baseEnd_3897398 < baseStart_3897398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897411 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 3]
def baseStart_3897411 : Nat := 118140960795 + 3897411 * 2 ^ 59
def prefixEnd_3897411 : Nat := 4983230072969 + 3 ^ 40 * 3897411 * 2
def baseEnd_3897411 : Nat := 2001245151120356095238639

theorem tailTrace_3897411 : CollatzResearch.WordTrace tailWord_3897411 prefixEnd_3897411 2001245151120356095238639 := by
  unfold tailWord_3897411
  simp only [CollatzResearch.WordTrace]
  refine ⟨142150257283353046650812087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94766838188902031100541391 142150257283353046650812087)
  ·
    refine ⟨213225385925029569976218131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142150257283353046650812087 213225385925029569976218131)
    ·
      refine ⟨319838078887544354964327197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213225385925029569976218131 319838078887544354964327197)
      ·
        refine ⟨119939279582829133111622699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319838078887544354964327197 119939279582829133111622699)
        ·
          refine ⟨179908919374243699667434049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119939279582829133111622699 179908919374243699667434049)
          ·
            refine ⟨134931689530682774750575537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179908919374243699667434049 134931689530682774750575537)
            ·
              refine ⟨101198767148012081062931653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134931689530682774750575537 101198767148012081062931653)
              ·
                refine ⟨18974768840252265199299685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101198767148012081062931653 18974768840252265199299685)
                ·
                  refine ⟨3557769157547299724868691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18974768840252265199299685 3557769157547299724868691)
                  ·
                    refine ⟨5336653736320949587303037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3557769157547299724868691 5336653736320949587303037)
                    ·
                      refine ⟨2001245151120356095238639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336653736320949587303037 2001245151120356095238639)
                      ·
                        rfl

theorem cell23_3897411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_3897411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897411 prefixEnd_3897411 := by exact prefixLift 3897411
  have htrace : WordTrace (prefixWord ++ tailWord_3897411) baseStart_3897411 baseEnd_3897411 := by
    simpa [prefixWord, tailWord_3897411, baseEnd_3897411] using wordTrace_append hprefix tailTrace_3897411
  have hstable : (prefixWord ++ tailWord_3897411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897411).length < 2 ^ (prefixWord ++ tailWord_3897411).sum := by decide
  have hdescent : baseEnd_3897411 < baseStart_3897411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897429 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3897429 : Nat := 118140960795 + 3897429 * 2 ^ 59
def prefixEnd_3897429 : Nat := 4983230072969 + 3 ^ 40 * 3897429 * 2
def baseEnd_3897429 : Nat := 2001254393772137024813557

theorem tailTrace_3897429 : CollatzResearch.WordTrace tailWord_3897429 prefixEnd_3897429 2001254393772137024813557 := by
  unfold tailWord_3897429
  simp only [CollatzResearch.WordTrace]
  refine ⟨142150913797287835724967341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94767275864858557149978227 142150913797287835724967341)
  ·
    refine ⟨53306592673982938396862753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142150913797287835724967341 53306592673982938396862753)
    ·
      refine ⟨39979944505487203797647065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53306592673982938396862753 39979944505487203797647065)
      ·
        refine ⟨29984958379115402848235299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39979944505487203797647065 29984958379115402848235299)
        ·
          refine ⟨44977437568673104272352949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29984958379115402848235299 44977437568673104272352949)
          ·
            refine ⟨4216634772063103525533089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44977437568673104272352949 4216634772063103525533089)
            ·
              refine ⟨3162476079047327644149817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216634772063103525533089 3162476079047327644149817)
              ·
                refine ⟨2371857059285495733112363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3162476079047327644149817 2371857059285495733112363)
                ·
                  refine ⟨3557785588928243599668545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2371857059285495733112363 3557785588928243599668545)
                  ·
                    refine ⟨2668339191696182699751409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3557785588928243599668545 2668339191696182699751409)
                    ·
                      refine ⟨2001254393772137024813557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668339191696182699751409 2001254393772137024813557)
                      ·
                        rfl

theorem cell23_3897429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3897429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897429 prefixEnd_3897429 := by exact prefixLift 3897429
  have htrace : WordTrace (prefixWord ++ tailWord_3897429) baseStart_3897429 baseEnd_3897429 := by
    simpa [prefixWord, tailWord_3897429, baseEnd_3897429] using wordTrace_append hprefix tailTrace_3897429
  have hstable : (prefixWord ++ tailWord_3897429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897429).length < 2 ^ (prefixWord ++ tailWord_3897429).sum := by decide
  have hdescent : baseEnd_3897429 < baseStart_3897429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897434 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3897434 : Nat := 118140960795 + 3897434 * 2 ^ 59
def prefixEnd_3897434 : Nat := 4983230072969 + 3 ^ 40 * 3897434 * 2
def baseEnd_3897434 : Nat := 2001256961175409505251033

theorem tailTrace_3897434 : CollatzResearch.WordTrace tailWord_3897434 prefixEnd_3897434 2001256961175409505251033 := by
  unfold tailWord_3897434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537774040567430394724839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94767397441513147719266237 35537774040567430394724839)
  ·
    refine ⟨53306661060851145592087259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35537774040567430394724839 53306661060851145592087259)
    ·
      refine ⟨79959991591276718388130889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53306661060851145592087259 79959991591276718388130889)
      ·
        refine ⟨59969993693457538791098167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79959991591276718388130889 59969993693457538791098167)
        ·
          refine ⟨89954990540186308186647251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59969993693457538791098167 89954990540186308186647251)
          ·
            refine ⟨134932485810279462279970877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89954990540186308186647251 134932485810279462279970877)
            ·
              refine ⟨50599682178854798354989079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134932485810279462279970877 50599682178854798354989079)
              ·
                refine ⟨75899523268282197532483619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50599682178854798354989079 75899523268282197532483619)
                ·
                  refine ⟨113849284902423296298725429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75899523268282197532483619 113849284902423296298725429)
                  ·
                    refine ⟨10673370459602184028005509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113849284902423296298725429 10673370459602184028005509)
                    ·
                      refine ⟨2001256961175409505251033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10673370459602184028005509 2001256961175409505251033)
                      ·
                        rfl

theorem cell23_3897434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3897434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897434 prefixEnd_3897434 := by exact prefixLift 3897434
  have htrace : WordTrace (prefixWord ++ tailWord_3897434) baseStart_3897434 baseEnd_3897434 := by
    simpa [prefixWord, tailWord_3897434, baseEnd_3897434] using wordTrace_append hprefix tailTrace_3897434
  have hstable : (prefixWord ++ tailWord_3897434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897434).length < 2 ^ (prefixWord ++ tailWord_3897434).sum := by decide
  have hdescent : baseEnd_3897434 < baseStart_3897434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897444 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3897444 : Nat := 118140960795 + 3897444 * 2 ^ 59
def prefixEnd_3897444 : Nat := 4983230072969 + 3 ^ 40 * 3897444 * 2
def baseEnd_3897444 : Nat := 667087365327318155375329

theorem tailTrace_3897444 : CollatzResearch.WordTrace tailWord_3897444 prefixEnd_3897444 667087365327318155375329 := by
  unfold tailWord_3897444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71075730446116746643381693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94767640594822328857842257 71075730446116746643381693)
  ·
    refine ⟨26653398917293779991268135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71075730446116746643381693 26653398917293779991268135)
    ·
      refine ⟨39980098375940669986902203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26653398917293779991268135 39980098375940669986902203)
      ·
        refine ⟨59970147563911004980353305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39980098375940669986902203 59970147563911004980353305)
        ·
          refine ⟨44977610672933253735264979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59970147563911004980353305 44977610672933253735264979)
          ·
            refine ⟨67466416009399880602897469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44977610672933253735264979 67466416009399880602897469)
            ·
              refine ⟨25299906003524955226086551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67466416009399880602897469 25299906003524955226086551)
              ·
                refine ⟨37949859005287432839129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25299906003524955226086551 37949859005287432839129827)
                ·
                  refine ⟨56924788507931149258694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37949859005287432839129827 56924788507931149258694741)
                  ·
                    refine ⟨667087365327318155375329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56924788507931149258694741 667087365327318155375329)
                    ·
                      rfl

theorem cell23_3897444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3897444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897444 prefixEnd_3897444 := by exact prefixLift 3897444
  have htrace : WordTrace (prefixWord ++ tailWord_3897444) baseStart_3897444 baseEnd_3897444 := by
    simpa [prefixWord, tailWord_3897444, baseEnd_3897444] using wordTrace_append hprefix tailTrace_3897444
  have hstable : (prefixWord ++ tailWord_3897444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897444).length < 2 ^ (prefixWord ++ tailWord_3897444).sum := by decide
  have hdescent : baseEnd_3897444 < baseStart_3897444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897464 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_3897464 : Nat := 118140960795 + 3897464 * 2 ^ 59
def prefixEnd_3897464 : Nat := 4983230072969 + 3 ^ 40 * 3897464 * 2
def baseEnd_3897464 : Nat := 2001272365595044387875895

theorem tailTrace_3897464 : CollatzResearch.WordTrace tailWord_3897464 prefixEnd_3897464 2001272365595044387875895 := by
  unfold tailWord_3897464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71076095176080518351245723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94768126901440691134994297 71076095176080518351245723)
  ·
    refine ⟨106614142764120777526868585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71076095176080518351245723 106614142764120777526868585)
    ·
      refine ⟨79960607073090583145151439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106614142764120777526868585 79960607073090583145151439)
      ·
        refine ⟨119940910609635874717727159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79960607073090583145151439 119940910609635874717727159)
        ·
          refine ⟨179911365914453812076590739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119940910609635874717727159 179911365914453812076590739)
          ·
            refine ⟨269867048871680718114886109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179911365914453812076590739 269867048871680718114886109)
            ·
              refine ⟨101200143326880269293082291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269867048871680718114886109 101200143326880269293082291)
              ·
                refine ⟨151800214990320403939623437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101200143326880269293082291 151800214990320403939623437)
                ·
                  refine ⟨56925080621370151477358789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151800214990320403939623437 56925080621370151477358789)
                  ·
                    refine ⟨10673452616506903402004773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56925080621370151477358789 10673452616506903402004773)
                    ·
                      refine ⟨2001272365595044387875895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10673452616506903402004773 2001272365595044387875895)
                      ·
                        rfl

theorem cell23_3897464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_3897464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897464 prefixEnd_3897464 := by exact prefixLift 3897464
  have htrace : WordTrace (prefixWord ++ tailWord_3897464) baseStart_3897464 baseEnd_3897464 := by
    simpa [prefixWord, tailWord_3897464, baseEnd_3897464] using wordTrace_append hprefix tailTrace_3897464
  have hstable : (prefixWord ++ tailWord_3897464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897464).length < 2 ^ (prefixWord ++ tailWord_3897464).sum := by decide
  have hdescent : baseEnd_3897464 < baseStart_3897464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897468 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_3897468 : Nat := 118140960795 + 3897468 * 2 ^ 59
def prefixEnd_3897468 : Nat := 4983230072969 + 3 ^ 40 * 3897468 * 2
def baseEnd_3897468 : Nat := 2001274419517662372225877

theorem tailTrace_3897468 : CollatzResearch.WordTrace tailWord_3897468 prefixEnd_3897468 2001274419517662372225877 := by
  unfold tailWord_3897468
  simp only [CollatzResearch.WordTrace]
  refine ⟨71076168122073272692818529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94768224162764363590424705 71076168122073272692818529)
  ·
    refine ⟨53307126091554954519613897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71076168122073272692818529 53307126091554954519613897)
    ·
      refine ⟨39980344568666215889710423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53307126091554954519613897 39980344568666215889710423)
      ·
        refine ⟨59970516852999323834565635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39980344568666215889710423 59970516852999323834565635)
        ·
          refine ⟨89955775279498985751848453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59970516852999323834565635 89955775279498985751848453)
          ·
            refine ⟨16866707864906059828471585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89955775279498985751848453 16866707864906059828471585)
            ·
              refine ⟨12650030898679544871353689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16866707864906059828471585 12650030898679544871353689)
              ·
                refine ⟨9487523174009658653515267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12650030898679544871353689 9487523174009658653515267)
                ·
                  refine ⟨14231284761014487980272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9487523174009658653515267 14231284761014487980272901)
                  ·
                    refine ⟨2668365892690216496301169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14231284761014487980272901 2668365892690216496301169)
                    ·
                      refine ⟨2001274419517662372225877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668365892690216496301169 2001274419517662372225877)
                      ·
                        rfl

theorem cell23_3897468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_3897468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897468 prefixEnd_3897468 := by exact prefixLift 3897468
  have htrace : WordTrace (prefixWord ++ tailWord_3897468) baseStart_3897468 baseEnd_3897468 := by
    simpa [prefixWord, tailWord_3897468, baseEnd_3897468] using wordTrace_append hprefix tailTrace_3897468
  have hstable : (prefixWord ++ tailWord_3897468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897468).length < 2 ^ (prefixWord ++ tailWord_3897468).sum := by decide
  have hdescent : baseEnd_3897468 < baseStart_3897468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897541 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3897541 : Nat := 118140960795 + 3897541 * 2 ^ 59
def prefixEnd_3897541 : Nat := 4983230072969 + 3 ^ 40 * 3897541 * 2
def baseEnd_3897541 : Nat := 2001311903605440586613041

theorem tailTrace_3897541 : CollatzResearch.WordTrace tailWord_3897541 prefixEnd_3897541 2001311903605440586613041 := by
  unfold tailWord_3897541
  simp only [CollatzResearch.WordTrace]
  refine ⟨142154998772882078853044477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94769999181921385902029651 142154998772882078853044477)
  ·
    refine ⟨53308124539830779569891679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142154998772882078853044477 53308124539830779569891679)
    ·
      refine ⟨79962186809746169354837519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53308124539830779569891679 79962186809746169354837519)
      ·
        refine ⟨119943280214619254032256279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79962186809746169354837519 119943280214619254032256279)
        ·
          refine ⟨179914920321928881048384419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119943280214619254032256279 179914920321928881048384419)
          ·
            refine ⟨269872380482893321572576629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179914920321928881048384419 269872380482893321572576629)
            ·
              refine ⟨25300535670271248897429059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269872380482893321572576629 25300535670271248897429059)
              ·
                refine ⟨37950803505406873346143589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25300535670271248897429059 37950803505406873346143589)
                ·
                  refine ⟨7115775657263788752401923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37950803505406873346143589 7115775657263788752401923)
                  ·
                    refine ⟨10673663485895683128602885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7115775657263788752401923 10673663485895683128602885)
                    ·
                      refine ⟨2001311903605440586613041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10673663485895683128602885 2001311903605440586613041)
                      ·
                        rfl

theorem cell23_3897541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3897541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897541 prefixEnd_3897541 := by exact prefixLift 3897541
  have htrace : WordTrace (prefixWord ++ tailWord_3897541) baseStart_3897541 baseEnd_3897541 := by
    simpa [prefixWord, tailWord_3897541, baseEnd_3897541] using wordTrace_append hprefix tailTrace_3897541
  have hstable : (prefixWord ++ tailWord_3897541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897541).length < 2 ^ (prefixWord ++ tailWord_3897541).sum := by decide
  have hdescent : baseEnd_3897541 < baseStart_3897541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897561 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_3897561 : Nat := 118140960795 + 3897561 * 2 ^ 59
def prefixEnd_3897561 : Nat := 4983230072969 + 3 ^ 40 * 3897561 * 2
def baseEnd_3897561 : Nat := 2001322173218530508362949

theorem tailTrace_3897561 : CollatzResearch.WordTrace tailWord_3897561 prefixEnd_3897561 2001322173218530508362949 := by
  unfold tailWord_3897561
  simp only [CollatzResearch.WordTrace]
  refine ⟨142155728232809622268772537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94770485488539748179181691 142155728232809622268772537)
  ·
    refine ⟨106616796174607216701579403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142155728232809622268772537 106616796174607216701579403)
    ·
      refine ⟨159925194261910825052369105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106616796174607216701579403 159925194261910825052369105)
      ·
        refine ⟨119943895696433118789276829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159925194261910825052369105 119943895696433118789276829)
        ·
          refine ⟨44978960886162419545978811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119943895696433118789276829 44978960886162419545978811)
          ·
            refine ⟨67468441329243629318968217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44978960886162419545978811 67468441329243629318968217)
            ·
              refine ⟨50601330996932721989226163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67468441329243629318968217 50601330996932721989226163)
              ·
                refine ⟨75901996495399082983839245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50601330996932721989226163 75901996495399082983839245)
                ·
                  refine ⟨28463248685774656118939717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75901996495399082983839245 28463248685774656118939717)
                  ·
                    refine ⟨5336859128582748022301197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28463248685774656118939717 5336859128582748022301197)
                    ·
                      refine ⟨2001322173218530508362949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336859128582748022301197 2001322173218530508362949)
                      ·
                        rfl

theorem cell23_3897561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_3897561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897561 prefixEnd_3897561 := by exact prefixLift 3897561
  have htrace : WordTrace (prefixWord ++ tailWord_3897561) baseStart_3897561 baseEnd_3897561 := by
    simpa [prefixWord, tailWord_3897561, baseEnd_3897561] using wordTrace_append hprefix tailTrace_3897561
  have hstable : (prefixWord ++ tailWord_3897561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897561).length < 2 ^ (prefixWord ++ tailWord_3897561).sum := by decide
  have hdescent : baseEnd_3897561 < baseStart_3897561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897575 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3897575 : Nat := 118140960795 + 3897575 * 2 ^ 59
def prefixEnd_3897575 : Nat := 4983230072969 + 3 ^ 40 * 3897575 * 2
def baseEnd_3897575 : Nat := 2001329361947693453587885

theorem tailTrace_3897575 : CollatzResearch.WordTrace tailWord_3897575 prefixEnd_3897575 2001329361947693453587885 := by
  unfold tailWord_3897575
  simp only [CollatzResearch.WordTrace]
  refine ⟨142156238854758902659782179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94770825903172601773188119 142156238854758902659782179)
  ·
    refine ⟨213234358282138353989673269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142156238854758902659782179 213234358282138353989673269)
    ·
      refine ⟨19990721088950470686531869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213234358282138353989673269 19990721088950470686531869)
      ·
        refine ⟨7496520408356426507449451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19990721088950470686531869 7496520408356426507449451)
        ·
          refine ⟨11244780612534639761174177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7496520408356426507449451 11244780612534639761174177)
          ·
            refine ⟨8433585459400979820880633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11244780612534639761174177 8433585459400979820880633)
            ·
              refine ⟨6325189094550734865660475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8433585459400979820880633 6325189094550734865660475)
              ·
                refine ⟨9487783641826102298490713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325189094550734865660475 9487783641826102298490713)
                ·
                  refine ⟨7115837731369576723868035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487783641826102298490713 7115837731369576723868035)
                  ·
                    refine ⟨10673756597054365085802053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7115837731369576723868035 10673756597054365085802053)
                    ·
                      refine ⟨2001329361947693453587885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10673756597054365085802053 2001329361947693453587885)
                      ·
                        rfl

theorem cell23_3897575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3897575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897575 prefixEnd_3897575 := by exact prefixLift 3897575
  have htrace : WordTrace (prefixWord ++ tailWord_3897575) baseStart_3897575 baseEnd_3897575 := by
    simpa [prefixWord, tailWord_3897575, baseEnd_3897575] using wordTrace_append hprefix tailTrace_3897575
  have hstable : (prefixWord ++ tailWord_3897575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897575).length < 2 ^ (prefixWord ++ tailWord_3897575).sum := by decide
  have hdescent : baseEnd_3897575 < baseStart_3897575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897601 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3897601 : Nat := 118140960795 + 3897601 * 2 ^ 59
def prefixEnd_3897601 : Nat := 4983230072969 + 3 ^ 40 * 3897601 * 2
def baseEnd_3897601 : Nat := 2001342712444710351862765

theorem tailTrace_3897601 : CollatzResearch.WordTrace tailWord_3897601 prefixEnd_3897601 2001342712444710351862765 := by
  unfold tailWord_3897601
  simp only [CollatzResearch.WordTrace]
  refine ⟨142157187152664709100228657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94771458101776472733485771 142157187152664709100228657)
  ·
    refine ⟨106617890364498531825171493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142157187152664709100228657 106617890364498531825171493)
    ·
      refine ⟨19990854443343474717219655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106617890364498531825171493 19990854443343474717219655)
      ·
        refine ⟨29986281665015212075829483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990854443343474717219655 29986281665015212075829483)
        ·
          refine ⟨44979422497522818113744225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29986281665015212075829483 44979422497522818113744225)
          ·
            refine ⟨33734566873142113585308169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44979422497522818113744225 33734566873142113585308169)
            ·
              refine ⟨25300925154856585188981127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33734566873142113585308169 25300925154856585188981127)
              ·
                refine ⟨37951387732284877783471691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25300925154856585188981127 37951387732284877783471691)
                ·
                  refine ⟨56927081598427316675207537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37951387732284877783471691 56927081598427316675207537)
                  ·
                    refine ⟨42695311198820487506405653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56927081598427316675207537 42695311198820487506405653)
                    ·
                      refine ⟨2001342712444710351862765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42695311198820487506405653 2001342712444710351862765)
                      ·
                        rfl

theorem cell23_3897601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3897601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897601 prefixEnd_3897601 := by exact prefixLift 3897601
  have htrace : WordTrace (prefixWord ++ tailWord_3897601) baseStart_3897601 baseEnd_3897601 := by
    simpa [prefixWord, tailWord_3897601, baseEnd_3897601] using wordTrace_append hprefix tailTrace_3897601
  have hstable : (prefixWord ++ tailWord_3897601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897601).length < 2 ^ (prefixWord ++ tailWord_3897601).sum := by decide
  have hdescent : baseEnd_3897601 < baseStart_3897601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897611 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 5, 5]
def baseStart_3897611 : Nat := 118140960795 + 3897611 * 2 ^ 59
def prefixEnd_3897611 : Nat := 4983230072969 + 3 ^ 40 * 3897611 * 2
def baseEnd_3897611 : Nat := 667115949083751770912573

theorem tailTrace_3897611 : CollatzResearch.WordTrace tailWord_3897611 prefixEnd_3897611 667115949083751770912573 := by
  unfold tailWord_3897611
  simp only [CollatzResearch.WordTrace]
  refine ⟨142157551882628480808092687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94771701255085653872061791 142157551882628480808092687)
  ·
    refine ⟨213236327823942721212139031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142157551882628480808092687 213236327823942721212139031)
    ·
      refine ⟨319854491735914081818208547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213236327823942721212139031 319854491735914081818208547)
      ·
        refine ⟨479781737603871122727312821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319854491735914081818208547 479781737603871122727312821)
        ·
          refine ⟨44979537900362917755685577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479781737603871122727312821 44979537900362917755685577)
          ·
            refine ⟨33734653425272188316764183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44979537900362917755685577 33734653425272188316764183)
            ·
              refine ⟨50601980137908282475146275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33734653425272188316764183 50601980137908282475146275)
              ·
                refine ⟨75902970206862423712719413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50601980137908282475146275 75902970206862423712719413)
                ·
                  refine ⟨7115903456893352223067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75902970206862423712719413 7115903456893352223067445)
                  ·
                    refine ⟨667115949083751770912573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7115903456893352223067445 667115949083751770912573)
                    ·
                      rfl

theorem cell23_3897611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 5].length) (baseStart_3897611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897611 prefixEnd_3897611 := by exact prefixLift 3897611
  have htrace : WordTrace (prefixWord ++ tailWord_3897611) baseStart_3897611 baseEnd_3897611 := by
    simpa [prefixWord, tailWord_3897611, baseEnd_3897611] using wordTrace_append hprefix tailTrace_3897611
  have hstable : (prefixWord ++ tailWord_3897611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897611).length < 2 ^ (prefixWord ++ tailWord_3897611).sum := by decide
  have hdescent : baseEnd_3897611 < baseStart_3897611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897628 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3897628 : Nat := 118140960795 + 3897628 * 2 ^ 59
def prefixEnd_3897628 : Nat := 4983230072969 + 3 ^ 40 * 3897628 * 2
def baseEnd_3897628 : Nat := 667118858807460582075047

theorem tailTrace_3897628 : CollatzResearch.WordTrace tailWord_3897628 prefixEnd_3897628 667118858807460582075047 := by
  unfold tailWord_3897628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71079085961783446355730769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94772114615711261807641025 71079085961783446355730769)
  ·
    refine ⟨53309314471337584766798077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71079085961783446355730769 53309314471337584766798077)
    ·
      refine ⟨19990992926751594287549279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53309314471337584766798077 19990992926751594287549279)
      ·
        refine ⟨29986489390127391431323919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19990992926751594287549279 29986489390127391431323919)
        ·
          refine ⟨44979734085191087146985879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29986489390127391431323919 44979734085191087146985879)
          ·
            refine ⟨67469601127786630720478819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44979734085191087146985879 67469601127786630720478819)
            ·
              refine ⟨101204401691679946080718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67469601127786630720478819 101204401691679946080718229)
              ·
                refine ⟨4743956329297497472533667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101204401691679946080718229 4743956329297497472533667)
                ·
                  refine ⟨7115934493946246208800501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4743956329297497472533667 7115934493946246208800501)
                  ·
                    refine ⟨667118858807460582075047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7115934493946246208800501 667118858807460582075047)
                    ·
                      rfl

theorem cell23_3897628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3897628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897628 prefixEnd_3897628 := by exact prefixLift 3897628
  have htrace : WordTrace (prefixWord ++ tailWord_3897628) baseStart_3897628 baseEnd_3897628 := by
    simpa [prefixWord, tailWord_3897628, baseEnd_3897628] using wordTrace_append hprefix tailTrace_3897628
  have hstable : (prefixWord ++ tailWord_3897628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897628).length < 2 ^ (prefixWord ++ tailWord_3897628).sum := by decide
  have hdescent : baseEnd_3897628 < baseStart_3897628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897629 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3897629 : Nat := 118140960795 + 3897629 * 2 ^ 59
def prefixEnd_3897629 : Nat := 4983230072969 + 3 ^ 40 * 3897629 * 2
def baseEnd_3897629 : Nat := 2001357089903036242312637

theorem tailTrace_3897629 : CollatzResearch.WordTrace tailWord_3897629 prefixEnd_3897629 2001357089903036242312637 := by
  unfold tailWord_3897629
  simp only [CollatzResearch.WordTrace]
  refine ⟨142158208396563269882247941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94772138931042179921498627 142158208396563269882247941)
  ·
    refine ⟨26654664074355613102921489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142158208396563269882247941 26654664074355613102921489)
    ·
      refine ⟨19990998055766709827191117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26654664074355613102921489 19990998055766709827191117)
      ·
        refine ⟨7496624270912516185196669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19990998055766709827191117 7496624270912516185196669)
        ·
          refine ⟨2811234101592193569448751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7496624270912516185196669 2811234101592193569448751)
          ·
            refine ⟨4216851152388290354173127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811234101592193569448751 4216851152388290354173127)
            ·
              refine ⟨6325276728582435531259691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216851152388290354173127 6325276728582435531259691)
              ·
                refine ⟨9487915092873653296889537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325276728582435531259691 9487915092873653296889537)
                ·
                  refine ⟨7115936319655239972667153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9487915092873653296889537 7115936319655239972667153)
                  ·
                    refine ⟨5336952239741429979500365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7115936319655239972667153 5336952239741429979500365)
                    ·
                      refine ⟨2001357089903036242312637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5336952239741429979500365 2001357089903036242312637)
                      ·
                        rfl

theorem cell23_3897629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3897629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897629 prefixEnd_3897629 := by exact prefixLift 3897629
  have htrace : WordTrace (prefixWord ++ tailWord_3897629) baseStart_3897629 baseEnd_3897629 := by
    simpa [prefixWord, tailWord_3897629, baseEnd_3897629] using wordTrace_append hprefix tailTrace_3897629
  have hstable : (prefixWord ++ tailWord_3897629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897629).length < 2 ^ (prefixWord ++ tailWord_3897629).sum := by decide
  have hdescent : baseEnd_3897629 < baseStart_3897629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897671 : List Nat := [1, 1, 4, 1, 2, 2, 2, 10]
def baseStart_3897671 : Nat := 118140960795 + 3897671 * 2 ^ 59
def prefixEnd_3897671 : Nat := 4983230072969 + 3 ^ 40 * 3897671 * 2
def baseEnd_3897671 : Nat := 74125135410760188073609

theorem tailTrace_3897671 : CollatzResearch.WordTrace tailWord_3897671 prefixEnd_3897671 74125135410760188073609 := by
  unfold tailWord_3897671
  simp only [CollatzResearch.WordTrace]
  refine ⟨142159740262411111055276867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94773160174940740703517911 142159740262411111055276867)
  ·
    refine ⟨213239610393616666582915301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142159740262411111055276867 213239610393616666582915301)
    ·
      refine ⟨39982426948803124984296619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213239610393616666582915301 39982426948803124984296619)
      ·
        refine ⟨59973640423204687476444929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39982426948803124984296619 59973640423204687476444929)
        ·
          refine ⟨44980230317403515607333697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59973640423204687476444929 44980230317403515607333697)
          ·
            refine ⟨33735172738052636705500273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44980230317403515607333697 33735172738052636705500273)
            ·
              refine ⟨25301379553539477529125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33735172738052636705500273 25301379553539477529125205)
              ·
                refine ⟨74125135410760188073609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25301379553539477529125205 74125135410760188073609)
                ·
                  rfl

theorem cell23_3897671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 10].length) (baseStart_3897671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897671 prefixEnd_3897671 := by exact prefixLift 3897671
  have htrace : WordTrace (prefixWord ++ tailWord_3897671) baseStart_3897671 baseEnd_3897671 := by
    simpa [prefixWord, tailWord_3897671, baseEnd_3897671] using wordTrace_append hprefix tailTrace_3897671
  have hstable : (prefixWord ++ tailWord_3897671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897671).length < 2 ^ (prefixWord ++ tailWord_3897671).sum := by decide
  have hdescent : baseEnd_3897671 < baseStart_3897671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897678 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3897678 : Nat := 118140960795 + 3897678 * 2 ^ 59
def prefixEnd_3897678 : Nat := 4983230072969 + 3 ^ 40 * 3897678 * 2
def baseEnd_3897678 : Nat := 2001382250455106550599911

theorem tailTrace_3897678 : CollatzResearch.WordTrace tailWord_3897678 prefixEnd_3897678 2001382250455106550599911 := by
  unfold tailWord_3897678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17769999446673218906347711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94773330382257167500521125 17769999446673218906347711)
  ·
    refine ⟨26654999170009828359521567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17769999446673218906347711 26654999170009828359521567)
    ·
      refine ⟨39982498755014742539282351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26654999170009828359521567 39982498755014742539282351)
      ·
        refine ⟨59973748132522113808923527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39982498755014742539282351 59973748132522113808923527)
        ·
          refine ⟨89960622198783170713385291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59973748132522113808923527 89960622198783170713385291)
          ·
            refine ⟨134940933298174756070077937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89960622198783170713385291 134940933298174756070077937)
            ·
              refine ⟨101205699973631067052558453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134940933298174756070077937 101205699973631067052558453)
              ·
                refine ⟨9488034372527912536177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101205699973631067052558453 9488034372527912536177355)
                ·
                  refine ⟨14232051558791868804266033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488034372527912536177355 14232051558791868804266033)
                  ·
                    refine ⟨10674038669093901603199525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14232051558791868804266033 10674038669093901603199525)
                    ·
                      refine ⟨2001382250455106550599911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10674038669093901603199525 2001382250455106550599911)
                      ·
                        rfl

theorem cell23_3897678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3897678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897678 prefixEnd_3897678 := by exact prefixLift 3897678
  have htrace : WordTrace (prefixWord ++ tailWord_3897678) baseStart_3897678 baseEnd_3897678 := by
    simpa [prefixWord, tailWord_3897678, baseEnd_3897678] using wordTrace_append hprefix tailTrace_3897678
  have hstable : (prefixWord ++ tailWord_3897678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897678).length < 2 ^ (prefixWord ++ tailWord_3897678).sum := by decide
  have hdescent : baseEnd_3897678 < baseStart_3897678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897682 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_3897682 : Nat := 118140960795 + 3897682 * 2 ^ 59
def prefixEnd_3897682 : Nat := 4983230072969 + 3 ^ 40 * 3897682 * 2
def baseEnd_3897682 : Nat := 2001384304377724534949893

theorem tailTrace_3897682 : CollatzResearch.WordTrace tailWord_3897682 prefixEnd_3897682 2001384304377724534949893 := by
  unfold tailWord_3897682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35540035366342814983481825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94773427643580839955951533 35540035366342814983481825)
  ·
    refine ⟨26655026524757111237611369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35540035366342814983481825 26655026524757111237611369)
    ·
      refine ⟨19991269893567833428208527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26655026524757111237611369 19991269893567833428208527)
      ·
        refine ⟨29986904840351750142312791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19991269893567833428208527 29986904840351750142312791)
        ·
          refine ⟨44980357260527625213469187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29986904840351750142312791 44980357260527625213469187)
          ·
            refine ⟨67470535890791437820203781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44980357260527625213469187 67470535890791437820203781)
            ·
              refine ⟨12650725479523394591288209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67470535890791437820203781 12650725479523394591288209)
              ·
                refine ⟨9488044109642545943466157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12650725479523394591288209 9488044109642545943466157)
                ·
                  refine ⟨3558016541115954728799809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9488044109642545943466157 3558016541115954728799809)
                  ·
                    refine ⟨2668512405836966046599857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558016541115954728799809 2668512405836966046599857)
                    ·
                      refine ⟨2001384304377724534949893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668512405836966046599857 2001384304377724534949893)
                      ·
                        rfl

theorem cell23_3897682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_3897682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897682 prefixEnd_3897682 := by exact prefixLift 3897682
  have htrace : WordTrace (prefixWord ++ tailWord_3897682) baseStart_3897682 baseEnd_3897682 := by
    simpa [prefixWord, tailWord_3897682, baseEnd_3897682] using wordTrace_append hprefix tailTrace_3897682
  have hstable : (prefixWord ++ tailWord_3897682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897682).length < 2 ^ (prefixWord ++ tailWord_3897682).sum := by decide
  have hdescent : baseEnd_3897682 < baseStart_3897682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897732 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3897732 : Nat := 118140960795 + 3897732 * 2 ^ 59
def prefixEnd_3897732 : Nat := 4983230072969 + 3 ^ 40 * 3897732 * 2
def baseEnd_3897732 : Nat := 2001409978410449339324663

theorem tailTrace_3897732 : CollatzResearch.WordTrace tailWord_3897732 prefixEnd_3897732 2001409978410449339324663 := by
  unfold tailWord_3897732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71080982557595059236623725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94774643410126745648831633 71080982557595059236623725)
  ·
    refine ⟨26655368459098147213733897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71080982557595059236623725 26655368459098147213733897)
    ·
      refine ⟨19991526344323610410300423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26655368459098147213733897 19991526344323610410300423)
      ·
        refine ⟨29987289516485415615450635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19991526344323610410300423 29987289516485415615450635)
        ·
          refine ⟨44980934274728123423175953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29987289516485415615450635 44980934274728123423175953)
          ·
            refine ⟨33735700706046092567381965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44980934274728123423175953 33735700706046092567381965)
            ·
              refine ⟨12650887764767284712768237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33735700706046092567381965 12650887764767284712768237)
              ·
                refine ⟨4744082911787731767288089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12650887764767284712768237 4744082911787731767288089)
                ·
                  refine ⟨3558062183840798825466067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744082911787731767288089 3558062183840798825466067)
                  ·
                    refine ⟨5337093275761198238199101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558062183840798825466067 5337093275761198238199101)
                    ·
                      refine ⟨2001409978410449339324663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337093275761198238199101 2001409978410449339324663)
                      ·
                        rfl

theorem cell23_3897732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3897732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897732 prefixEnd_3897732 := by exact prefixLift 3897732
  have htrace : WordTrace (prefixWord ++ tailWord_3897732) baseStart_3897732 baseEnd_3897732 := by
    simpa [prefixWord, tailWord_3897732, baseEnd_3897732] using wordTrace_append hprefix tailTrace_3897732
  have hstable : (prefixWord ++ tailWord_3897732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897732).length < 2 ^ (prefixWord ++ tailWord_3897732).sum := by decide
  have hdescent : baseEnd_3897732 < baseStart_3897732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897759 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 1, 3, 2]
def baseStart_3897759 : Nat := 118140960795 + 3897759 * 2 ^ 59
def prefixEnd_3897759 : Nat := 4983230072969 + 3 ^ 40 * 3897759 * 2
def baseEnd_3897759 : Nat := 2001423842388120733687039

theorem tailTrace_3897759 : CollatzResearch.WordTrace tailWord_3897759 prefixEnd_3897759 2001423842388120733687039 := by
  unfold tailWord_3897759
  simp only [CollatzResearch.WordTrace]
  refine ⟨142162949886092302084480331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94775299924061534722986887 142162949886092302084480331)
  ·
    refine ⟨213244424829138453126720497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142162949886092302084480331 213244424829138453126720497)
    ·
      refine ⟨159933318621853839845040373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213244424829138453126720497 159933318621853839845040373)
      ·
        refine ⟨14993748620798797485472535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159933318621853839845040373 14993748620798797485472535)
        ·
          refine ⟨22490622931198196228208803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993748620798797485472535 22490622931198196228208803)
          ·
            refine ⟨33735934396797294342313205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22490622931198196228208803 33735934396797294342313205)
            ·
              refine ⟨3162743849699746344591863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33735934396797294342313205 3162743849699746344591863)
              ·
                refine ⟨4744115774549619516887795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162743849699746344591863 4744115774549619516887795)
                ·
                  refine ⟨7116173661824429275331693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744115774549619516887795 7116173661824429275331693)
                  ·
                    refine ⟨2668565123184160978249385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7116173661824429275331693 2668565123184160978249385)
                    ·
                      refine ⟨2001423842388120733687039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668565123184160978249385 2001423842388120733687039)
                      ·
                        rfl

theorem cell23_3897759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_3897759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897759 prefixEnd_3897759 := by exact prefixLift 3897759
  have htrace : WordTrace (prefixWord ++ tailWord_3897759) baseStart_3897759 baseEnd_3897759 := by
    simpa [prefixWord, tailWord_3897759, baseEnd_3897759] using wordTrace_append hprefix tailTrace_3897759
  have hstable : (prefixWord ++ tailWord_3897759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897759).length < 2 ^ (prefixWord ++ tailWord_3897759).sum := by decide
  have hdescent : baseEnd_3897759 < baseStart_3897759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897778 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_3897778 : Nat := 118140960795 + 3897778 * 2 ^ 59
def prefixEnd_3897778 : Nat := 4983230072969 + 3 ^ 40 * 3897778 * 2
def baseEnd_3897778 : Nat := 222381510946728462149939

theorem tailTrace_3897778 : CollatzResearch.WordTrace tailWord_3897778 prefixEnd_3897778 222381510946728462149939 := by
  unfold tailWord_3897778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35540910718255867082355497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94775761915348978886281325 35540910718255867082355497)
  ·
    refine ⟨26655683038691900311766623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35540910718255867082355497 26655683038691900311766623)
    ·
      refine ⟨39983524558037850467649935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26655683038691900311766623 39983524558037850467649935)
      ·
        refine ⟨59975286837056775701474903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39983524558037850467649935 59975286837056775701474903)
        ·
          refine ⟨89962930255585163552212355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59975286837056775701474903 89962930255585163552212355)
          ·
            refine ⟨134944395383377745328318533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89962930255585163552212355 134944395383377745328318533)
            ·
              refine ⟨25302074134383327249059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134944395383377745328318533 25302074134383327249059725)
              ·
                refine ⟨9488277800393747718397397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25302074134383327249059725 9488277800393747718397397)
                ·
                  refine ⟨222381510946728462149939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9488277800393747718397397 222381510946728462149939)
                  ·
                    rfl

theorem cell23_3897778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_3897778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897778 prefixEnd_3897778 := by exact prefixLift 3897778
  have htrace : WordTrace (prefixWord ++ tailWord_3897778) baseStart_3897778 baseEnd_3897778 := by
    simpa [prefixWord, tailWord_3897778, baseEnd_3897778] using wordTrace_append hprefix tailTrace_3897778
  have hstable : (prefixWord ++ tailWord_3897778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897778).length < 2 ^ (prefixWord ++ tailWord_3897778).sum := by decide
  have hdescent : baseEnd_3897778 < baseStart_3897778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897785 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3897785 : Nat := 118140960795 + 3897785 * 2 ^ 59
def prefixEnd_3897785 : Nat := 4983230072969 + 3 ^ 40 * 3897785 * 2
def baseEnd_3897785 : Nat := 2001437192885137631961919

theorem tailTrace_3897785 : CollatzResearch.WordTrace tailWord_3897785 prefixEnd_3897785 2001437192885137631961919 := by
  unfold tailWord_3897785
  simp only [CollatzResearch.WordTrace]
  refine ⟨142163898183998108524926809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94775932122665405683284539 142163898183998108524926809)
  ·
    refine ⟨106622923637998581393695107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142163898183998108524926809 106622923637998581393695107)
    ·
      refine ⟨159934385456997872090542661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106622923637998581393695107 159934385456997872090542661)
      ·
        refine ⟨29987697273187101016976749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159934385456997872090542661 29987697273187101016976749)
        ·
          refine ⟨11245386477445162881366281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29987697273187101016976749 11245386477445162881366281)
          ·
            refine ⟨8434039858083872161024711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11245386477445162881366281 8434039858083872161024711)
            ·
              refine ⟨12651059787125808241537067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434039858083872161024711 12651059787125808241537067)
              ·
                refine ⟨18976589680688712362305601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12651059787125808241537067 18976589680688712362305601)
                ·
                  refine ⟨14232442260516534271729201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18976589680688712362305601 14232442260516534271729201)
                  ·
                    refine ⟨10674331695387400703796901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14232442260516534271729201 10674331695387400703796901)
                    ·
                      refine ⟨2001437192885137631961919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10674331695387400703796901 2001437192885137631961919)
                      ·
                        rfl

theorem cell23_3897785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3897785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897785 prefixEnd_3897785 := by exact prefixLift 3897785
  have htrace : WordTrace (prefixWord ++ tailWord_3897785) baseStart_3897785 baseEnd_3897785 := by
    simpa [prefixWord, tailWord_3897785, baseEnd_3897785] using wordTrace_append hprefix tailTrace_3897785
  have hstable : (prefixWord ++ tailWord_3897785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897785).length < 2 ^ (prefixWord ++ tailWord_3897785).sum := by decide
  have hdescent : baseEnd_3897785 < baseStart_3897785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897789 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3897789 : Nat := 118140960795 + 3897789 * 2 ^ 59
def prefixEnd_3897789 : Nat := 4983230072969 + 3 ^ 40 * 3897789 * 2
def baseEnd_3897789 : Nat := 2001439246807755616311901

theorem tailTrace_3897789 : CollatzResearch.WordTrace tailWord_3897789 prefixEnd_3897789 2001439246807755616311901 := by
  unfold tailWord_3897789
  simp only [CollatzResearch.WordTrace]
  refine ⟨142164044075983617208072421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94776029383989078138714947 142164044075983617208072421)
  ·
    refine ⟨26655758264246928226513579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142164044075983617208072421 26655758264246928226513579)
    ·
      refine ⟨39983637396370392339770369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26655758264246928226513579 39983637396370392339770369)
      ·
        refine ⟨29987728047277794254827777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39983637396370392339770369 29987728047277794254827777)
        ·
          refine ⟨22490796035458345691120833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29987728047277794254827777 22490796035458345691120833)
          ·
            refine ⟨16868097026593759268340625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22490796035458345691120833 16868097026593759268340625)
            ·
              refine ⟨12651072769945319451255469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16868097026593759268340625 12651072769945319451255469)
              ·
                refine ⟨4744152288729494794220801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12651072769945319451255469 4744152288729494794220801)
                ·
                  refine ⟨3558114216547121095665601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744152288729494794220801 3558114216547121095665601)
                  ·
                    refine ⟨2668585662410340821749201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558114216547121095665601 2668585662410340821749201)
                    ·
                      refine ⟨2001439246807755616311901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668585662410340821749201 2001439246807755616311901)
                      ·
                        rfl

theorem cell23_3897789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3897789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897789 prefixEnd_3897789 := by exact prefixLift 3897789
  have htrace : WordTrace (prefixWord ++ tailWord_3897789) baseStart_3897789 baseEnd_3897789 := by
    simpa [prefixWord, tailWord_3897789, baseEnd_3897789] using wordTrace_append hprefix tailTrace_3897789
  have hstable : (prefixWord ++ tailWord_3897789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897789).length < 2 ^ (prefixWord ++ tailWord_3897789).sum := by decide
  have hdescent : baseEnd_3897789 < baseStart_3897789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897810 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3897810 : Nat := 118140960795 + 3897810 * 2 ^ 59
def prefixEnd_3897810 : Nat := 4983230072969 + 3 ^ 40 * 3897810 * 2
def baseEnd_3897810 : Nat := 2001450029901500034149305

theorem tailTrace_3897810 : CollatzResearch.WordTrace tailWord_3897810 prefixEnd_3897810 2001450029901500034149305 := by
  unfold tailWord_3897810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541202502226884448646721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94776540005938358529724589 35541202502226884448646721)
  ·
    refine ⟨26655901876670163336485041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35541202502226884448646721 26655901876670163336485041)
    ·
      refine ⟨19991926407502622502363781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26655901876670163336485041 19991926407502622502363781)
      ·
        refine ⟨3748486201406741719193209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19991926407502622502363781 3748486201406741719193209)
        ·
          refine ⟨2811364651055056289394907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3748486201406741719193209 2811364651055056289394907)
          ·
            refine ⟨4217046976582584434092361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811364651055056289394907 4217046976582584434092361)
            ·
              refine ⟨3162785232436938325569271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217046976582584434092361 3162785232436938325569271)
              ·
                refine ⟨4744177848655407488353907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162785232436938325569271 4744177848655407488353907)
                ·
                  refine ⟨7116266772983111232530861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744177848655407488353907 7116266772983111232530861)
                  ·
                    refine ⟨2668600039868666712199073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7116266772983111232530861 2668600039868666712199073)
                    ·
                      refine ⟨2001450029901500034149305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668600039868666712199073 2001450029901500034149305)
                      ·
                        rfl

theorem cell23_3897810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3897810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897810 prefixEnd_3897810 := by exact prefixLift 3897810
  have htrace : WordTrace (prefixWord ++ tailWord_3897810) baseStart_3897810 baseEnd_3897810 := by
    simpa [prefixWord, tailWord_3897810, baseEnd_3897810] using wordTrace_append hprefix tailTrace_3897810
  have hstable : (prefixWord ++ tailWord_3897810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897810).length < 2 ^ (prefixWord ++ tailWord_3897810).sum := by decide
  have hdescent : baseEnd_3897810 < baseStart_3897810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897812 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 5]
def baseStart_3897812 : Nat := 118140960795 + 3897812 * 2 ^ 59
def prefixEnd_3897812 : Nat := 4983230072969 + 3 ^ 40 * 3897812 * 2
def baseEnd_3897812 : Nat := 222383450762534336258255

theorem tailTrace_3897812 : CollatzResearch.WordTrace tailWord_3897812 prefixEnd_3897812 222383450762534336258255 := by
  unfold tailWord_3897812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71082441477450146068079845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94776588636600194757439793 71082441477450146068079845)
  ·
    refine ⟨13327957777021902387764971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71082441477450146068079845 13327957777021902387764971)
    ·
      refine ⟨19991936665532853581647457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13327957777021902387764971 19991936665532853581647457)
      ·
        refine ⟨14993952499149640186235593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19991936665532853581647457 14993952499149640186235593)
        ·
          refine ⟨11245464374362230139676695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14993952499149640186235593 11245464374362230139676695)
          ·
            refine ⟨16868196561543345209515043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11245464374362230139676695 16868196561543345209515043)
            ·
              refine ⟨25302294842315017814272565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16868196561543345209515043 25302294842315017814272565)
              ·
                refine ⟨2372090141467032920088053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25302294842315017814272565 2372090141467032920088053)
                ·
                  refine ⟨222383450762534336258255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2372090141467032920088053 222383450762534336258255)
                  ·
                    rfl

theorem cell23_3897812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_3897812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897812 prefixEnd_3897812 := by exact prefixLift 3897812
  have htrace : WordTrace (prefixWord ++ tailWord_3897812) baseStart_3897812 baseEnd_3897812 := by
    simpa [prefixWord, tailWord_3897812, baseEnd_3897812] using wordTrace_append hprefix tailTrace_3897812
  have hstable : (prefixWord ++ tailWord_3897812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897812).length < 2 ^ (prefixWord ++ tailWord_3897812).sum := by decide
  have hdescent : baseEnd_3897812 < baseStart_3897812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897855 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 3, 4]
def baseStart_3897855 : Nat := 118140960795 + 3897855 * 2 ^ 59
def prefixEnd_3897855 : Nat := 4983230072969 + 3 ^ 40 * 3897855 * 2
def baseEnd_3897855 : Nat := 667157712176984119362199

theorem tailTrace_3897855 : CollatzResearch.WordTrace tailWord_3897855 prefixEnd_3897855 667157712176984119362199 := by
  unfold tailWord_3897855
  simp only [CollatzResearch.WordTrace]
  refine ⟨142166451293744510479975019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94777634195829673653316679 142166451293744510479975019)
  ·
    refine ⟨213249676940616765719962529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142166451293744510479975019 213249676940616765719962529)
    ·
      refine ⟨159937257705462574289971897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213249676940616765719962529 159937257705462574289971897)
      ·
        refine ⟨119952943279096930717478923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159937257705462574289971897 119952943279096930717478923)
        ·
          refine ⟨179929414918645396076218385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119952943279096930717478923 179929414918645396076218385)
          ·
            refine ⟨134947061188984047057163789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179929414918645396076218385 134947061188984047057163789)
            ·
              refine ⟨50605147945869017646436421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134947061188984047057163789 50605147945869017646436421)
              ·
                refine ⟨9488465239850440808706829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50605147945869017646436421 9488465239850440808706829)
                ·
                  refine ⟨3558174464943915303265061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9488465239850440808706829 3558174464943915303265061)
                  ·
                    refine ⟨667157712176984119362199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3558174464943915303265061 667157712176984119362199)
                    ·
                      rfl

theorem cell23_3897855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_3897855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897855 prefixEnd_3897855 := by exact prefixLift 3897855
  have htrace : WordTrace (prefixWord ++ tailWord_3897855) baseStart_3897855 baseEnd_3897855 := by
    simpa [prefixWord, tailWord_3897855, baseEnd_3897855] using wordTrace_append hprefix tailTrace_3897855
  have hstable : (prefixWord ++ tailWord_3897855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897855).length < 2 ^ (prefixWord ++ tailWord_3897855).sum := by decide
  have hdescent : baseEnd_3897855 < baseStart_3897855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897879 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3897879 : Nat := 118140960795 + 3897879 * 2 ^ 59
def prefixEnd_3897879 : Nat := 4983230072969 + 3 ^ 40 * 3897879 * 2
def baseEnd_3897879 : Nat := 2001485460066660264186487

theorem tailTrace_3897879 : CollatzResearch.WordTrace tailWord_3897879 prefixEnd_3897879 2001485460066660264186487 := by
  unfold tailWord_3897879
  simp only [CollatzResearch.WordTrace]
  refine ⟨142167326645657562578848691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94778217763771708385899127 142167326645657562578848691)
  ·
    refine ⟨213250989968486343868273037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142167326645657562578848691 213250989968486343868273037)
    ·
      refine ⟨79969121238182378950602389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213250989968486343868273037 79969121238182378950602389)
      ·
        refine ⟨3748552558039799013309487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79969121238182378950602389 3748552558039799013309487)
        ·
          refine ⟨5622828837059698519964231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748552558039799013309487 5622828837059698519964231)
          ·
            refine ⟨8434243255589547779946347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622828837059698519964231 8434243255589547779946347)
            ·
              refine ⟨12651364883384321669919521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434243255589547779946347 12651364883384321669919521)
              ·
                refine ⟨9488523662538241252439641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12651364883384321669919521 9488523662538241252439641)
                ·
                  refine ⟨7116392746903680939329731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9488523662538241252439641 7116392746903680939329731)
                  ·
                    refine ⟨10674589120355521408994597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7116392746903680939329731 10674589120355521408994597)
                    ·
                      refine ⟨2001485460066660264186487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10674589120355521408994597 2001485460066660264186487)
                      ·
                        rfl

theorem cell23_3897879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3897879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897879 prefixEnd_3897879 := by exact prefixLift 3897879
  have htrace : WordTrace (prefixWord ++ tailWord_3897879) baseStart_3897879 baseEnd_3897879 := by
    simpa [prefixWord, tailWord_3897879, baseEnd_3897879] using wordTrace_append hprefix tailTrace_3897879
  have hstable : (prefixWord ++ tailWord_3897879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897879).length < 2 ^ (prefixWord ++ tailWord_3897879).sum := by decide
  have hdescent : baseEnd_3897879 < baseStart_3897879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897885 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 8]
def baseStart_3897885 : Nat := 118140960795 + 3897885 * 2 ^ 59
def prefixEnd_3897885 : Nat := 4983230072969 + 3 ^ 40 * 3897885 * 2
def baseEnd_3897885 : Nat := 222387615661176360079051

theorem tailTrace_3897885 : CollatzResearch.WordTrace tailWord_3897885 prefixEnd_3897885 222387615661176360079051 := by
  unfold tailWord_3897885
  simp only [CollatzResearch.WordTrace]
  refine ⟨142167545483635825603567109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94778363655757217069044739 142167545483635825603567109)
  ·
    refine ⟨26656414778181717300668833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142167545483635825603567109 26656414778181717300668833)
    ·
      refine ⟨19992311083636287975501625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26656414778181717300668833 19992311083636287975501625)
      ·
        refine ⟨14994233312727215981626219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19992311083636287975501625 14994233312727215981626219)
        ·
          refine ⟨22491349969090823972439329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994233312727215981626219 22491349969090823972439329)
          ·
            refine ⟨16868512476818117979329497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22491349969090823972439329 16868512476818117979329497)
            ·
              refine ⟨12651384357613588484497123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16868512476818117979329497 12651384357613588484497123)
              ·
                refine ⟨18977076536420382726745685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12651384357613588484497123 18977076536420382726745685)
                ·
                  refine ⟨222387615661176360079051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18977076536420382726745685 222387615661176360079051)
                  ·
                    rfl

theorem cell23_3897885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_3897885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897885 prefixEnd_3897885 := by exact prefixLift 3897885
  have htrace : WordTrace (prefixWord ++ tailWord_3897885) baseStart_3897885 baseEnd_3897885 := by
    simpa [prefixWord, tailWord_3897885, baseEnd_3897885] using wordTrace_append hprefix tailTrace_3897885
  have hstable : (prefixWord ++ tailWord_3897885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897885).length < 2 ^ (prefixWord ++ tailWord_3897885).sum := by decide
  have hdescent : baseEnd_3897885 < baseStart_3897885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897912 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_3897912 : Nat := 118140960795 + 3897912 * 2 ^ 59
def prefixEnd_3897912 : Nat := 4983230072969 + 3 ^ 40 * 3897912 * 2
def baseEnd_3897912 : Nat := 2001502404928258635073835

theorem tailTrace_3897912 : CollatzResearch.WordTrace tailWord_3897912 prefixEnd_3897912 2001502404928258635073835 := by
  unfold tailWord_3897912
  simp only [CollatzResearch.WordTrace]
  refine ⟨71084265127269004607399995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94779020169692006143199993 71084265127269004607399995)
  ·
    refine ⟨106626397690903506911099993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71084265127269004607399995 106626397690903506911099993)
    ·
      refine ⟨79969798268177630183324995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106626397690903506911099993 79969798268177630183324995)
      ·
        refine ⟨119954697402266445274987493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79969798268177630183324995 119954697402266445274987493)
        ·
          refine ⟨22491505762924958489060155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119954697402266445274987493 22491505762924958489060155)
          ·
            refine ⟨33737258644387437733590233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22491505762924958489060155 33737258644387437733590233)
            ·
              refine ⟨25302943983290578300192675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33737258644387437733590233 25302943983290578300192675)
              ·
                refine ⟨37954415974935867450289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25302943983290578300192675 37954415974935867450289013)
                ·
                  refine ⟨3558226497650237573464595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37954415974935867450289013 3558226497650237573464595)
                  ·
                    refine ⟨5337339746475356360196893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558226497650237573464595 5337339746475356360196893)
                    ·
                      refine ⟨2001502404928258635073835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337339746475356360196893 2001502404928258635073835)
                      ·
                        rfl

theorem cell23_3897912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_3897912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897912 prefixEnd_3897912 := by exact prefixLift 3897912
  have htrace : WordTrace (prefixWord ++ tailWord_3897912) baseStart_3897912 baseEnd_3897912 := by
    simpa [prefixWord, tailWord_3897912, baseEnd_3897912] using wordTrace_append hprefix tailTrace_3897912
  have hstable : (prefixWord ++ tailWord_3897912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897912).length < 2 ^ (prefixWord ++ tailWord_3897912).sum := by decide
  have hdescent : baseEnd_3897912 < baseStart_3897912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897955 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3897955 : Nat := 118140960795 + 3897955 * 2 ^ 59
def prefixEnd_3897955 : Nat := 4983230072969 + 3 ^ 40 * 3897955 * 2
def baseEnd_3897955 : Nat := 2001524484596401966836137

theorem tailTrace_3897955 : CollatzResearch.WordTrace tailWord_3897955 prefixEnd_3897955 2001524484596401966836137 := by
  unfold tailWord_3897955
  simp only [CollatzResearch.WordTrace]
  refine ⟨142170098593382227558615319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94780065728921485039076879 142170098593382227558615319)
  ·
    refine ⟨213255147890073341337922979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142170098593382227558615319 213255147890073341337922979)
    ·
      refine ⟨319882721835110012006884469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213255147890073341337922979 319882721835110012006884469)
      ·
        refine ⟨29989005172041563625645419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319882721835110012006884469 29989005172041563625645419)
        ·
          refine ⟨44983507758062345438468129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29989005172041563625645419 44983507758062345438468129)
          ·
            refine ⟨33737630818546759078851097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44983507758062345438468129 33737630818546759078851097)
            ·
              refine ⟨25303223113910069309138323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33737630818546759078851097 25303223113910069309138323)
              ·
                refine ⟨37954834670865103963707485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25303223113910069309138323 37954834670865103963707485)
                ·
                  refine ⟨14233063001574413986390307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37954834670865103963707485 14233063001574413986390307)
                  ·
                    refine ⟨21349594502361620979585461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14233063001574413986390307 21349594502361620979585461)
                    ·
                      refine ⟨2001524484596401966836137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21349594502361620979585461 2001524484596401966836137)
                      ·
                        rfl

theorem cell23_3897955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3897955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897955 prefixEnd_3897955 := by exact prefixLift 3897955
  have htrace : WordTrace (prefixWord ++ tailWord_3897955) baseStart_3897955 baseEnd_3897955 := by
    simpa [prefixWord, tailWord_3897955, baseEnd_3897955] using wordTrace_append hprefix tailTrace_3897955
  have hstable : (prefixWord ++ tailWord_3897955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897955).length < 2 ^ (prefixWord ++ tailWord_3897955).sum := by decide
  have hdescent : baseEnd_3897955 < baseStart_3897955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897962 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_3897962 : Nat := 118140960795 + 3897962 * 2 ^ 59
def prefixEnd_3897962 : Nat := 4983230072969 + 3 ^ 40 * 3897962 * 2
def baseEnd_3897962 : Nat := 667176026320327813149535

theorem tailTrace_3897962 : CollatzResearch.WordTrace tailWord_3897962 prefixEnd_3897962 667176026320327813149535 := by
  unfold tailWord_3897962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35542588476089216938530035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94780235936237911836080093 35542588476089216938530035)
  ·
    refine ⟨53313882714133825407795053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35542588476089216938530035 53313882714133825407795053)
    ·
      refine ⟨19992706017800184527923145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53313882714133825407795053 19992706017800184527923145)
      ·
        refine ⟨14994529513350138395942359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19992706017800184527923145 14994529513350138395942359)
        ·
          refine ⟨22491794270025207593913539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994529513350138395942359 22491794270025207593913539)
          ·
            refine ⟨33737691405037811390870309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22491794270025207593913539 33737691405037811390870309)
            ·
              refine ⟨6325817138444589635788183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33737691405037811390870309 6325817138444589635788183)
              ·
                refine ⟨9488725707666884453682275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325817138444589635788183 9488725707666884453682275)
                ·
                  refine ⟨14233088561500326680523413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488725707666884453682275 14233088561500326680523413)
                  ·
                    refine ⟨667176026320327813149535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14233088561500326680523413 667176026320327813149535)
                    ·
                      rfl

theorem cell23_3897962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_3897962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897962 prefixEnd_3897962 := by exact prefixLift 3897962
  have htrace : WordTrace (prefixWord ++ tailWord_3897962) baseStart_3897962 baseEnd_3897962 := by
    simpa [prefixWord, tailWord_3897962, baseEnd_3897962] using wordTrace_append hprefix tailTrace_3897962
  have hstable : (prefixWord ++ tailWord_3897962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897962).length < 2 ^ (prefixWord ++ tailWord_3897962).sum := by decide
  have hdescent : baseEnd_3897962 < baseStart_3897962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897973 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3897973 : Nat := 118140960795 + 3897973 * 2 ^ 59
def prefixEnd_3897973 : Nat := 4983230072969 + 3 ^ 40 * 3897973 * 2
def baseEnd_3897973 : Nat := 2001533727248182896411055

theorem tailTrace_3897973 : CollatzResearch.WordTrace tailWord_3897973 prefixEnd_3897973 2001533727248182896411055 := by
  unfold tailWord_3897973
  simp only [CollatzResearch.WordTrace]
  refine ⟨142170755107317016632770573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94780503404878011088513715 142170755107317016632770573)
  ·
    refine ⟨53314033165243881237288965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142170755107317016632770573 53314033165243881237288965)
    ·
      refine ⟨9996381218483227731991681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53314033165243881237288965 9996381218483227731991681)
      ·
        refine ⟨7497285913862420798993761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9996381218483227731991681 7497285913862420798993761)
        ·
          refine ⟨5622964435396815599245321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497285913862420798993761 5622964435396815599245321)
          ·
            refine ⟨4217223326547611699433991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5622964435396815599245321 4217223326547611699433991)
            ·
              refine ⟨6325834989821417549150987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217223326547611699433991 6325834989821417549150987)
              ·
                refine ⟨9488752484732126323726481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325834989821417549150987 9488752484732126323726481)
                ·
                  refine ⟨7116564363549094742794861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9488752484732126323726481 7116564363549094742794861)
                  ·
                    refine ⟨2668711636330910528548073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7116564363549094742794861 2668711636330910528548073)
                    ·
                      refine ⟨2001533727248182896411055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668711636330910528548073 2001533727248182896411055)
                      ·
                        rfl

theorem cell23_3897973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3897973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897973 prefixEnd_3897973 := by exact prefixLift 3897973
  have htrace : WordTrace (prefixWord ++ tailWord_3897973) baseStart_3897973 baseEnd_3897973 := by
    simpa [prefixWord, tailWord_3897973, baseEnd_3897973] using wordTrace_append hprefix tailTrace_3897973
  have hstable : (prefixWord ++ tailWord_3897973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897973).length < 2 ^ (prefixWord ++ tailWord_3897973).sum := by decide
  have hdescent : baseEnd_3897973 < baseStart_3897973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3897989 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_3897989 : Nat := 118140960795 + 3897989 * 2 ^ 59
def prefixEnd_3897989 : Nat := 4983230072969 + 3 ^ 40 * 3897989 * 2
def baseEnd_3897989 : Nat := 2001541942938654833810981

theorem tailTrace_3897989 : CollatzResearch.WordTrace tailWord_3897989 prefixEnd_3897989 2001541942938654833810981 := by
  unfold tailWord_3897989
  simp only [CollatzResearch.WordTrace]
  refine ⟨142171338675259051365353021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94780892450172700910235347 142171338675259051365353021)
  ·
    refine ⟨53314252003222144262007383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142171338675259051365353021 53314252003222144262007383)
    ·
      refine ⟨79971378004833216393011075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53314252003222144262007383 79971378004833216393011075)
      ·
        refine ⟨119957067007249824589516613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79971378004833216393011075 119957067007249824589516613)
        ·
          refine ⟨22491950063859342110534365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119957067007249824589516613 22491950063859342110534365)
          ·
            refine ⟨8434481273947253291450387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22491950063859342110534365 8434481273947253291450387)
            ·
              refine ⟨12651721910920879937175581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8434481273947253291450387 12651721910920879937175581)
              ·
                refine ⟨4744395716595329976440843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12651721910920879937175581 4744395716595329976440843)
                ·
                  refine ⟨7116593574892994964661265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744395716595329976440843 7116593574892994964661265)
                  ·
                    refine ⟨5337445181169746223495949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7116593574892994964661265 5337445181169746223495949)
                    ·
                      refine ⟨2001541942938654833810981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337445181169746223495949 2001541942938654833810981)
                      ·
                        rfl

theorem cell23_3897989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_3897989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3897989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3897989 prefixEnd_3897989 := by exact prefixLift 3897989
  have htrace : WordTrace (prefixWord ++ tailWord_3897989) baseStart_3897989 baseEnd_3897989 := by
    simpa [prefixWord, tailWord_3897989, baseEnd_3897989] using wordTrace_append hprefix tailTrace_3897989
  have hstable : (prefixWord ++ tailWord_3897989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3897989).length < 2 ^ (prefixWord ++ tailWord_3897989).sum := by decide
  have hdescent : baseEnd_3897989 < baseStart_3897989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3897989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898016 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4]
def baseStart_3898016 : Nat := 118140960795 + 3898016 * 2 ^ 59
def prefixEnd_3898016 : Nat := 4983230072969 + 3 ^ 40 * 3898016 * 2
def baseEnd_3898016 : Nat := 2001555806916326228173357

theorem tailTrace_3898016 : CollatzResearch.WordTrace tailWord_3898016 prefixEnd_3898016 2001555806916326228173357 := by
  unfold tailWord_3898016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71086161723080617488292951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94781548964107489984390601 71086161723080617488292951)
  ·
    refine ⟨106629242584620926232439427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71086161723080617488292951 106629242584620926232439427)
    ·
      refine ⟨159943863876931389348659141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106629242584620926232439427 159943863876931389348659141)
      ·
        refine ⟨29989474476924635502873589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159943863876931389348659141 29989474476924635502873589)
        ·
          refine ⟨2811513232211684578394399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29989474476924635502873589 2811513232211684578394399)
          ·
            refine ⟨4217269848317526867591599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811513232211684578394399 4217269848317526867591599)
            ·
              refine ⟨6325904772476290301387399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217269848317526867591599 6325904772476290301387399)
              ·
                refine ⟨9488857158714435452081099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325904772476290301387399 9488857158714435452081099)
                ·
                  refine ⟨14233285738071653178121649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9488857158714435452081099 14233285738071653178121649)
                  ·
                    refine ⟨10674964303553739883591237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14233285738071653178121649 10674964303553739883591237)
                    ·
                      refine ⟨2001555806916326228173357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10674964303553739883591237 2001555806916326228173357)
                      ·
                        rfl

theorem cell23_3898016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_3898016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898016 prefixEnd_3898016 := by exact prefixLift 3898016
  have htrace : WordTrace (prefixWord ++ tailWord_3898016) baseStart_3898016 baseEnd_3898016 := by
    simpa [prefixWord, tailWord_3898016, baseEnd_3898016] using wordTrace_append hprefix tailTrace_3898016
  have hstable : (prefixWord ++ tailWord_3898016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898016).length < 2 ^ (prefixWord ++ tailWord_3898016).sum := by decide
  have hdescent : baseEnd_3898016 < baseStart_3898016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898023 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3898023 : Nat := 118140960795 + 3898023 * 2 ^ 59
def prefixEnd_3898023 : Nat := 4983230072969 + 3 ^ 40 * 3898023 * 2
def baseEnd_3898023 : Nat := 2001559401280907700785825

theorem tailTrace_3898023 : CollatzResearch.WordTrace tailWord_3898023 prefixEnd_3898023 2001559401280907700785825 := by
  unfold tailWord_3898023
  simp only [CollatzResearch.WordTrace]
  refine ⟨142172578757135875172090723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94781719171423916781393815 142172578757135875172090723)
  ·
    refine ⟨213258868135703812758136085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142172578757135875172090723 213258868135703812758136085)
    ·
      refine ⟨9996509443861116223037629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213258868135703812758136085 9996509443861116223037629)
      ·
        refine ⟨3748691041447918583639111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9996509443861116223037629 3748691041447918583639111)
        ·
          refine ⟨5623036562171877875458667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748691041447918583639111 5623036562171877875458667)
          ·
            refine ⟨8434554843257816813188001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623036562171877875458667 8434554843257816813188001)
            ·
              refine ⟨6325916132443362609891001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8434554843257816813188001 6325916132443362609891001)
              ·
                refine ⟨4744437099332521957418251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6325916132443362609891001 4744437099332521957418251)
                ·
                  refine ⟨7116655648998782936127377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744437099332521957418251 7116655648998782936127377)
                  ·
                    refine ⟨5337491736749087202095533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7116655648998782936127377 5337491736749087202095533)
                    ·
                      refine ⟨2001559401280907700785825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337491736749087202095533 2001559401280907700785825)
                      ·
                        rfl

theorem cell23_3898023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3898023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898023 prefixEnd_3898023 := by exact prefixLift 3898023
  have htrace : WordTrace (prefixWord ++ tailWord_3898023) baseStart_3898023 baseEnd_3898023 := by
    simpa [prefixWord, tailWord_3898023, baseEnd_3898023] using wordTrace_append hprefix tailTrace_3898023
  have hstable : (prefixWord ++ tailWord_3898023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898023).length < 2 ^ (prefixWord ++ tailWord_3898023).sum := by decide
  have hdescent : baseEnd_3898023 < baseStart_3898023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898025 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_3898025 : Nat := 118140960795 + 3898025 * 2 ^ 59
def prefixEnd_3898025 : Nat := 4983230072969 + 3 ^ 40 * 3898025 * 2
def baseEnd_3898025 : Nat := 2001560428242216692960815

theorem tailTrace_3898025 : CollatzResearch.WordTrace tailWord_3898025 prefixEnd_3898025 2001560428242216692960815 := by
  unfold tailWord_3898025
  simp only [CollatzResearch.WordTrace]
  refine ⟨142172651703128629513663529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94781767802085753009109019 142172651703128629513663529)
  ·
    refine ⟨106629488777346472135247647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142172651703128629513663529 106629488777346472135247647)
    ·
      refine ⟨159944233166019708202871471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106629488777346472135247647 159944233166019708202871471)
      ·
        refine ⟨239916349749029562304307207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159944233166019708202871471 239916349749029562304307207)
        ·
          refine ⟨359874524623544343456460811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239916349749029562304307207 359874524623544343456460811)
          ·
            refine ⟨539811786935316515184691217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359874524623544343456460811 539811786935316515184691217)
            ·
              refine ⟨404858840201487386388518413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539811786935316515184691217 404858840201487386388518413)
              ·
                refine ⟨151822065075557769895694405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404858840201487386388518413 151822065075557769895694405)
                ·
                  refine ⟨28466637201667081855442701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151822065075557769895694405 28466637201667081855442701)
                  ·
                    refine ⟨10674988950625155695791013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28466637201667081855442701 10674988950625155695791013)
                    ·
                      refine ⟨2001560428242216692960815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10674988950625155695791013 2001560428242216692960815)
                      ·
                        rfl

theorem cell23_3898025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_3898025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898025 prefixEnd_3898025 := by exact prefixLift 3898025
  have htrace : WordTrace (prefixWord ++ tailWord_3898025) baseStart_3898025 baseEnd_3898025 := by
    simpa [prefixWord, tailWord_3898025, baseEnd_3898025] using wordTrace_append hprefix tailTrace_3898025
  have hstable : (prefixWord ++ tailWord_3898025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898025).length < 2 ^ (prefixWord ++ tailWord_3898025).sum := by decide
  have hdescent : baseEnd_3898025 < baseStart_3898025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898046 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3898046 : Nat := 118140960795 + 3898046 * 2 ^ 59
def prefixEnd_3898046 : Nat := 4983230072969 + 3 ^ 40 * 3898046 * 2
def baseEnd_3898046 : Nat := 2001571211335961110798219

theorem tailTrace_3898046 : CollatzResearch.WordTrace tailWord_3898046 prefixEnd_3898046 2001571211335961110798219 := by
  unfold tailWord_3898046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17771677204506568762522249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94782278424035033400118661 17771677204506568762522249)
  ·
    refine ⟨13328757903379926571891687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17771677204506568762522249 13328757903379926571891687)
    ·
      refine ⟨19993136855069889857837531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328757903379926571891687 19993136855069889857837531)
      ·
        refine ⟨29989705282604834786756297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19993136855069889857837531 29989705282604834786756297)
        ·
          refine ⟨22492278961953626090067223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29989705282604834786756297 22492278961953626090067223)
          ·
            refine ⟨33738418442930439135100835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22492278961953626090067223 33738418442930439135100835)
            ·
              refine ⟨50607627664395658702651253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33738418442930439135100835 50607627664395658702651253)
              ·
                refine ⟨4744465093537093003373555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50607627664395658702651253 4744465093537093003373555)
                ·
                  refine ⟨7116697640305639505060333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744465093537093003373555 7116697640305639505060333)
                  ·
                    refine ⟨2668761615114614814397625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7116697640305639505060333 2668761615114614814397625)
                    ·
                      refine ⟨2001571211335961110798219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668761615114614814397625 2001571211335961110798219)
                      ·
                        rfl

theorem cell23_3898046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3898046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898046 prefixEnd_3898046 := by exact prefixLift 3898046
  have htrace : WordTrace (prefixWord ++ tailWord_3898046) baseStart_3898046 baseEnd_3898046 := by
    simpa [prefixWord, tailWord_3898046, baseEnd_3898046] using wordTrace_append hprefix tailTrace_3898046
  have hstable : (prefixWord ++ tailWord_3898046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898046).length < 2 ^ (prefixWord ++ tailWord_3898046).sum := by decide
  have hdescent : baseEnd_3898046 < baseStart_3898046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898054 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3898054 : Nat := 118140960795 + 3898054 * 2 ^ 59
def prefixEnd_3898054 : Nat := 4983230072969 + 3 ^ 40 * 3898054 * 2
def baseEnd_3898054 : Nat := 2001575319181197079498183

theorem tailTrace_3898054 : CollatzResearch.WordTrace tailWord_3898054 prefixEnd_3898054 2001575319181197079498183 := by
  unfold tailWord_3898054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4442928419375736483327163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94782472946682378310979477 4442928419375736483327163)
  ·
    refine ⟨6664392629063604724990745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4442928419375736483327163 6664392629063604724990745)
    ·
      refine ⟨4998294471797703543743059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6664392629063604724990745 4998294471797703543743059)
      ·
        refine ⟨7497441707696555315614589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998294471797703543743059 7497441707696555315614589)
        ·
          refine ⟨2811540640386208243355471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7497441707696555315614589 2811540640386208243355471)
          ·
            refine ⟨4217310960579312365033207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811540640386208243355471 4217310960579312365033207)
            ·
              refine ⟨6325966440868968547549811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217310960579312365033207 6325966440868968547549811)
              ·
                refine ⟨9488949661303452821324717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6325966440868968547549811 9488949661303452821324717)
                ·
                  refine ⟨3558356122988794807996769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9488949661303452821324717 3558356122988794807996769)
                  ·
                    refine ⟨2668767092241596105997577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558356122988794807996769 2668767092241596105997577)
                    ·
                      refine ⟨2001575319181197079498183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668767092241596105997577 2001575319181197079498183)
                      ·
                        rfl

theorem cell23_3898054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3898054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898054 prefixEnd_3898054 := by exact prefixLift 3898054
  have htrace : WordTrace (prefixWord ++ tailWord_3898054) baseStart_3898054 baseEnd_3898054 := by
    simpa [prefixWord, tailWord_3898054, baseEnd_3898054] using wordTrace_append hprefix tailTrace_3898054
  have hstable : (prefixWord ++ tailWord_3898054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898054).length < 2 ^ (prefixWord ++ tailWord_3898054).sum := by decide
  have hdescent : baseEnd_3898054 < baseStart_3898054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898055 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3898055 : Nat := 118140960795 + 3898055 * 2 ^ 59
def prefixEnd_3898055 : Nat := 4983230072969 + 3 ^ 40 * 3898055 * 2
def baseEnd_3898055 : Nat := 2001575832661851575585677

theorem tailTrace_3898055 : CollatzResearch.WordTrace tailWord_3898055 prefixEnd_3898055 2001575832661851575585677 := by
  unfold tailWord_3898055
  simp only [CollatzResearch.WordTrace]
  refine ⟨142173745893019944637255619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94782497262013296424837079 142173745893019944637255619)
  ·
    refine ⟨213260618839529916955883429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142173745893019944637255619 213260618839529916955883429)
    ·
      refine ⟨39986366032411859429228143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213260618839529916955883429 39986366032411859429228143)
      ·
        refine ⟨59979549048617789143842215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39986366032411859429228143 59979549048617789143842215)
        ·
          refine ⟨89969323572926683715763323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59979549048617789143842215 89969323572926683715763323)
          ·
            refine ⟨134953985359390025573644985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89969323572926683715763323 134953985359390025573644985)
            ·
              refine ⟨101215489019542519180233739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134953985359390025573644985 101215489019542519180233739)
              ·
                refine ⟨151823233529313778770350609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101215489019542519180233739 151823233529313778770350609)
                ·
                  refine ⟨113867425146985334077762957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151823233529313778770350609 113867425146985334077762957)
                  ·
                    refine ⟨42700284430119500279161109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113867425146985334077762957 42700284430119500279161109)
                    ·
                      refine ⟨2001575832661851575585677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42700284430119500279161109 2001575832661851575585677)
                      ·
                        rfl

theorem cell23_3898055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3898055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898055 prefixEnd_3898055 := by exact prefixLift 3898055
  have htrace : WordTrace (prefixWord ++ tailWord_3898055) baseStart_3898055 baseEnd_3898055 := by
    simpa [prefixWord, tailWord_3898055, baseEnd_3898055] using wordTrace_append hprefix tailTrace_3898055
  have hstable : (prefixWord ++ tailWord_3898055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898055).length < 2 ^ (prefixWord ++ tailWord_3898055).sum := by decide
  have hdescent : baseEnd_3898055 < baseStart_3898055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898092 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_3898092 : Nat := 118140960795 + 3898092 * 2 ^ 59
def prefixEnd_3898092 : Nat := 4983230072969 + 3 ^ 40 * 3898092 * 2
def baseEnd_3898092 : Nat := 2001594831446067930823007

theorem tailTrace_3898092 : CollatzResearch.WordTrace tailWord_3898092 prefixEnd_3898092 2001594831446067930823007 := by
  unfold tailWord_3898092
  simp only [CollatzResearch.WordTrace]
  refine ⟨71087547696942949978176265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94783396929257266637568353 71087547696942949978176265)
  ·
    refine ⟨53315660772707212483632199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71087547696942949978176265 53315660772707212483632199)
    ·
      refine ⟨79973491159060818725448299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53315660772707212483632199 79973491159060818725448299)
      ·
        refine ⟨119960236738591228088172449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79973491159060818725448299 119960236738591228088172449)
        ·
          refine ⟨89970177553943421066129337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119960236738591228088172449 89970177553943421066129337)
          ·
            refine ⟨67477633165457565799597003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89970177553943421066129337 67477633165457565799597003)
            ·
              refine ⟨101216449748186348699395505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67477633165457565799597003 101216449748186348699395505)
              ·
                refine ⟨75912337311139761524546629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101216449748186348699395505 75912337311139761524546629)
                ·
                  refine ⟨14233563245838705285852493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75912337311139761524546629 14233563245838705285852493)
                  ·
                    refine ⟨5337586217189514482194685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14233563245838705285852493 5337586217189514482194685)
                    ·
                      refine ⟨2001594831446067930823007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337586217189514482194685 2001594831446067930823007)
                      ·
                        rfl

theorem cell23_3898092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_3898092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898092 prefixEnd_3898092 := by exact prefixLift 3898092
  have htrace : WordTrace (prefixWord ++ tailWord_3898092) baseStart_3898092 baseEnd_3898092 := by
    simpa [prefixWord, tailWord_3898092, baseEnd_3898092] using wordTrace_append hprefix tailTrace_3898092
  have hstable : (prefixWord ++ tailWord_3898092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898092).length < 2 ^ (prefixWord ++ tailWord_3898092).sum := by decide
  have hdescent : baseEnd_3898092 < baseStart_3898092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898110 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3898110 : Nat := 118140960795 + 3898110 * 2 ^ 59
def prefixEnd_3898110 : Nat := 4983230072969 + 3 ^ 40 * 3898110 * 2
def baseEnd_3898110 : Nat := 2001604074097848860397925

theorem tailTrace_3898110 : CollatzResearch.WordTrace tailWord_3898110 prefixEnd_3898110 2001604074097848860397925 := by
  unfold tailWord_3898110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17771968988477586128813473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94783834605213792687005189 17771968988477586128813473)
  ·
    refine ⟨13328976741358189596610105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17771968988477586128813473 13328976741358189596610105)
    ·
      refine ⟨9996732556018642197457579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13328976741358189596610105 9996732556018642197457579)
      ·
        refine ⟨14995098834027963296186369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996732556018642197457579 14995098834027963296186369)
        ·
          refine ⟨11246324125520972472139777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14995098834027963296186369 11246324125520972472139777)
          ·
            refine ⟨8434743094140729354104833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11246324125520972472139777 8434743094140729354104833)
            ·
              refine ⟨6326057320605547015578625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8434743094140729354104833 6326057320605547015578625)
              ·
                refine ⟨4744542990454160261683969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326057320605547015578625 4744542990454160261683969)
                ·
                  refine ⟨3558407242840620196262977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4744542990454160261683969 3558407242840620196262977)
                  ·
                    refine ⟨2668805432130465147197233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558407242840620196262977 2668805432130465147197233)
                    ·
                      refine ⟨2001604074097848860397925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668805432130465147197233 2001604074097848860397925)
                      ·
                        rfl

theorem cell23_3898110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3898110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898110 prefixEnd_3898110 := by exact prefixLift 3898110
  have htrace : WordTrace (prefixWord ++ tailWord_3898110) baseStart_3898110 baseEnd_3898110 := by
    simpa [prefixWord, tailWord_3898110, baseEnd_3898110] using wordTrace_append hprefix tailTrace_3898110
  have hstable : (prefixWord ++ tailWord_3898110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898110).length < 2 ^ (prefixWord ++ tailWord_3898110).sum := by decide
  have hdescent : baseEnd_3898110 < baseStart_3898110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898122 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3898122 : Nat := 118140960795 + 3898122 * 2 ^ 59
def prefixEnd_3898122 : Nat := 4983230072969 + 3 ^ 40 * 3898122 * 2
def baseEnd_3898122 : Nat := 2001610235865702813447869

theorem tailTrace_3898122 : CollatzResearch.WordTrace tailWord_3898122 prefixEnd_3898122 2001610235865702813447869 := by
  unfold tailWord_3898122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35544047395944303769986155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94784126389184810053296413 35544047395944303769986155)
  ·
    refine ⟨53316071093916455654979233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35544047395944303769986155 53316071093916455654979233)
    ·
      refine ⟨39987053320437341741234425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53316071093916455654979233 39987053320437341741234425)
      ·
        refine ⟨29990289990328006305925819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39987053320437341741234425 29990289990328006305925819)
        ·
          refine ⟨44985434985492009458888729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29990289990328006305925819 44985434985492009458888729)
          ·
            refine ⟨33739076239119007094166547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44985434985492009458888729 33739076239119007094166547)
            ·
              refine ⟨50608614358678510641249821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33739076239119007094166547 50608614358678510641249821)
              ·
                refine ⟨18978230384504441490468683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50608614358678510641249821 18978230384504441490468683)
                ·
                  refine ⟨28467345576756662235703025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18978230384504441490468683 28467345576756662235703025)
                  ·
                    refine ⟨21350509182567496676777269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28467345576756662235703025 21350509182567496676777269)
                    ·
                      refine ⟨2001610235865702813447869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21350509182567496676777269 2001610235865702813447869)
                      ·
                        rfl

theorem cell23_3898122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3898122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898122 prefixEnd_3898122 := by exact prefixLift 3898122
  have htrace : WordTrace (prefixWord ++ tailWord_3898122) baseStart_3898122 baseEnd_3898122 := by
    simpa [prefixWord, tailWord_3898122, baseEnd_3898122] using wordTrace_append hprefix tailTrace_3898122
  have hstable : (prefixWord ++ tailWord_3898122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898122).length < 2 ^ (prefixWord ++ tailWord_3898122).sum := by decide
  have hdescent : baseEnd_3898122 < baseStart_3898122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898146 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3898146 : Nat := 118140960795 + 3898146 * 2 ^ 59
def prefixEnd_3898146 : Nat := 4983230072969 + 3 ^ 40 * 3898146 * 2
def baseEnd_3898146 : Nat := 667207519800470239849253

theorem tailTrace_3898146 : CollatzResearch.WordTrace tailWord_3898146 prefixEnd_3898146 667207519800470239849253 := by
  unfold tailWord_3898146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35544266233922566794704573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94784709957126844785878861 35544266233922566794704573)
  ·
    refine ⟨13329099837720962548014215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35544266233922566794704573 13329099837720962548014215)
    ·
      refine ⟨19993649756581443822021323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13329099837720962548014215 19993649756581443822021323)
      ·
        refine ⟨29990474634872165733031985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19993649756581443822021323 29990474634872165733031985)
        ·
          refine ⟨22492855976154124299773989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29990474634872165733031985 22492855976154124299773989)
          ·
            refine ⟨4217410495528898306207623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22492855976154124299773989 4217410495528898306207623)
            ·
              refine ⟨6326115743293347459311435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217410495528898306207623 6326115743293347459311435)
              ·
                refine ⟨9489173614940021188967153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326115743293347459311435 9489173614940021188967153)
                ·
                  refine ⟨7116880211205015891725365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9489173614940021188967153 7116880211205015891725365)
                  ·
                    refine ⟨667207519800470239849253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7116880211205015891725365 667207519800470239849253)
                    ·
                      rfl

theorem cell23_3898146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3898146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898146 prefixEnd_3898146 := by exact prefixLift 3898146
  have htrace : WordTrace (prefixWord ++ tailWord_3898146) baseStart_3898146 baseEnd_3898146 := by
    simpa [prefixWord, tailWord_3898146, baseEnd_3898146] using wordTrace_append hprefix tailTrace_3898146
  have hstable : (prefixWord ++ tailWord_3898146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898146).length < 2 ^ (prefixWord ++ tailWord_3898146).sum := by decide
  have hdescent : baseEnd_3898146 < baseStart_3898146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898149 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_3898149 : Nat := 118140960795 + 3898149 * 2 ^ 59
def prefixEnd_3898149 : Nat := 4983230072969 + 3 ^ 40 * 3898149 * 2
def baseEnd_3898149 : Nat := 2001624099843374207810245

theorem tailTrace_3898149 : CollatzResearch.WordTrace tailWord_3898149 prefixEnd_3898149 2001624099843374207810245 := by
  unfold tailWord_3898149
  simp only [CollatzResearch.WordTrace]
  refine ⟨142177174354679398691177501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94784782903119599127451667 142177174354679398691177501)
  ·
    refine ⟨53316440383004774509191563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142177174354679398691177501 53316440383004774509191563)
    ·
      refine ⟨79974660574507161763787345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53316440383004774509191563 79974660574507161763787345)
      ·
        refine ⟨59980995430880371322840509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79974660574507161763787345 59980995430880371322840509)
        ·
          refine ⟨22492873286580139246065191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59980995430880371322840509 22492873286580139246065191)
          ·
            refine ⟨33739309929870208869097787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22492873286580139246065191 33739309929870208869097787)
            ·
              refine ⟨50608964894805313303646681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33739309929870208869097787 50608964894805313303646681)
              ·
                refine ⟨37956723671103984977735011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50608964894805313303646681 37956723671103984977735011)
                ·
                  refine ⟨56935085506655977466602517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37956723671103984977735011 56935085506655977466602517)
                  ·
                    refine ⟨2668832133124498943746993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56935085506655977466602517 2668832133124498943746993)
                    ·
                      refine ⟨2001624099843374207810245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668832133124498943746993 2001624099843374207810245)
                      ·
                        rfl

theorem cell23_3898149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_3898149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898149 prefixEnd_3898149 := by exact prefixLift 3898149
  have htrace : WordTrace (prefixWord ++ tailWord_3898149) baseStart_3898149 baseEnd_3898149 := by
    simpa [prefixWord, tailWord_3898149, baseEnd_3898149] using wordTrace_append hprefix tailTrace_3898149
  have hstable : (prefixWord ++ tailWord_3898149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898149).length < 2 ^ (prefixWord ++ tailWord_3898149).sum := by decide
  have hdescent : baseEnd_3898149 < baseStart_3898149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898162 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3898162 : Nat := 118140960795 + 3898162 * 2 ^ 59
def prefixEnd_3898162 : Nat := 4983230072969 + 3 ^ 40 * 3898162 * 2
def baseEnd_3898162 : Nat := 2001630775091882656947685

theorem tailTrace_3898162 : CollatzResearch.WordTrace tailWord_3898162 prefixEnd_3898162 2001630775091882656947685 := by
  unfold tailWord_3898162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35544412125908075477850185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94785099002421534607600493 35544412125908075477850185)
  ·
    refine ⟨26658309094431056608387639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35544412125908075477850185 26658309094431056608387639)
    ·
      refine ⟨39987463641646584912581459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26658309094431056608387639 39987463641646584912581459)
      ·
        refine ⟨59981195462469877368872189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39987463641646584912581459 59981195462469877368872189)
        ·
          refine ⟨22492948298426204013327071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59981195462469877368872189 22492948298426204013327071)
          ·
            refine ⟨33739422447639306019990607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22492948298426204013327071 33739422447639306019990607)
            ·
              refine ⟨50609133671458959029985911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33739422447639306019990607 50609133671458959029985911)
              ·
                refine ⟨75913700507188438544978867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50609133671458959029985911 75913700507188438544978867)
                ·
                  refine ⟨113870550760782657817468301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75913700507188438544978867 113870550760782657817468301)
                  ·
                    refine ⟨42701456535293496681550613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113870550760782657817468301 42701456535293496681550613)
                    ·
                      refine ⟨2001630775091882656947685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42701456535293496681550613 2001630775091882656947685)
                      ·
                        rfl

theorem cell23_3898162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3898162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898162 prefixEnd_3898162 := by exact prefixLift 3898162
  have htrace : WordTrace (prefixWord ++ tailWord_3898162) baseStart_3898162 baseEnd_3898162 := by
    simpa [prefixWord, tailWord_3898162, baseEnd_3898162] using wordTrace_append hprefix tailTrace_3898162
  have hstable : (prefixWord ++ tailWord_3898162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898162).length < 2 ^ (prefixWord ++ tailWord_3898162).sum := by decide
  have hdescent : baseEnd_3898162 < baseStart_3898162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898219 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 1, 5]
def baseStart_3898219 : Nat := 118140960795 + 3898219 * 2 ^ 59
def prefixEnd_3898219 : Nat := 4983230072969 + 3 ^ 40 * 3898219 * 2
def baseEnd_3898219 : Nat := 667220014496396311311641

theorem tailTrace_3898219 : CollatzResearch.WordTrace tailWord_3898219 prefixEnd_3898219 667220014496396311311641 := by
  unfold tailWord_3898219
  simp only [CollatzResearch.WordTrace]
  refine ⟨142179727464425800646225711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94786484976283867097483807 142179727464425800646225711)
  ·
    refine ⟨213269591196638700969338567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142179727464425800646225711 213269591196638700969338567)
    ·
      refine ⟨319904386794958051454007851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213269591196638700969338567 319904386794958051454007851)
      ·
        refine ⟨479856580192437077181011777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319904386794958051454007851 479856580192437077181011777)
        ·
          refine ⟨359892435144327807885758833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479856580192437077181011777 359892435144327807885758833)
          ·
            refine ⟨269919326358245855914319125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359892435144327807885758833 269919326358245855914319125)
            ·
              refine ⟨12652468423042774495983709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269919326358245855914319125 12652468423042774495983709)
              ·
                refine ⟨4744675658641040435993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12652468423042774495983709 4744675658641040435993891)
                ·
                  refine ⟨7117013487961560653990837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4744675658641040435993891 7117013487961560653990837)
                  ·
                    refine ⟨667220014496396311311641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7117013487961560653990837 667220014496396311311641)
                    ·
                      rfl

theorem cell23_3898219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 5].length) (baseStart_3898219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898219 prefixEnd_3898219 := by exact prefixLift 3898219
  have htrace : WordTrace (prefixWord ++ tailWord_3898219) baseStart_3898219 baseEnd_3898219 := by
    simpa [prefixWord, tailWord_3898219, baseEnd_3898219] using wordTrace_append hprefix tailTrace_3898219
  have hstable : (prefixWord ++ tailWord_3898219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898219).length < 2 ^ (prefixWord ++ tailWord_3898219).sum := by decide
  have hdescent : baseEnd_3898219 < baseStart_3898219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898226 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_3898226 : Nat := 118140960795 + 3898226 * 2 ^ 59
def prefixEnd_3898226 : Nat := 4983230072969 + 3 ^ 40 * 3898226 * 2
def baseEnd_3898226 : Nat := 2001663637853770406547391

theorem tailTrace_3898226 : CollatzResearch.WordTrace tailWord_3898226 prefixEnd_3898226 2001663637853770406547391 := by
  unfold tailWord_3898226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35544995693850110210432633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94786655183600293894487021 35544995693850110210432633)
  ·
    refine ⟨26658746770387582657824475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35544995693850110210432633 26658746770387582657824475)
    ·
      refine ⟨39988120155581373986736713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26658746770387582657824475 39988120155581373986736713)
      ·
        refine ⟨29991090116686030490052535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39988120155581373986736713 29991090116686030490052535)
        ·
          refine ⟨44986635175029045735078803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29991090116686030490052535 44986635175029045735078803)
          ·
            refine ⟨67479952762543568602618205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44986635175029045735078803 67479952762543568602618205)
            ·
              refine ⟨25304982285953838225981827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67479952762543568602618205 25304982285953838225981827)
              ·
                refine ⟨37957473428930757338972741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25304982285953838225981827 37957473428930757338972741)
                ·
                  refine ⟨7117026267924517001057389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37957473428930757338972741 7117026267924517001057389)
                  ·
                    refine ⟨2668884850471693875396521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7117026267924517001057389 2668884850471693875396521)
                    ·
                      refine ⟨2001663637853770406547391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2668884850471693875396521 2001663637853770406547391)
                      ·
                        rfl

theorem cell23_3898226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_3898226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898226 prefixEnd_3898226 := by exact prefixLift 3898226
  have htrace : WordTrace (prefixWord ++ tailWord_3898226) baseStart_3898226 baseEnd_3898226 := by
    simpa [prefixWord, tailWord_3898226, baseEnd_3898226] using wordTrace_append hprefix tailTrace_3898226
  have hstable : (prefixWord ++ tailWord_3898226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898226).length < 2 ^ (prefixWord ++ tailWord_3898226).sum := by decide
  have hdescent : baseEnd_3898226 < baseStart_3898226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898232 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_3898232 : Nat := 118140960795 + 3898232 * 2 ^ 59
def prefixEnd_3898232 : Nat := 4983230072969 + 3 ^ 40 * 3898232 * 2
def baseEnd_3898232 : Nat := 667222239579232461024121

theorem tailTrace_3898232 : CollatzResearch.WordTrace tailWord_3898232 prefixEnd_3898232 667222239579232461024121 := by
  unfold tailWord_3898232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71090100806689351933224475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94786801075585802577632633 71090100806689351933224475)
  ·
    refine ⟨106635151210034027899836713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71090100806689351933224475 106635151210034027899836713)
    ·
      refine ⟨79976363407525520924877535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106635151210034027899836713 79976363407525520924877535)
      ·
        refine ⟨119964545111288281387316303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79976363407525520924877535 119964545111288281387316303)
        ·
          refine ⟨179946817666932422080974455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119964545111288281387316303 179946817666932422080974455)
          ·
            refine ⟨269920226500398633121461683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179946817666932422080974455 269920226500398633121461683)
            ·
              refine ⟨404880339750597949682192525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269920226500398633121461683 404880339750597949682192525)
              ·
                refine ⟨151830127406474231130822197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404880339750597949682192525 151830127406474231130822197)
                ·
                  refine ⟨14234074444356959168514581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151830127406474231130822197 14234074444356959168514581)
                  ·
                    refine ⟨667222239579232461024121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14234074444356959168514581 667222239579232461024121)
                    ·
                      rfl

theorem cell23_3898232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_3898232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898232 prefixEnd_3898232 := by exact prefixLift 3898232
  have htrace : WordTrace (prefixWord ++ tailWord_3898232) baseStart_3898232 baseEnd_3898232 := by
    simpa [prefixWord, tailWord_3898232, baseEnd_3898232] using wordTrace_append hprefix tailTrace_3898232
  have hstable : (prefixWord ++ tailWord_3898232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898232).length < 2 ^ (prefixWord ++ tailWord_3898232).sum := by decide
  have hdescent : baseEnd_3898232 < baseStart_3898232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898233 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3898233 : Nat := 118140960795 + 3898233 * 2 ^ 59
def prefixEnd_3898233 : Nat := 4983230072969 + 3 ^ 40 * 3898233 * 2
def baseEnd_3898233 : Nat := 2001667232218351879159859

theorem tailTrace_3898233 : CollatzResearch.WordTrace tailWord_3898233 prefixEnd_3898233 2001667232218351879159859 := by
  unfold tailWord_3898233
  simp only [CollatzResearch.WordTrace]
  refine ⟨142180238086375081037235353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94786825390916720691490235 142180238086375081037235353)
  ·
    refine ⟨106635178564781310777926515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142180238086375081037235353 106635178564781310777926515)
    ·
      refine ⟨159952767847171966166889773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106635178564781310777926515 159952767847171966166889773)
      ·
        refine ⟨59982287942689487312583665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159952767847171966166889773 59982287942689487312583665)
        ·
          refine ⟨44986715957017115484437749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59982287942689487312583665 44986715957017115484437749)
          ·
            refine ⟨4217504620970354576666039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44986715957017115484437749 4217504620970354576666039)
            ·
              refine ⟨6326256931455531864999059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217504620970354576666039 6326256931455531864999059)
              ·
                refine ⟨9489385397183297797498589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326256931455531864999059 9489385397183297797498589)
                ·
                  refine ⟨3558519523943736674061971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9489385397183297797498589 3558519523943736674061971)
                  ·
                    refine ⟨5337779285915605011092957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558519523943736674061971 5337779285915605011092957)
                    ·
                      refine ⟨2001667232218351879159859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337779285915605011092957 2001667232218351879159859)
                      ·
                        rfl

theorem cell23_3898233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3898233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898233 prefixEnd_3898233 := by exact prefixLift 3898233
  have htrace : WordTrace (prefixWord ++ tailWord_3898233) baseStart_3898233 baseEnd_3898233 := by
    simpa [prefixWord, tailWord_3898233, baseEnd_3898233] using wordTrace_append hprefix tailTrace_3898233
  have hstable : (prefixWord ++ tailWord_3898233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898233).length < 2 ^ (prefixWord ++ tailWord_3898233).sum := by decide
  have hdescent : baseEnd_3898233 < baseStart_3898233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898266 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_3898266 : Nat := 118140960795 + 3898266 * 2 ^ 59
def prefixEnd_3898266 : Nat := 4983230072969 + 3 ^ 40 * 3898266 * 2
def baseEnd_3898266 : Nat := 667228059026650083349069

theorem tailTrace_3898266 : CollatzResearch.WordTrace tailWord_3898266 prefixEnd_3898266 667228059026650083349069 := by
  unfold tailWord_3898266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545360423813881918296663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94787627796837018448791101 35545360423813881918296663)
  ·
    refine ⟨53318040635720822877444995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35545360423813881918296663 53318040635720822877444995)
    ·
      refine ⟨79977060953581234316167493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53318040635720822877444995 79977060953581234316167493)
      ·
        refine ⟨14995698928796481434281405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79977060953581234316167493 14995698928796481434281405)
        ·
          refine ⟨5623387098298680537855527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14995698928796481434281405 5623387098298680537855527)
          ·
            refine ⟨8435080647448020806783291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623387098298680537855527 8435080647448020806783291)
            ·
              refine ⟨12652620971172031210174937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435080647448020806783291 12652620971172031210174937)
              ·
                refine ⟨9489465728379023407631203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12652620971172031210174937 9489465728379023407631203)
                ·
                  refine ⟨14234198592568535111446805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9489465728379023407631203 14234198592568535111446805)
                  ·
                    refine ⟨667228059026650083349069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14234198592568535111446805 667228059026650083349069)
                    ·
                      rfl

theorem cell23_3898266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_3898266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898266 prefixEnd_3898266 := by exact prefixLift 3898266
  have htrace : WordTrace (prefixWord ++ tailWord_3898266) baseStart_3898266 baseEnd_3898266 := by
    simpa [prefixWord, tailWord_3898266, baseEnd_3898266] using wordTrace_append hprefix tailTrace_3898266
  have hstable : (prefixWord ++ tailWord_3898266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898266).length < 2 ^ (prefixWord ++ tailWord_3898266).sum := by decide
  have hdescent : baseEnd_3898266 < baseStart_3898266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898279 : List Nat := [1, 1, 6, 1, 3, 11]
def baseStart_3898279 : Nat := 118140960795 + 3898279 * 2 ^ 59
def prefixEnd_3898279 : Nat := 4983230072969 + 3 ^ 40 * 3898279 * 2
def baseEnd_3898279 : Nat := 8237410914931928803229

theorem tailTrace_3898279 : CollatzResearch.WordTrace tailWord_3898279 prefixEnd_3898279 8237410914931928803229 := by
  unfold tailWord_3898279
  simp only [CollatzResearch.WordTrace]
  refine ⟨142181915844208430893409891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94787943896138953928939927 142181915844208430893409891)
  ·
    refine ⟨213272873766312646340114837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142181915844208430893409891 213272873766312646340114837)
    ·
      refine ⟨9997165957795905297192883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213272873766312646340114837 9997165957795905297192883)
      ·
        refine ⟨14995748936693857945789325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9997165957795905297192883 14995748936693857945789325)
        ·
          refine ⟨5623405851260196729670997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14995748936693857945789325 5623405851260196729670997)
          ·
            refine ⟨8237410914931928803229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5623405851260196729670997 8237410914931928803229)
            ·
              rfl

theorem cell23_3898279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 11].length) (baseStart_3898279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898279 prefixEnd_3898279 := by exact prefixLift 3898279
  have htrace : WordTrace (prefixWord ++ tailWord_3898279) baseStart_3898279 baseEnd_3898279 := by
    simpa [prefixWord, tailWord_3898279, baseEnd_3898279] using wordTrace_append hprefix tailTrace_3898279
  have hstable : (prefixWord ++ tailWord_3898279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898279).length < 2 ^ (prefixWord ++ tailWord_3898279).sum := by decide
  have hdescent : baseEnd_3898279 < baseStart_3898279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898339 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 6]
def baseStart_3898339 : Nat := 118140960795 + 3898339 * 2 ^ 59
def prefixEnd_3898339 : Nat := 4983230072969 + 3 ^ 40 * 3898339 * 2
def baseEnd_3898339 : Nat := 667240553722576154811457

theorem tailTrace_3898339 : CollatzResearch.WordTrace tailWord_3898339 prefixEnd_3898339 667240553722576154811457 := by
  unfold tailWord_3898339
  simp only [CollatzResearch.WordTrace]
  refine ⟨142184104223991061140594071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94789402815994040760396047 142184104223991061140594071)
  ·
    refine ⟨213276156335986591710891107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142184104223991061140594071 213276156335986591710891107)
    ·
      refine ⟨319914234503979887566336661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213276156335986591710891107 319914234503979887566336661)
      ·
        refine ⟨14995979742374057229672031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319914234503979887566336661 14995979742374057229672031)
        ·
          refine ⟨22493969613561085844508047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14995979742374057229672031 22493969613561085844508047)
          ·
            refine ⟨33740954420341628766762071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22493969613561085844508047 33740954420341628766762071)
            ·
              refine ⟨50611431630512443150143107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33740954420341628766762071 50611431630512443150143107)
              ·
                refine ⟨75917147445768664725214661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50611431630512443150143107 75917147445768664725214661)
                ·
                  refine ⟨14234465146081624635977749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75917147445768664725214661 14234465146081624635977749)
                  ·
                    refine ⟨667240553722576154811457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14234465146081624635977749 667240553722576154811457)
                    ·
                      rfl

theorem cell23_3898339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_3898339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898339 prefixEnd_3898339 := by exact prefixLift 3898339
  have htrace : WordTrace (prefixWord ++ tailWord_3898339) baseStart_3898339 baseEnd_3898339 := by
    simpa [prefixWord, tailWord_3898339, baseEnd_3898339] using wordTrace_append hprefix tailTrace_3898339
  have hstable : (prefixWord ++ tailWord_3898339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898339).length < 2 ^ (prefixWord ++ tailWord_3898339).sum := by decide
  have hdescent : baseEnd_3898339 < baseStart_3898339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898357 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3898357 : Nat := 118140960795 + 3898357 * 2 ^ 59
def prefixEnd_3898357 : Nat := 4983230072969 + 3 ^ 40 * 3898357 * 2
def baseEnd_3898357 : Nat := 2001730903819509394009289

theorem tailTrace_3898357 : CollatzResearch.WordTrace tailWord_3898357 prefixEnd_3898357 2001730903819509394009289 := by
  unfold tailWord_3898357
  simp only [CollatzResearch.WordTrace]
  refine ⟨142184760737925850214749325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94789840491950566809832883 142184760737925850214749325)
  ·
    refine ⟨53319285276722193830530997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142184760737925850214749325 53319285276722193830530997)
    ·
      refine ⟨4998682994692705671612281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53319285276722193830530997 4998682994692705671612281)
      ·
        refine ⟨3749012246019529253709211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998682994692705671612281 3749012246019529253709211)
        ·
          refine ⟨5623518369029293880563817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749012246019529253709211 5623518369029293880563817)
          ·
            refine ⟨4217638776771970410422863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5623518369029293880563817 4217638776771970410422863)
            ·
              refine ⟨6326458165157955615634295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217638776771970410422863 6326458165157955615634295)
              ·
                refine ⟨9489687247736933423451443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326458165157955615634295 9489687247736933423451443)
                ·
                  refine ⟨14234530871605400135177165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9489687247736933423451443 14234530871605400135177165)
                  ·
                    refine ⟨5337949076852025050691437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14234530871605400135177165 5337949076852025050691437)
                    ·
                      refine ⟨2001730903819509394009289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5337949076852025050691437 2001730903819509394009289)
                      ·
                        rfl

theorem cell23_3898357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3898357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898357 prefixEnd_3898357 := by exact prefixLift 3898357
  have htrace : WordTrace (prefixWord ++ tailWord_3898357) baseStart_3898357 baseEnd_3898357 := by
    simpa [prefixWord, tailWord_3898357, baseEnd_3898357] using wordTrace_append hprefix tailTrace_3898357
  have hstable : (prefixWord ++ tailWord_3898357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898357).length < 2 ^ (prefixWord ++ tailWord_3898357).sum := by decide
  have hdescent : baseEnd_3898357 < baseStart_3898357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898453 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3898453 : Nat := 118140960795 + 3898453 * 2 ^ 59
def prefixEnd_3898453 : Nat := 4983230072969 + 3 ^ 40 * 3898453 * 2
def baseEnd_3898453 : Nat := 2001780197962341018408847

theorem tailTrace_3898453 : CollatzResearch.WordTrace tailWord_3898453 prefixEnd_3898453 2001780197962341018408847 := by
  unfold tailWord_3898453
  simp only [CollatzResearch.WordTrace]
  refine ⟨142188262145578058610244013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94792174763718705740162675 142188262145578058610244013)
  ·
    refine ⟨53320598304591771978841505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142188262145578058610244013 53320598304591771978841505)
    ·
      refine ⟨39990448728443828984131129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53320598304591771978841505 39990448728443828984131129)
      ·
        refine ⟨29992836546332871738098347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39990448728443828984131129 29992836546332871738098347)
        ·
          refine ⟨44989254819499307607147521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29992836546332871738098347 44989254819499307607147521)
          ·
            refine ⟨33741941114624480705360641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44989254819499307607147521 33741941114624480705360641)
            ·
              refine ⟨25306455835968360529020481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33741941114624480705360641 25306455835968360529020481)
              ·
                refine ⟨18979841876976270396765361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25306455835968360529020481 18979841876976270396765361)
                ·
                  refine ⟨14234881407732202797574021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18979841876976270396765361 14234881407732202797574021)
                  ·
                    refine ⟨2669040263949788024545129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14234881407732202797574021 2669040263949788024545129)
                    ·
                      refine ⟨2001780197962341018408847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669040263949788024545129 2001780197962341018408847)
                      ·
                        rfl

theorem cell23_3898453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3898453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898453 prefixEnd_3898453 := by exact prefixLift 3898453
  have htrace : WordTrace (prefixWord ++ tailWord_3898453) baseStart_3898453 baseEnd_3898453 := by
    simpa [prefixWord, tailWord_3898453, baseEnd_3898453] using wordTrace_append hprefix tailTrace_3898453
  have hstable : (prefixWord ++ tailWord_3898453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898453).length < 2 ^ (prefixWord ++ tailWord_3898453).sum := by decide
  have hdescent : baseEnd_3898453 < baseStart_3898453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898476 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 6]
def baseStart_3898476 : Nat := 118140960795 + 3898476 * 2 ^ 59
def prefixEnd_3898476 : Nat := 4983230072969 + 3 ^ 40 * 3898476 * 2
def baseEnd_3898476 : Nat := 222421334224154936491249

theorem tailTrace_3898476 : CollatzResearch.WordTrace tailWord_3898476 prefixEnd_3898476 222421334224154936491249 := by
  unfold tailWord_3898476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71094550512247366769165641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94792734016329822358887521 71094550512247366769165641)
  ·
    refine ⟨53320912884185525076874231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71094550512247366769165641 53320912884185525076874231)
    ·
      refine ⟨79981369326278287615311347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53320912884185525076874231 79981369326278287615311347)
      ·
        refine ⟨119972053989417431422967021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79981369326278287615311347 119972053989417431422967021)
        ·
          refine ⟨44989520246031536783612633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119972053989417431422967021 44989520246031536783612633)
          ·
            refine ⟨33742140184523652587709475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44989520246031536783612633 33742140184523652587709475)
            ·
              refine ⟨50613210276785478881564213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33742140184523652587709475 50613210276785478881564213)
              ·
                refine ⟨4744988463448638645146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50613210276785478881564213 4744988463448638645146645)
                ·
                  refine ⟨222421334224154936491249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4744988463448638645146645 222421334224154936491249)
                  ·
                    rfl

theorem cell23_3898476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_3898476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898476 prefixEnd_3898476 := by exact prefixLift 3898476
  have htrace : WordTrace (prefixWord ++ tailWord_3898476) baseStart_3898476 baseEnd_3898476 := by
    simpa [prefixWord, tailWord_3898476, baseEnd_3898476] using wordTrace_append hprefix tailTrace_3898476
  have hstable : (prefixWord ++ tailWord_3898476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898476).length < 2 ^ (prefixWord ++ tailWord_3898476).sum := by decide
  have hdescent : baseEnd_3898476 < baseStart_3898476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898497 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3898497 : Nat := 118140960795 + 3898497 * 2 ^ 59
def prefixEnd_3898497 : Nat := 4983230072969 + 3 ^ 40 * 3898497 * 2
def baseEnd_3898497 : Nat := 667267597037046282086215

theorem tailTrace_3898497 : CollatzResearch.WordTrace tailWord_3898497 prefixEnd_3898497 667267597037046282086215 := by
  unfold tailWord_3898497
  simp only [CollatzResearch.WordTrace]
  refine ⟨142189866957418654124845745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94793244638279102749897163 142189866957418654124845745)
  ·
    refine ⟨106642400218063990593634309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142189866957418654124845745 106642400218063990593634309)
    ·
      refine ⟨19995450040886998236306433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106642400218063990593634309 19995450040886998236306433)
      ·
        refine ⟨14996587530665248677229825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19995450040886998236306433 14996587530665248677229825)
        ·
          refine ⟨11247440647998936507922369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14996587530665248677229825 11247440647998936507922369)
          ·
            refine ⟨8435580485999202380941777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11247440647998936507922369 8435580485999202380941777)
            ·
              refine ⟨6326685364499401785706333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435580485999202380941777 6326685364499401785706333)
              ·
                refine ⟨2372507011687275669639875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6326685364499401785706333 2372507011687275669639875)
                ·
                  refine ⟨3558760517530913504459813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372507011687275669639875 3558760517530913504459813)
                  ·
                    refine ⟨667267597037046282086215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3558760517530913504459813 667267597037046282086215)
                    ·
                      rfl

theorem cell23_3898497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3898497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898497 prefixEnd_3898497 := by exact prefixLift 3898497
  have htrace : WordTrace (prefixWord ++ tailWord_3898497) baseStart_3898497 baseEnd_3898497 := by
    simpa [prefixWord, tailWord_3898497, baseEnd_3898497] using wordTrace_append hprefix tailTrace_3898497
  have hstable : (prefixWord ++ tailWord_3898497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898497).length < 2 ^ (prefixWord ++ tailWord_3898497).sum := by decide
  have hdescent : baseEnd_3898497 < baseStart_3898497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898503 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3898503 : Nat := 118140960795 + 3898503 * 2 ^ 59
def prefixEnd_3898503 : Nat := 4983230072969 + 3 ^ 40 * 3898503 * 2
def baseEnd_3898503 : Nat := 2001805871995065822783617

theorem tailTrace_3898503 : CollatzResearch.WordTrace tailWord_3898503 prefixEnd_3898503 2001805871995065822783617 := by
  unfold tailWord_3898503
  simp only [CollatzResearch.WordTrace]
  refine ⟨142190085795396917149564163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94793390530264611433042775 142190085795396917149564163)
  ·
    refine ⟨213285128693095375724346245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142190085795396917149564163 213285128693095375724346245)
    ·
      refine ⟨39990961629955382948314921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213285128693095375724346245 39990961629955382948314921)
      ·
        refine ⟨29993221222466537211236191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39990961629955382948314921 29993221222466537211236191)
        ·
          refine ⟨44989831833699805816854287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29993221222466537211236191 44989831833699805816854287)
          ·
            refine ⟨67484747750549708725281431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44989831833699805816854287 67484747750549708725281431)
            ·
              refine ⟨101227121625824563087922147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67484747750549708725281431 101227121625824563087922147)
              ·
                refine ⟨151840682438736844631883221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101227121625824563087922147 151840682438736844631883221)
                ·
                  refine ⟨3558765994657894796059763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 151840682438736844631883221 3558765994657894796059763)
                  ·
                    refine ⟨5338148991986842194089645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558765994657894796059763 5338148991986842194089645)
                    ·
                      refine ⟨2001805871995065822783617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338148991986842194089645 2001805871995065822783617)
                      ·
                        rfl

theorem cell23_3898503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3898503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898503 prefixEnd_3898503 := by exact prefixLift 3898503
  have htrace : WordTrace (prefixWord ++ tailWord_3898503) baseStart_3898503 baseEnd_3898503 := by
    simpa [prefixWord, tailWord_3898503, baseEnd_3898503] using wordTrace_append hprefix tailTrace_3898503
  have hstable : (prefixWord ++ tailWord_3898503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898503).length < 2 ^ (prefixWord ++ tailWord_3898503).sum := by decide
  have hdescent : baseEnd_3898503 < baseStart_3898503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898510 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3898510 : Nat := 118140960795 + 3898510 * 2 ^ 59
def prefixEnd_3898510 : Nat := 4983230072969 + 3 ^ 40 * 3898510 * 2
def baseEnd_3898510 : Nat := 222423274039960810599565

theorem tailTrace_3898510 : CollatzResearch.WordTrace tailWord_3898510 prefixEnd_3898510 222423274039960810599565 := by
  unfold tailWord_3898510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773792638296444668133623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94793560737581038230045989 17773792638296444668133623)
  ·
    refine ⟨26660688957444667002200435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17773792638296444668133623 26660688957444667002200435)
    ·
      refine ⟨39991033436167000503300653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26660688957444667002200435 39991033436167000503300653)
      ·
        refine ⟨14996637538562625188737745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39991033436167000503300653 14996637538562625188737745)
        ·
          refine ⟨11247478153921968891553309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14996637538562625188737745 11247478153921968891553309)
          ·
            refine ⟨4217804307720738334332491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11247478153921968891553309 4217804307720738334332491)
            ·
              refine ⟨6326706461581107501498737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217804307720738334332491 6326706461581107501498737)
              ·
                refine ⟨4745029846185830626124053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326706461581107501498737 4745029846185830626124053)
                ·
                  refine ⟨222423274039960810599565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4745029846185830626124053 222423274039960810599565)
                  ·
                    rfl

theorem cell23_3898510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3898510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898510 prefixEnd_3898510 := by exact prefixLift 3898510
  have htrace : WordTrace (prefixWord ++ tailWord_3898510) baseStart_3898510 baseEnd_3898510 := by
    simpa [prefixWord, tailWord_3898510, baseEnd_3898510] using wordTrace_append hprefix tailTrace_3898510
  have hstable : (prefixWord ++ tailWord_3898510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898510).length < 2 ^ (prefixWord ++ tailWord_3898510).sum := by decide
  have hdescent : baseEnd_3898510 < baseStart_3898510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898520 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3898520 : Nat := 118140960795 + 3898520 * 2 ^ 59
def prefixEnd_3898520 : Nat := 4983230072969 + 3 ^ 40 * 3898520 * 2
def baseEnd_3898520 : Nat := 2001814601166192256271039

theorem tailTrace_3898520 : CollatzResearch.WordTrace tailWord_3898520 prefixEnd_3898520 2001814601166192256271039 := by
  unfold tailWord_3898520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71095352918167664526466507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94793803890890219368622009 71095352918167664526466507)
  ·
    refine ⟨106643029377251496789699761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71095352918167664526466507 106643029377251496789699761)
    ·
      refine ⟨79982272032938622592274821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106643029377251496789699761 79982272032938622592274821)
      ·
        refine ⟨14996676006175991736051529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79982272032938622592274821 14996676006175991736051529)
        ·
          refine ⟨11247507004631993802038647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14996676006175991736051529 11247507004631993802038647)
          ·
            refine ⟨16871260506947990703057971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11247507004631993802038647 16871260506947990703057971)
            ·
              refine ⟨25306890760421986054586957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16871260506947990703057971 25306890760421986054586957)
              ·
                refine ⟨9490084035158244770470109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25306890760421986054586957 9490084035158244770470109)
                ·
                  refine ⟨3558781513184341788926291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9490084035158244770470109 3558781513184341788926291)
                  ·
                    refine ⟨5338172269776512683389437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558781513184341788926291 5338172269776512683389437)
                    ·
                      refine ⟨2001814601166192256271039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338172269776512683389437 2001814601166192256271039)
                      ·
                        rfl

theorem cell23_3898520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3898520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898520 prefixEnd_3898520 := by exact prefixLift 3898520
  have htrace : WordTrace (prefixWord ++ tailWord_3898520) baseStart_3898520 baseEnd_3898520 := by
    simpa [prefixWord, tailWord_3898520, baseEnd_3898520] using wordTrace_append hprefix tailTrace_3898520
  have hstable : (prefixWord ++ tailWord_3898520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898520).length < 2 ^ (prefixWord ++ tailWord_3898520).sum := by decide
  have hdescent : baseEnd_3898520 < baseStart_3898520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898543 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_3898543 : Nat := 118140960795 + 3898543 * 2 ^ 59
def prefixEnd_3898543 : Nat := 4983230072969 + 3 ^ 40 * 3898543 * 2
def baseEnd_3898543 : Nat := 2001826411221245666283433

theorem tailTrace_3898543 : CollatzResearch.WordTrace tailWord_3898543 prefixEnd_3898543 2001826411221245666283433 := by
  unfold tailWord_3898543
  simp only [CollatzResearch.WordTrace]
  refine ⟨142191544715252003981020283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94794363143501335987346855 142191544715252003981020283)
  ·
    refine ⟨213287317072878005971530425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142191544715252003981020283 213287317072878005971530425)
    ·
      refine ⟨159965487804658504478647819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213287317072878005971530425 159965487804658504478647819)
      ·
        refine ⟨239948231706987756717971729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159965487804658504478647819 239948231706987756717971729)
        ·
          refine ⟨179961173780240817538478797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239948231706987756717971729 179961173780240817538478797)
          ·
            refine ⟨67485440167590306576929549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179961173780240817538478797 67485440167590306576929549)
            ·
              refine ⟨25307040062846364966348581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67485440167590306576929549 25307040062846364966348581)
              ·
                refine ⟨4745070011783693431190359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25307040062846364966348581 4745070011783693431190359)
                ·
                  refine ⟨7117605017675540146785539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745070011783693431190359 7117605017675540146785539)
                  ·
                    refine ⟨10676407526513310220178309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7117605017675540146785539 10676407526513310220178309)
                    ·
                      refine ⟨2001826411221245666283433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10676407526513310220178309 2001826411221245666283433)
                      ·
                        rfl

theorem cell23_3898543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_3898543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898543 prefixEnd_3898543 := by exact prefixLift 3898543
  have htrace : WordTrace (prefixWord ++ tailWord_3898543) baseStart_3898543 baseEnd_3898543 := by
    simpa [prefixWord, tailWord_3898543, baseEnd_3898543] using wordTrace_append hprefix tailTrace_3898543
  have hstable : (prefixWord ++ tailWord_3898543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898543).length < 2 ^ (prefixWord ++ tailWord_3898543).sum := by decide
  have hdescent : baseEnd_3898543 < baseStart_3898543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898553 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_3898553 : Nat := 118140960795 + 3898553 * 2 ^ 59
def prefixEnd_3898553 : Nat := 4983230072969 + 3 ^ 40 * 3898553 * 2
def baseEnd_3898553 : Nat := 667277182009263542386129

theorem tailTrace_3898553 : CollatzResearch.WordTrace tailWord_3898553 prefixEnd_3898553 667277182009263542386129 := by
  unfold tailWord_3898553
  simp only [CollatzResearch.WordTrace]
  refine ⟨142191909445215775688884313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94794606296810517125922875 142191909445215775688884313)
  ·
    refine ⟨106643932083911831766663235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142191909445215775688884313 106643932083911831766663235)
    ·
      refine ⟨159965898125867747649994853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106643932083911831766663235 159965898125867747649994853)
      ·
        refine ⟨29993605898600202684374035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159965898125867747649994853 29993605898600202684374035)
        ·
          refine ⟨44990408847900304026561053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29993605898600202684374035 44990408847900304026561053)
          ·
            refine ⟨16871403317962614009960395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44990408847900304026561053 16871403317962614009960395)
            ·
              refine ⟨25307104976943921014940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16871403317962614009960395 25307104976943921014940593)
              ·
                refine ⟨18980328732707940761205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25307104976943921014940593 18980328732707940761205445)
                ·
                  refine ⟨3558811637382738892726021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18980328732707940761205445 3558811637382738892726021)
                  ·
                    refine ⟨667277182009263542386129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3558811637382738892726021 667277182009263542386129)
                    ·
                      rfl

theorem cell23_3898553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_3898553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898553 prefixEnd_3898553 := by exact prefixLift 3898553
  have htrace : WordTrace (prefixWord ++ tailWord_3898553) baseStart_3898553 baseEnd_3898553 := by
    simpa [prefixWord, tailWord_3898553, baseEnd_3898553] using wordTrace_append hprefix tailTrace_3898553
  have hstable : (prefixWord ++ tailWord_3898553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898553).length < 2 ^ (prefixWord ++ tailWord_3898553).sum := by decide
  have hdescent : baseEnd_3898553 < baseStart_3898553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3898586 : Nat := 118140960795 + 3898586 * 2 ^ 59
def prefixEnd_3898586 : Nat := 4983230072969 + 3 ^ 40 * 3898586 * 2
def baseEnd_3898586 : Nat := 2001848490889388998045735

theorem tailTrace_3898586 : CollatzResearch.WordTrace tailWord_3898586 prefixEnd_3898586 2001848490889388998045735 := by
  unfold tailWord_3898586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35548278263524055581208903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94795408702730814883223741 35548278263524055581208903)
  ·
    refine ⟨53322417395286083371813355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35548278263524055581208903 53322417395286083371813355)
    ·
      refine ⟨79983626092929125057720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53322417395286083371813355 79983626092929125057720033)
      ·
        refine ⟨59987719569696843793290025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79983626092929125057720033 59987719569696843793290025)
        ·
          refine ⟨44990789677272632844967519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59987719569696843793290025 44990789677272632844967519)
          ·
            refine ⟨67486184515908949267451279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44990789677272632844967519 67486184515908949267451279)
            ·
              refine ⟨101229276773863423901176919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67486184515908949267451279 101229276773863423901176919)
              ·
                refine ⟨151843915160795135851765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101229276773863423901176919 151843915160795135851765379)
                ·
                  refine ⟨227765872741192703777648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151843915160795135851765379 227765872741192703777648069)
                  ·
                    refine ⟨42706101138973631958309013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227765872741192703777648069 42706101138973631958309013)
                    ·
                      refine ⟨2001848490889388998045735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42706101138973631958309013 2001848490889388998045735)
                      ·
                        rfl

theorem cell23_3898586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3898586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898586 prefixEnd_3898586 := by exact prefixLift 3898586
  have htrace : WordTrace (prefixWord ++ tailWord_3898586) baseStart_3898586 baseEnd_3898586 := by
    simpa [prefixWord, tailWord_3898586, baseEnd_3898586] using wordTrace_append hprefix tailTrace_3898586
  have hstable : (prefixWord ++ tailWord_3898586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898586).length < 2 ^ (prefixWord ++ tailWord_3898586).sum := by decide
  have hdescent : baseEnd_3898586 < baseStart_3898586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898627 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 3]
def baseStart_3898627 : Nat := 118140960795 + 3898627 * 2 ^ 59
def prefixEnd_3898627 : Nat := 4983230072969 + 3 ^ 40 * 3898627 * 2
def baseEnd_3898627 : Nat := 2001869543596223337633047

theorem tailTrace_3898627 : CollatzResearch.WordTrace tailWord_3898627 prefixEnd_3898627 2001869543596223337633047 := by
  unfold tailWord_3898627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142194608446947686327078135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94796405631298457551385423 142194608446947686327078135)
  ·
    refine ⟨213291912670421529490617203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142194608446947686327078135 213291912670421529490617203)
    ·
      refine ⟨319937869005632294235925805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213291912670421529490617203 319937869005632294235925805)
      ·
        refine ⟨119976700877112110338472177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319937869005632294235925805 119976700877112110338472177)
        ·
          refine ⟨89982525657834082753854133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119976700877112110338472177 89982525657834082753854133)
          ·
            refine ⟨8435861780421945258173825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89982525657834082753854133 8435861780421945258173825)
            ·
              refine ⟨6326896335316458943630369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8435861780421945258173825 6326896335316458943630369)
              ·
                refine ⟨4745172251487344207722777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326896335316458943630369 4745172251487344207722777)
                ·
                  refine ⟨3558879188615508155792083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745172251487344207722777 3558879188615508155792083)
                  ·
                    refine ⟨5338318782923262233688125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558879188615508155792083 5338318782923262233688125)
                    ·
                      refine ⟨2001869543596223337633047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338318782923262233688125 2001869543596223337633047)
                      ·
                        rfl

theorem cell23_3898627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_3898627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898627 prefixEnd_3898627 := by exact prefixLift 3898627
  have htrace : WordTrace (prefixWord ++ tailWord_3898627) baseStart_3898627 baseEnd_3898627 := by
    simpa [prefixWord, tailWord_3898627, baseEnd_3898627] using wordTrace_append hprefix tailTrace_3898627
  have hstable : (prefixWord ++ tailWord_3898627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898627).length < 2 ^ (prefixWord ++ tailWord_3898627).sum := by decide
  have hdescent : baseEnd_3898627 < baseStart_3898627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898628 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3898628 : Nat := 118140960795 + 3898628 * 2 ^ 59
def prefixEnd_3898628 : Nat := 4983230072969 + 3 ^ 40 * 3898628 * 2
def baseEnd_3898628 : Nat := 2001870057076877833720543

theorem tailTrace_3898628 : CollatzResearch.WordTrace tailWord_3898628 prefixEnd_3898628 2001870057076877833720543 := by
  unfold tailWord_3898628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71097322459972031748932269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94796429946629375665243025 71097322459972031748932269)
  ·
    refine ⟨26661495922489511905849601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71097322459972031748932269 26661495922489511905849601)
    ·
      refine ⟨19996121941867133929387201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26661495922489511905849601 19996121941867133929387201)
      ·
        refine ⟨14997091456400350447040401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19996121941867133929387201 14997091456400350447040401)
        ·
          refine ⟨11247818592300262835280301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14997091456400350447040401 11247818592300262835280301)
          ·
            refine ⟨4217931972112598563230113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11247818592300262835280301 4217931972112598563230113)
            ·
              refine ⟨3163448979084448922422585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4217931972112598563230113 3163448979084448922422585)
              ·
                refine ⟨2372586734313336691816939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163448979084448922422585 2372586734313336691816939)
                ·
                  refine ⟨3558880101470005037725409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372586734313336691816939 3558880101470005037725409)
                  ·
                    refine ⟨2669160076102503778294057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558880101470005037725409 2669160076102503778294057)
                    ·
                      refine ⟨2001870057076877833720543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669160076102503778294057 2001870057076877833720543)
                      ·
                        rfl

theorem cell23_3898628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3898628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898628 prefixEnd_3898628 := by exact prefixLift 3898628
  have htrace : WordTrace (prefixWord ++ tailWord_3898628) baseStart_3898628 baseEnd_3898628 := by
    simpa [prefixWord, tailWord_3898628, baseEnd_3898628] using wordTrace_append hprefix tailTrace_3898628
  have hstable : (prefixWord ++ tailWord_3898628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898628).length < 2 ^ (prefixWord ++ tailWord_3898628).sum := by decide
  have hdescent : baseEnd_3898628 < baseStart_3898628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898678 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3898678 : Nat := 118140960795 + 3898678 * 2 ^ 59
def prefixEnd_3898678 : Nat := 4983230072969 + 3 ^ 40 * 3898678 * 2
def baseEnd_3898678 : Nat := 2001895731109602638095313

theorem tailTrace_3898678 : CollatzResearch.WordTrace tailWord_3898678 prefixEnd_3898678 2001895731109602638095313 := by
  unfold tailWord_3898678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887279285610182627324043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94797645713175281358123125 8887279285610182627324043)
  ·
    refine ⟨13330918928415273940986065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887279285610182627324043 13330918928415273940986065)
    ·
      refine ⟨9998189196311455455739549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13330918928415273940986065 9998189196311455455739549)
      ·
        refine ⟨3749320948616795795902331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9998189196311455455739549 3749320948616795795902331)
        ·
          refine ⟨5623981422925193693853497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749320948616795795902331 5623981422925193693853497)
          ·
            refine ⟨4217986067193895270390123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5623981422925193693853497 4217986067193895270390123)
            ·
              refine ⟨6326979100790842905585185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217986067193895270390123 6326979100790842905585185)
              ·
                refine ⟨4745234325593132179188889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326979100790842905585185 4745234325593132179188889)
                ·
                  refine ⟨3558925744194849134391667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745234325593132179188889 3558925744194849134391667)
                  ·
                    refine ⟨5338388616292273701587501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3558925744194849134391667 5338388616292273701587501)
                    ·
                      refine ⟨2001895731109602638095313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338388616292273701587501 2001895731109602638095313)
                      ·
                        rfl

theorem cell23_3898678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3898678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898678 prefixEnd_3898678 := by exact prefixLift 3898678
  have htrace : WordTrace (prefixWord ++ tailWord_3898678) baseStart_3898678 baseEnd_3898678 := by
    simpa [prefixWord, tailWord_3898678, baseEnd_3898678] using wordTrace_append hprefix tailTrace_3898678
  have hstable : (prefixWord ++ tailWord_3898678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898678).length < 2 ^ (prefixWord ++ tailWord_3898678).sum := by decide
  have hdescent : baseEnd_3898678 < baseStart_3898678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898684 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_3898684 : Nat := 118140960795 + 3898684 * 2 ^ 59
def prefixEnd_3898684 : Nat := 4983230072969 + 3 ^ 40 * 3898684 * 2
def baseEnd_3898684 : Nat := 2001898811993529614620285

theorem tailTrace_3898684 : CollatzResearch.WordTrace tailWord_3898684 prefixEnd_3898684 2001898811993529614620285 := by
  unfold tailWord_3898684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71098343703870592530951553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94797791605160790041268737 71098343703870592530951553)
  ·
    refine ⟨53323757777902944398213665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71098343703870592530951553 53323757777902944398213665)
    ·
      refine ⟨39992818333427208298660249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53323757777902944398213665 39992818333427208298660249)
      ·
        refine ⟨29994613750070406223995187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39992818333427208298660249 29994613750070406223995187)
        ·
          refine ⟨44991920625105609335992781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29994613750070406223995187 44991920625105609335992781)
          ·
            refine ⟨16871970234414603500997293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44991920625105609335992781 16871970234414603500997293)
            ·
              refine ⟨6326988837905476312873985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16871970234414603500997293 6326988837905476312873985)
              ·
                refine ⟨4745241628429107234655489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6326988837905476312873985 4745241628429107234655489)
                ·
                  refine ⟨3558931221321830425991617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745241628429107234655489 3558931221321830425991617)
                  ·
                    refine ⟨2669198415991372819493713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3558931221321830425991617 2669198415991372819493713)
                    ·
                      refine ⟨2001898811993529614620285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669198415991372819493713 2001898811993529614620285)
                      ·
                        rfl

theorem cell23_3898684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_3898684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898684 prefixEnd_3898684 := by exact prefixLift 3898684
  have htrace : WordTrace (prefixWord ++ tailWord_3898684) baseStart_3898684 baseEnd_3898684 := by
    simpa [prefixWord, tailWord_3898684, baseEnd_3898684] using wordTrace_append hprefix tailTrace_3898684
  have hstable : (prefixWord ++ tailWord_3898684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898684).length < 2 ^ (prefixWord ++ tailWord_3898684).sum := by decide
  have hdescent : baseEnd_3898684 < baseStart_3898684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898700 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3898700 : Nat := 118140960795 + 3898700 * 2 ^ 59
def prefixEnd_3898700 : Nat := 4983230072969 + 3 ^ 40 * 3898700 * 2
def baseEnd_3898700 : Nat := 2001907027684001552020211

theorem tailTrace_3898700 : CollatzResearch.WordTrace tailWord_3898700 prefixEnd_3898700 2001907027684001552020211 := by
  unfold tailWord_3898700
  simp only [CollatzResearch.WordTrace]
  refine ⟨71098635487841609897242777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94798180650455479862990369 71098635487841609897242777)
  ·
    refine ⟨53323976615881207422932083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71098635487841609897242777 53323976615881207422932083)
    ·
      refine ⟨79985964923821811134398125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53323976615881207422932083 79985964923821811134398125)
      ·
        refine ⟨29994736846433179175399297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79985964923821811134398125 29994736846433179175399297)
        ·
          refine ⟨22496052634824884381549473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29994736846433179175399297 22496052634824884381549473)
          ·
            refine ⟨16872039476118663286162105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22496052634824884381549473 16872039476118663286162105)
            ·
              refine ⟨12654029607088997464621579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16872039476118663286162105 12654029607088997464621579)
              ·
                refine ⟨18981044410633496196932369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654029607088997464621579 18981044410633496196932369)
                ·
                  refine ⟨14235783307975122147699277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18981044410633496196932369 14235783307975122147699277)
                  ·
                    refine ⟨5338418740490670805387229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14235783307975122147699277 5338418740490670805387229)
                    ·
                      refine ⟨2001907027684001552020211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338418740490670805387229 2001907027684001552020211)
                      ·
                        rfl

theorem cell23_3898700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3898700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898700 prefixEnd_3898700 := by exact prefixLift 3898700
  have htrace : WordTrace (prefixWord ++ tailWord_3898700) baseStart_3898700 baseEnd_3898700 := by
    simpa [prefixWord, tailWord_3898700, baseEnd_3898700] using wordTrace_append hprefix tailTrace_3898700
  have hstable : (prefixWord ++ tailWord_3898700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898700).length < 2 ^ (prefixWord ++ tailWord_3898700).sum := by decide
  have hdescent : baseEnd_3898700 < baseStart_3898700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898777 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_3898777 : Nat := 118140960795 + 3898777 * 2 ^ 59
def prefixEnd_3898777 : Nat := 4983230072969 + 3 ^ 40 * 3898777 * 2
def baseEnd_3898777 : Nat := 2001946565694397750757357

theorem tailTrace_3898777 : CollatzResearch.WordTrace tailWord_3898777 prefixEnd_3898777 2001946565694397750757357 := by
  unfold tailWord_3898777
  simp only [CollatzResearch.WordTrace]
  refine ⟨142200079396404261945038585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94800052930936174630025723 142200079396404261945038585)
  ·
    refine ⟨106650059547303196458778939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142200079396404261945038585 106650059547303196458778939)
    ·
      refine ⟨159975089320954794688168409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106650059547303196458778939 159975089320954794688168409)
      ·
        refine ⟨119981316990716096016126307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159975089320954794688168409 119981316990716096016126307)
        ·
          refine ⟨179971975486074144024189461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119981316990716096016126307 179971975486074144024189461)
          ·
            refine ⟨8436186350909725501133881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179971975486074144024189461 8436186350909725501133881)
            ·
              refine ⟨6327139763182294125850411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436186350909725501133881 6327139763182294125850411)
              ·
                refine ⟨9490709644773441188775617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327139763182294125850411 9490709644773441188775617)
                ·
                  refine ⟨7118032233580080891581713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9490709644773441188775617 7118032233580080891581713)
                  ·
                    refine ⟨5338524175185060668686285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7118032233580080891581713 5338524175185060668686285)
                    ·
                      refine ⟨2001946565694397750757357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338524175185060668686285 2001946565694397750757357)
                      ·
                        rfl

theorem cell23_3898777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_3898777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898777 prefixEnd_3898777 := by exact prefixLift 3898777
  have htrace : WordTrace (prefixWord ++ tailWord_3898777) baseStart_3898777 baseEnd_3898777 := by
    simpa [prefixWord, tailWord_3898777, baseEnd_3898777] using wordTrace_append hprefix tailTrace_3898777
  have hstable : (prefixWord ++ tailWord_3898777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898777).length < 2 ^ (prefixWord ++ tailWord_3898777).sum := by decide
  have hdescent : baseEnd_3898777 < baseStart_3898777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898797 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3898797 : Nat := 118140960795 + 3898797 * 2 ^ 59
def prefixEnd_3898797 : Nat := 4983230072969 + 3 ^ 40 * 3898797 * 2
def baseEnd_3898797 : Nat := 222439648367498630278585

theorem tailTrace_3898797 : CollatzResearch.WordTrace tailWord_3898797 prefixEnd_3898797 222439648367498630278585 := by
  unfold tailWord_3898797
  simp only [CollatzResearch.WordTrace]
  refine ⟨142200808856331805360766645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94800539237554536907177763 142200808856331805360766645)
  ·
    refine ⟨13331325830281106752571873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142200808856331805360766645 13331325830281106752571873)
    ·
      refine ⟨9998494372710830064428905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13331325830281106752571873 9998494372710830064428905)
      ·
        refine ⟨7498870779533122548321679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9998494372710830064428905 7498870779533122548321679)
        ·
          refine ⟨11248306169299683822482519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7498870779533122548321679 11248306169299683822482519)
          ·
            refine ⟨16872459253949525733723779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248306169299683822482519 16872459253949525733723779)
            ·
              refine ⟨25308688880924288600585669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872459253949525733723779 25308688880924288600585669)
              ·
                refine ⟨4745379165173304112609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25308688880924288600585669 4745379165173304112609813)
                ·
                  refine ⟨222439648367498630278585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4745379165173304112609813 222439648367498630278585)
                  ·
                    rfl

theorem cell23_3898797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3898797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898797 prefixEnd_3898797 := by exact prefixLift 3898797
  have htrace : WordTrace (prefixWord ++ tailWord_3898797) baseStart_3898797 baseEnd_3898797 := by
    simpa [prefixWord, tailWord_3898797, baseEnd_3898797] using wordTrace_append hprefix tailTrace_3898797
  have hstable : (prefixWord ++ tailWord_3898797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898797).length < 2 ^ (prefixWord ++ tailWord_3898797).sum := by decide
  have hdescent : baseEnd_3898797 < baseStart_3898797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898803 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5]
def baseStart_3898803 : Nat := 118140960795 + 3898803 * 2 ^ 59
def prefixEnd_3898803 : Nat := 4983230072969 + 3 ^ 40 * 3898803 * 2
def baseEnd_3898803 : Nat := 2001959916191414649032237

theorem tailTrace_3898803 : CollatzResearch.WordTrace tailWord_3898803 prefixEnd_3898803 2001959916191414649032237 := by
  unfold tailWord_3898803
  simp only [CollatzResearch.WordTrace]
  refine ⟨142201027694310068385485063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94800685129540045590323375 142201027694310068385485063)
  ·
    refine ⟨213301541541465102578227595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142201027694310068385485063 213301541541465102578227595)
    ·
      refine ⟨319952312312197653867341393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213301541541465102578227595 319952312312197653867341393)
      ·
        refine ⟨239964234234148240400506045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319952312312197653867341393 239964234234148240400506045)
        ·
          refine ⟨89986587837805590150189767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239964234234148240400506045 89986587837805590150189767)
          ·
            refine ⟨134979881756708385225284651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89986587837805590150189767 134979881756708385225284651)
            ·
              refine ⟨202469822635062577837926977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134979881756708385225284651 202469822635062577837926977)
              ·
                refine ⟨151852366976296933378445233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202469822635062577837926977 151852366976296933378445233)
                ·
                  refine ⟨113889275232222700033833925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151852366976296933378445233 113889275232222700033833925)
                  ·
                    refine ⟨21354239106041756256343861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113889275232222700033833925 21354239106041756256343861)
                    ·
                      refine ⟨2001959916191414649032237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21354239106041756256343861 2001959916191414649032237)
                      ·
                        rfl

theorem cell23_3898803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_3898803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898803 prefixEnd_3898803 := by exact prefixLift 3898803
  have htrace : WordTrace (prefixWord ++ tailWord_3898803) baseStart_3898803 baseEnd_3898803 := by
    simpa [prefixWord, tailWord_3898803, baseEnd_3898803] using wordTrace_append hprefix tailTrace_3898803
  have hstable : (prefixWord ++ tailWord_3898803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898803).length < 2 ^ (prefixWord ++ tailWord_3898803).sum := by decide
  have hdescent : baseEnd_3898803 < baseStart_3898803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898807 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_3898807 : Nat := 118140960795 + 3898807 * 2 ^ 59
def prefixEnd_3898807 : Nat := 4983230072969 + 3 ^ 40 * 3898807 * 2
def baseEnd_3898807 : Nat := 2001961970114032633382219

theorem tailTrace_3898807 : CollatzResearch.WordTrace tailWord_3898807 prefixEnd_3898807 2001961970114032633382219 := by
  unfold tailWord_3898807
  simp only [CollatzResearch.WordTrace]
  refine ⟨142201173586295577068630675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94800782390863718045753783 142201173586295577068630675)
  ·
    refine ⟨213301760379443365602946013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142201173586295577068630675 213301760379443365602946013)
    ·
      refine ⟨79988160142291262101104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213301760379443365602946013 79988160142291262101104755)
      ·
        refine ⟨119982240213436893151657133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79988160142291262101104755 119982240213436893151657133)
        ·
          refine ⟨44993340080038834931871425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119982240213436893151657133 44993340080038834931871425)
          ·
            refine ⟨33745005060029126198903569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44993340080038834931871425 33745005060029126198903569)
            ·
              refine ⟨25308753795021844649177677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33745005060029126198903569 25308753795021844649177677)
              ·
                refine ⟨9490782673133191743441629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25308753795021844649177677 9490782673133191743441629)
                ·
                  refine ⟨3559043502424946903790611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9490782673133191743441629 3559043502424946903790611)
                  ·
                    refine ⟨5338565253637420355685917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559043502424946903790611 5338565253637420355685917)
                    ·
                      refine ⟨2001961970114032633382219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338565253637420355685917 2001961970114032633382219)
                      ·
                        rfl

theorem cell23_3898807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_3898807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898807 prefixEnd_3898807 := by exact prefixLift 3898807
  have htrace : WordTrace (prefixWord ++ tailWord_3898807) baseStart_3898807 baseEnd_3898807 := by
    simpa [prefixWord, tailWord_3898807, baseEnd_3898807] using wordTrace_append hprefix tailTrace_3898807
  have hstable : (prefixWord ++ tailWord_3898807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898807).length < 2 ^ (prefixWord ++ tailWord_3898807).sum := by decide
  have hdescent : baseEnd_3898807 < baseStart_3898807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898840 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_3898840 : Nat := 118140960795 + 3898840 * 2 ^ 59
def prefixEnd_3898840 : Nat := 4983230072969 + 3 ^ 40 * 3898840 * 2
def baseEnd_3898840 : Nat := 667326304991877001423189

theorem tailTrace_3898840 : CollatzResearch.WordTrace tailWord_3898840 prefixEnd_3898840 667326304991877001423189 := by
  unfold tailWord_3898840
  simp only [CollatzResearch.WordTrace]
  refine ⟨71101188597588011852290987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94801584796784015803054649 71101188597588011852290987)
  ·
    refine ⟨106651782896382017778436481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71101188597588011852290987 106651782896382017778436481)
    ·
      refine ⟨79988837172286513333827361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106651782896382017778436481 79988837172286513333827361)
      ·
        refine ⟨59991627879214885000370521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79988837172286513333827361 59991627879214885000370521)
        ·
          refine ⟨44993720909411163750277891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59991627879214885000370521 44993720909411163750277891)
          ·
            refine ⟨67490581364116745625416837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44993720909411163750277891 67490581364116745625416837)
            ·
              refine ⟨12654484005771889804765657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67490581364116745625416837 12654484005771889804765657)
              ·
                refine ⟨9490863004328917353574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12654484005771889804765657 9490863004328917353574243)
                ·
                  refine ⟨14236294506493376030361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490863004328917353574243 14236294506493376030361365)
                  ·
                    refine ⟨667326304991877001423189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14236294506493376030361365 667326304991877001423189)
                    ·
                      rfl

theorem cell23_3898840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_3898840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898840 prefixEnd_3898840 := by exact prefixLift 3898840
  have htrace : WordTrace (prefixWord ++ tailWord_3898840) baseStart_3898840 baseEnd_3898840 := by
    simpa [prefixWord, tailWord_3898840, baseEnd_3898840] using wordTrace_append hprefix tailTrace_3898840
  have hstable : (prefixWord ++ tailWord_3898840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898840).length < 2 ^ (prefixWord ++ tailWord_3898840).sum := by decide
  have hdescent : baseEnd_3898840 < baseStart_3898840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898841 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 1, 1, 3]
def baseStart_3898841 : Nat := 118140960795 + 3898841 * 2 ^ 59
def prefixEnd_3898841 : Nat := 4983230072969 + 3 ^ 40 * 3898841 * 2
def baseEnd_3898841 : Nat := 2001979428456285500357063

theorem tailTrace_3898841 : CollatzResearch.WordTrace tailWord_3898841 prefixEnd_3898841 2001979428456285500357063 := by
  unfold tailWord_3898841
  simp only [CollatzResearch.WordTrace]
  refine ⟨142202413668172400875368377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94801609112114933916912251 142202413668172400875368377)
  ·
    refine ⟨106651810251129300656526283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142202413668172400875368377 106651810251129300656526283)
    ·
      refine ⟨159977715376693950984789425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106651810251129300656526283 159977715376693950984789425)
      ·
        refine ⟨119983286532520463238592069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159977715376693950984789425 119983286532520463238592069)
        ·
          refine ⟨22496866224847586857236013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119983286532520463238592069 22496866224847586857236013)
          ·
            refine ⟨8436324834317845071463505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22496866224847586857236013 8436324834317845071463505)
            ·
              refine ⟨6327243625738383803597629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8436324834317845071463505 6327243625738383803597629)
              ·
                refine ⟨2372716359651893926349111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6327243625738383803597629 2372716359651893926349111)
                ·
                  refine ⟨3559074539477840889523667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372716359651893926349111 3559074539477840889523667)
                  ·
                    refine ⟨5338611809216761334285501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559074539477840889523667 5338611809216761334285501)
                    ·
                      refine ⟨2001979428456285500357063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338611809216761334285501 2001979428456285500357063)
                      ·
                        rfl

theorem cell23_3898841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_3898841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898841 prefixEnd_3898841 := by exact prefixLift 3898841
  have htrace : WordTrace (prefixWord ++ tailWord_3898841) baseStart_3898841 baseEnd_3898841 := by
    simpa [prefixWord, tailWord_3898841, baseEnd_3898841] using wordTrace_append hprefix tailTrace_3898841
  have hstable : (prefixWord ++ tailWord_3898841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898841).length < 2 ^ (prefixWord ++ tailWord_3898841).sum := by decide
  have hdescent : baseEnd_3898841 < baseStart_3898841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898847 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_3898847 : Nat := 118140960795 + 3898847 * 2 ^ 59
def prefixEnd_3898847 : Nat := 4983230072969 + 3 ^ 40 * 3898847 * 2
def baseEnd_3898847 : Nat := 2001982509340212476882035

theorem tailTrace_3898847 : CollatzResearch.WordTrace tailWord_3898847 prefixEnd_3898847 2001982509340212476882035 := by
  unfold tailWord_3898847
  simp only [CollatzResearch.WordTrace]
  refine ⟨142202632506150663900086795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94801755004100442600057863 142202632506150663900086795)
  ·
    refine ⟨213303948759225995850130193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142202632506150663900086795 213303948759225995850130193)
    ·
      refine ⟨159977961569419496887597645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213303948759225995850130193 159977961569419496887597645)
      ·
        refine ⟨59991735588532311332849117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159977961569419496887597645 59991735588532311332849117)
        ·
          refine ⟨22496900845699616749818419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59991735588532311332849117 22496900845699616749818419)
          ·
            refine ⟨33745351268549425124727629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22496900845699616749818419 33745351268549425124727629)
            ·
              refine ⟨12654506725706034421772861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33745351268549425124727629 12654506725706034421772861)
              ·
                refine ⟨4745440022139762908164823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12654506725706034421772861 4745440022139762908164823)
                ·
                  refine ⟨7118160033209644362247235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745440022139762908164823 7118160033209644362247235)
                  ·
                    refine ⟨10677240049814466543370853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118160033209644362247235 10677240049814466543370853)
                    ·
                      refine ⟨2001982509340212476882035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10677240049814466543370853 2001982509340212476882035)
                      ·
                        rfl

theorem cell23_3898847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_3898847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898847 prefixEnd_3898847 := by exact prefixLift 3898847
  have htrace : WordTrace (prefixWord ++ tailWord_3898847) baseStart_3898847 baseEnd_3898847 := by
    simpa [prefixWord, tailWord_3898847, baseEnd_3898847] using wordTrace_append hprefix tailTrace_3898847
  have hstable : (prefixWord ++ tailWord_3898847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898847).length < 2 ^ (prefixWord ++ tailWord_3898847).sum := by decide
  have hdescent : baseEnd_3898847 < baseStart_3898847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898864 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2]
def baseStart_3898864 : Nat := 118140960795 + 3898864 * 2 ^ 59
def prefixEnd_3898864 : Nat := 4983230072969 + 3 ^ 40 * 3898864 * 2
def baseEnd_3898864 : Nat := 2001991238511338910369457

theorem tailTrace_3898864 : CollatzResearch.WordTrace tailWord_3898864 prefixEnd_3898864 2001991238511338910369457 := by
  unfold tailWord_3898864
  simp only [CollatzResearch.WordTrace]
  refine ⟨71101626273544537901727823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94802168364726050535637097 71101626273544537901727823)
  ·
    refine ⟨106652439410316806852591735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71101626273544537901727823 106652439410316806852591735)
    ·
      refine ⟨159978659115475210278887603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106652439410316806852591735 159978659115475210278887603)
      ·
        refine ⟨239967988673212815418331405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159978659115475210278887603 239967988673212815418331405)
        ·
          refine ⟨89987995752454805781874277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239967988673212815418331405 89987995752454805781874277)
          ·
            refine ⟨16872749203585276084101427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89987995752454805781874277 16872749203585276084101427)
            ·
              refine ⟨25309123805377914126152141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16872749203585276084101427 25309123805377914126152141)
              ·
                refine ⟨9490921427016717797307053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25309123805377914126152141 9490921427016717797307053)
                ·
                  refine ⟨3559095535131269173990145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9490921427016717797307053 3559095535131269173990145)
                  ·
                    refine ⟨2669321651348451880492609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559095535131269173990145 2669321651348451880492609)
                    ·
                      refine ⟨2001991238511338910369457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669321651348451880492609 2001991238511338910369457)
                      ·
                        rfl

theorem cell23_3898864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2].length) (baseStart_3898864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898864 prefixEnd_3898864 := by exact prefixLift 3898864
  have htrace : WordTrace (prefixWord ++ tailWord_3898864) baseStart_3898864 baseEnd_3898864 := by
    simpa [prefixWord, tailWord_3898864, baseEnd_3898864] using wordTrace_append hprefix tailTrace_3898864
  have hstable : (prefixWord ++ tailWord_3898864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898864).length < 2 ^ (prefixWord ++ tailWord_3898864).sum := by decide
  have hdescent : baseEnd_3898864 < baseStart_3898864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898874 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_3898874 : Nat := 118140960795 + 3898874 * 2 ^ 59
def prefixEnd_3898874 : Nat := 4983230072969 + 3 ^ 40 * 3898874 * 2
def baseEnd_3898874 : Nat := 667332124439294623748137

theorem tailTrace_3898874 : CollatzResearch.WordTrace tailWord_3898874 prefixEnd_3898874 667332124439294623748137 := by
  unfold tailWord_3898874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35550904319263211877829919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94802411518035231674213117 35550904319263211877829919)
  ·
    refine ⟨53326356478894817816744879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35550904319263211877829919 53326356478894817816744879)
    ·
      refine ⟨79989534718342226725117319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53326356478894817816744879 79989534718342226725117319)
      ·
        refine ⟨119984302077513340087675979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79989534718342226725117319 119984302077513340087675979)
        ·
          refine ⟨179976453116270010131513969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119984302077513340087675979 179976453116270010131513969)
          ·
            refine ⟨134982339837202507598635477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179976453116270010131513969 134982339837202507598635477)
            ·
              refine ⟨3163648589934433771843019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134982339837202507598635477 3163648589934433771843019)
              ·
                refine ⟨4745472884901650657764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163648589934433771843019 4745472884901650657764529)
                ·
                  refine ⟨3559104663676237993323397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745472884901650657764529 3559104663676237993323397)
                  ·
                    refine ⟨667332124439294623748137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3559104663676237993323397 667332124439294623748137)
                    ·
                      rfl

theorem cell23_3898874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_3898874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898874 prefixEnd_3898874 := by exact prefixLift 3898874
  have htrace : WordTrace (prefixWord ++ tailWord_3898874) baseStart_3898874 baseEnd_3898874 := by
    simpa [prefixWord, tailWord_3898874, baseEnd_3898874] using wordTrace_append hprefix tailTrace_3898874
  have hstable : (prefixWord ++ tailWord_3898874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898874).length < 2 ^ (prefixWord ++ tailWord_3898874).sum := by decide
  have hdescent : baseEnd_3898874 < baseStart_3898874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898877 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_3898877 : Nat := 118140960795 + 3898877 * 2 ^ 59
def prefixEnd_3898877 : Nat := 4983230072969 + 3 ^ 40 * 3898877 * 2
def baseEnd_3898877 : Nat := 2001997913759847359506897

theorem tailTrace_3898877 : CollatzResearch.WordTrace tailWord_3898877 prefixEnd_3898877 2001997913759847359506897 := by
  unfold tailWord_3898877
  simp only [CollatzResearch.WordTrace]
  refine ⟨142203726696041979023678885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94802484464027986015785923 142203726696041979023678885)
  ·
    refine ⟨26663198755507871066939791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142203726696041979023678885 26663198755507871066939791)
    ·
      refine ⟨39994798133261806600409687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663198755507871066939791 39994798133261806600409687)
      ·
        refine ⟨59992197199892709900614531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39994798133261806600409687 59992197199892709900614531)
        ·
          refine ⟨89988295799839064850921797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59992197199892709900614531 89988295799839064850921797)
          ·
            refine ⟨16872805462469824659547837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89988295799839064850921797 16872805462469824659547837)
            ·
              refine ⟨6327302048426184247330439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16872805462469824659547837 6327302048426184247330439)
              ·
                refine ⟨9490953072639276370995659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327302048426184247330439 9490953072639276370995659)
                ·
                  refine ⟨14236429608958914556493489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9490953072639276370995659 14236429608958914556493489)
                  ·
                    refine ⟨10677322206719185917370117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14236429608958914556493489 10677322206719185917370117)
                    ·
                      refine ⟨2001997913759847359506897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10677322206719185917370117 2001997913759847359506897)
                      ·
                        rfl

theorem cell23_3898877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_3898877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898877 prefixEnd_3898877 := by exact prefixLift 3898877
  have htrace : WordTrace (prefixWord ++ tailWord_3898877) baseStart_3898877 baseEnd_3898877 := by
    simpa [prefixWord, tailWord_3898877, baseEnd_3898877] using wordTrace_append hprefix tailTrace_3898877
  have hstable : (prefixWord ++ tailWord_3898877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898877).length < 2 ^ (prefixWord ++ tailWord_3898877).sum := by decide
  have hdescent : baseEnd_3898877 < baseStart_3898877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898887 : List Nat := [1, 1, 4, 3, 2, 1, 4, 7]
def baseStart_3898887 : Nat := 118140960795 + 3898887 * 2 ^ 59
def prefixEnd_3898887 : Nat := 4983230072969 + 3 ^ 40 * 3898887 * 2
def baseEnd_3898887 : Nat := 74148261058014530384513

theorem tailTrace_3898887 : CollatzResearch.WordTrace tailWord_3898887 prefixEnd_3898887 74148261058014530384513 := by
  unfold tailWord_3898887
  simp only [CollatzResearch.WordTrace]
  refine ⟨142204091426005750731542915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94802727617337167154361943 142204091426005750731542915)
  ·
    refine ⟨213306137139008626097314373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142204091426005750731542915 213306137139008626097314373)
    ·
      refine ⟨39994900713564117393246445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213306137139008626097314373 39994900713564117393246445)
      ·
        refine ⟨14998087767586544022467417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39994900713564117393246445 14998087767586544022467417)
        ·
          refine ⟨11248565825689908016850563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14998087767586544022467417 11248565825689908016850563)
          ·
            refine ⟨16872848738534862025275845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11248565825689908016850563 16872848738534862025275845)
            ·
              refine ⟨3163659138475286629739221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16872848738534862025275845 3163659138475286629739221)
              ·
                refine ⟨74148261058014530384513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3163659138475286629739221 74148261058014530384513)
                ·
                  rfl

theorem cell23_3898887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 7].length) (baseStart_3898887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898887 prefixEnd_3898887 := by exact prefixLift 3898887
  have htrace : WordTrace (prefixWord ++ tailWord_3898887) baseStart_3898887 baseEnd_3898887 := by
    simpa [prefixWord, tailWord_3898887, baseEnd_3898887] using wordTrace_append hprefix tailTrace_3898887
  have hstable : (prefixWord ++ tailWord_3898887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898887).length < 2 ^ (prefixWord ++ tailWord_3898887).sum := by decide
  have hdescent : baseEnd_3898887 < baseStart_3898887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898897 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_3898897 : Nat := 118140960795 + 3898897 * 2 ^ 59
def prefixEnd_3898897 : Nat := 4983230072969 + 3 ^ 40 * 3898897 * 2
def baseEnd_3898897 : Nat := 2002008183372937281256805

theorem tailTrace_3898897 : CollatzResearch.WordTrace tailWord_3898897 prefixEnd_3898897 2002008183372937281256805 := by
  unfold tailWord_3898897
  simp only [CollatzResearch.WordTrace]
  refine ⟨142204456155969522439406945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94802970770646348292937963 142204456155969522439406945)
  ·
    refine ⟨106653342116977141829555209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142204456155969522439406945 106653342116977141829555209)
    ·
      refine ⟨79990006587732856372166407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106653342116977141829555209 79990006587732856372166407)
      ·
        refine ⟨119985009881599284558249611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79990006587732856372166407 119985009881599284558249611)
        ·
          refine ⟨179977514822398926837374417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119985009881599284558249611 179977514822398926837374417)
          ·
            refine ⟨134983136116799195128030813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179977514822398926837374417 134983136116799195128030813)
            ·
              refine ⟨50618676043799698173011555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134983136116799195128030813 50618676043799698173011555)
              ·
                refine ⟨75928014065699547259517333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50618676043799698173011555 75928014065699547259517333)
                ·
                  refine ⟨3559125659329666277789875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75928014065699547259517333 3559125659329666277789875)
                  ·
                    refine ⟨5338688488994499416684813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559125659329666277789875 5338688488994499416684813)
                    ·
                      refine ⟨2002008183372937281256805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338688488994499416684813 2002008183372937281256805)
                      ·
                        rfl

theorem cell23_3898897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_3898897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898897 prefixEnd_3898897 := by exact prefixLift 3898897
  have htrace : WordTrace (prefixWord ++ tailWord_3898897) baseStart_3898897 baseEnd_3898897 := by
    simpa [prefixWord, tailWord_3898897, baseEnd_3898897] using wordTrace_append hprefix tailTrace_3898897
  have hstable : (prefixWord ++ tailWord_3898897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898897).length < 2 ^ (prefixWord ++ tailWord_3898897).sum := by decide
  have hdescent : baseEnd_3898897 < baseStart_3898897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898914 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3898914 : Nat := 118140960795 + 3898914 * 2 ^ 59
def prefixEnd_3898914 : Nat := 4983230072969 + 3 ^ 40 * 3898914 * 2
def baseEnd_3898914 : Nat := 2002016912544063714744227

theorem tailTrace_3898914 : CollatzResearch.WordTrace tailWord_3898914 prefixEnd_3898914 2002016912544063714744227 := by
  unfold tailWord_3898914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551269049226983585693949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94803384131271956228517197 35551269049226983585693949)
  ·
    refine ⟨13331725893460118844635231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35551269049226983585693949 13331725893460118844635231)
    ·
      refine ⟨19997588840190178266952847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331725893460118844635231 19997588840190178266952847)
      ·
        refine ⟨29996383260285267400429271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19997588840190178266952847 29996383260285267400429271)
        ·
          refine ⟨44994574890427901100643907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29996383260285267400429271 44994574890427901100643907)
          ·
            refine ⟨67491862335641851650965861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44994574890427901100643907 67491862335641851650965861)
            ·
              refine ⟨12654724187932847184556099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67491862335641851650965861 12654724187932847184556099)
              ·
                refine ⟨18982086281899270776834149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654724187932847184556099 18982086281899270776834149)
                ·
                  refine ⟨3559141177856113270656403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18982086281899270776834149 3559141177856113270656403)
                  ·
                    refine ⟨5338711766784169905984605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559141177856113270656403 5338711766784169905984605)
                    ·
                      refine ⟨2002016912544063714744227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338711766784169905984605 2002016912544063714744227)
                      ·
                        rfl

theorem cell23_3898914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3898914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898914 prefixEnd_3898914 := by exact prefixLift 3898914
  have htrace : WordTrace (prefixWord ++ tailWord_3898914) baseStart_3898914 baseEnd_3898914 := by
    simpa [prefixWord, tailWord_3898914, baseEnd_3898914] using wordTrace_append hprefix tailTrace_3898914
  have hstable : (prefixWord ++ tailWord_3898914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898914).length < 2 ^ (prefixWord ++ tailWord_3898914).sum := by decide
  have hdescent : baseEnd_3898914 < baseStart_3898914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898915 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 1, 2, 2]
def baseStart_3898915 : Nat := 118140960795 + 3898915 * 2 ^ 59
def prefixEnd_3898915 : Nat := 4983230072969 + 3 ^ 40 * 3898915 * 2
def baseEnd_3898915 : Nat := 2002017426024718210831723

theorem tailTrace_3898915 : CollatzResearch.WordTrace tailWord_3898915 prefixEnd_3898915 2002017426024718210831723 := by
  unfold tailWord_3898915
  simp only [CollatzResearch.WordTrace]
  refine ⟨142205112669904311513562199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94803408446602874342374799 142205112669904311513562199)
  ·
    refine ⟨213307669004856467270343299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142205112669904311513562199 213307669004856467270343299)
    ·
      refine ⟨319961503507284700905514949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213307669004856467270343299 319961503507284700905514949)
      ·
        refine ⟨59992781907615881419784053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319961503507284700905514949 59992781907615881419784053)
        ·
          refine ⟨5624323303838988883104755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59992781907615881419784053 5624323303838988883104755)
          ·
            refine ⟨8436484955758483324657133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624323303838988883104755 8436484955758483324657133)
            ·
              refine ⟨3163681858409431246746425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8436484955758483324657133 3163681858409431246746425)
              ·
                refine ⟨2372761393807073435059819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163681858409431246746425 2372761393807073435059819)
                ·
                  refine ⟨3559142090710610152589729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372761393807073435059819 3559142090710610152589729)
                  ·
                    refine ⟨2669356568032957614442297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559142090710610152589729 2669356568032957614442297)
                    ·
                      refine ⟨2002017426024718210831723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669356568032957614442297 2002017426024718210831723)
                      ·
                        rfl

theorem cell23_3898915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_3898915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898915 prefixEnd_3898915 := by exact prefixLift 3898915
  have htrace : WordTrace (prefixWord ++ tailWord_3898915) baseStart_3898915 baseEnd_3898915 := by
    simpa [prefixWord, tailWord_3898915, baseEnd_3898915] using wordTrace_append hprefix tailTrace_3898915
  have hstable : (prefixWord ++ tailWord_3898915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898915).length < 2 ^ (prefixWord ++ tailWord_3898915).sum := by decide
  have hdescent : baseEnd_3898915 < baseStart_3898915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898930 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3898930 : Nat := 118140960795 + 3898930 * 2 ^ 59
def prefixEnd_3898930 : Nat := 4983230072969 + 3 ^ 40 * 3898930 * 2
def baseEnd_3898930 : Nat := 667341709411511884048051

theorem tailTrace_3898930 : CollatzResearch.WordTrace tailWord_3898930 prefixEnd_3898930 667341709411511884048051 := by
  unfold tailWord_3898930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551414941212492268839561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94803773176566646050238829 35551414941212492268839561)
  ·
    refine ⟨26663561205909369201629671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35551414941212492268839561 26663561205909369201629671)
    ·
      refine ⟨39995341808864053802444507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663561205909369201629671 39995341808864053802444507)
      ·
        refine ⟨59993012713296080703666761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39995341808864053802444507 59993012713296080703666761)
        ·
          refine ⟨44994759534972060527750071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59993012713296080703666761 44994759534972060527750071)
          ·
            refine ⟨67492139302458090791625107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44994759534972060527750071 67492139302458090791625107)
            ·
              refine ⟨101238208953687136187437661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67492139302458090791625107 101238208953687136187437661)
              ·
                refine ⟨37964328357632676070289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101238208953687136187437661 37964328357632676070289123)
                ·
                  refine ⟨56946492536449014105433685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37964328357632676070289123 56946492536449014105433685)
                  ·
                    refine ⟨667341709411511884048051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56946492536449014105433685 667341709411511884048051)
                    ·
                      rfl

theorem cell23_3898930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3898930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898930 prefixEnd_3898930 := by exact prefixLift 3898930
  have htrace : WordTrace (prefixWord ++ tailWord_3898930) baseStart_3898930 baseEnd_3898930 := by
    simpa [prefixWord, tailWord_3898930, baseEnd_3898930] using wordTrace_append hprefix tailTrace_3898930
  have hstable : (prefixWord ++ tailWord_3898930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898930).length < 2 ^ (prefixWord ++ tailWord_3898930).sum := by decide
  have hdescent : baseEnd_3898930 < baseStart_3898930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898931 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 2, 1, 3]
def baseStart_3898931 : Nat := 118140960795 + 3898931 * 2 ^ 59
def prefixEnd_3898931 : Nat := 4983230072969 + 3 ^ 40 * 3898931 * 2
def baseEnd_3898931 : Nat := 2002025641715190148231649

theorem tailTrace_3898931 : CollatzResearch.WordTrace tailWord_3898931 prefixEnd_3898931 2002025641715190148231649 := by
  unfold tailWord_3898931
  simp only [CollatzResearch.WordTrace]
  refine ⟨142205696237846346246144647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94803797491897564164096431 142205696237846346246144647)
  ·
    refine ⟨213308544356769519369216971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142205696237846346246144647 213308544356769519369216971)
    ·
      refine ⟨319962816535154279053825457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213308544356769519369216971 319962816535154279053825457)
      ·
        refine ⟨239972112401365709290369093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319962816535154279053825457 239972112401365709290369093)
        ·
          refine ⟨44994771075256070491944205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239972112401365709290369093 44994771075256070491944205)
          ·
            refine ⟨16873039153221026434479077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44994771075256070491944205 16873039153221026434479077)
            ·
              refine ⟨3163694841228942456464827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16873039153221026434479077 3163694841228942456464827)
              ·
                refine ⟨4745542261843413684697241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163694841228942456464827 4745542261843413684697241)
                ·
                  refine ⟨3559156696382560263522931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4745542261843413684697241 3559156696382560263522931)
                  ·
                    refine ⟨5338735044573840395284397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559156696382560263522931 5338735044573840395284397)
                    ·
                      refine ⟨2002025641715190148231649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338735044573840395284397 2002025641715190148231649)
                      ·
                        rfl

theorem cell23_3898931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 1, 3].length) (baseStart_3898931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898931 prefixEnd_3898931 := by exact prefixLift 3898931
  have htrace : WordTrace (prefixWord ++ tailWord_3898931) baseStart_3898931 baseEnd_3898931 := by
    simpa [prefixWord, tailWord_3898931, baseEnd_3898931] using wordTrace_append hprefix tailTrace_3898931
  have hstable : (prefixWord ++ tailWord_3898931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898931).length < 2 ^ (prefixWord ++ tailWord_3898931).sum := by decide
  have hdescent : baseEnd_3898931 < baseStart_3898931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898941 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3898941 : Nat := 118140960795 + 3898941 * 2 ^ 59
def prefixEnd_3898941 : Nat := 4983230072969 + 3 ^ 40 * 3898941 * 2
def baseEnd_3898941 : Nat := 2002030776521735109106603

theorem tailTrace_3898941 : CollatzResearch.WordTrace tailWord_3898941 prefixEnd_3898941 2002030776521735109106603 := by
  unfold tailWord_3898941
  simp only [CollatzResearch.WordTrace]
  refine ⟨142206060967810117954008677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94804040645206745302672451 142206060967810117954008677)
  ·
    refine ⟨26663636431464397116376627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142206060967810117954008677 26663636431464397116376627)
    ·
      refine ⟨39995454647196595674564941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26663636431464397116376627 39995454647196595674564941)
      ·
        refine ⟨14998295492698723377961853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39995454647196595674564941 14998295492698723377961853)
        ·
          refine ⟨5624360809762021266735695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14998295492698723377961853 5624360809762021266735695)
          ·
            refine ⟨8436541214643031900103543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5624360809762021266735695 8436541214643031900103543)
            ·
              refine ⟨12654811821964547850155315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436541214643031900103543 12654811821964547850155315)
              ·
                refine ⟨18982217732946821775232973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654811821964547850155315 18982217732946821775232973)
                ·
                  refine ⟨7118331649855058165712365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18982217732946821775232973 7118331649855058165712365)
                  ·
                    refine ⟨2669374368695646812142137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7118331649855058165712365 2669374368695646812142137)
                    ·
                      refine ⟨2002030776521735109106603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669374368695646812142137 2002030776521735109106603)
                      ·
                        rfl

theorem cell23_3898941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3898941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898941 prefixEnd_3898941 := by exact prefixLift 3898941
  have htrace : WordTrace (prefixWord ++ tailWord_3898941) baseStart_3898941 baseEnd_3898941 := by
    simpa [prefixWord, tailWord_3898941, baseEnd_3898941] using wordTrace_append hprefix tailTrace_3898941
  have hstable : (prefixWord ++ tailWord_3898941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898941).length < 2 ^ (prefixWord ++ tailWord_3898941).sum := by decide
  have hdescent : baseEnd_3898941 < baseStart_3898941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898954 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_3898954 : Nat := 118140960795 + 3898954 * 2 ^ 59
def prefixEnd_3898954 : Nat := 4983230072969 + 3 ^ 40 * 3898954 * 2
def baseEnd_3898954 : Nat := 2002037451770243558244043

theorem tailTrace_3898954 : CollatzResearch.WordTrace tailWord_3898954 prefixEnd_3898954 2002037451770243558244043 := by
  unfold tailWord_3898954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551633779190755293557979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94804356744508680782821277 35551633779190755293557979)
  ·
    refine ⟨53327450668786132940336969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35551633779190755293557979 53327450668786132940336969)
    ·
      refine ⟨39995588001589599705252727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53327450668786132940336969 39995588001589599705252727)
      ·
        refine ⟨59993382002384399557879091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39995588001589599705252727 59993382002384399557879091)
        ·
          refine ⟨89990073003576599336818637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59993382002384399557879091 89990073003576599336818637)
          ·
            refine ⟨33746277376341224751306989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89990073003576599336818637 33746277376341224751306989)
            ·
              refine ⟨12654854016127959281740121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33746277376341224751306989 12654854016127959281740121)
              ·
                refine ⟨9491140512095969461305091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12654854016127959281740121 9491140512095969461305091)
                ·
                  refine ⟨14236710768143954191957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491140512095969461305091 14236710768143954191957637)
                  ·
                    refine ⟨2669383269026991410992057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14236710768143954191957637 2669383269026991410992057)
                    ·
                      refine ⟨2002037451770243558244043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669383269026991410992057 2002037451770243558244043)
                      ·
                        rfl

theorem cell23_3898954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_3898954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898954 prefixEnd_3898954 := by exact prefixLift 3898954
  have htrace : WordTrace (prefixWord ++ tailWord_3898954) baseStart_3898954 baseEnd_3898954 := by
    simpa [prefixWord, tailWord_3898954, baseEnd_3898954] using wordTrace_append hprefix tailTrace_3898954
  have hstable : (prefixWord ++ tailWord_3898954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898954).length < 2 ^ (prefixWord ++ tailWord_3898954).sum := by decide
  have hdescent : baseEnd_3898954 < baseStart_3898954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898966 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3898966 : Nat := 118140960795 + 3898966 * 2 ^ 59
def prefixEnd_3898966 : Nat := 4983230072969 + 3 ^ 40 * 3898966 * 2
def baseEnd_3898966 : Nat := 2002043613538097511293989

theorem tailTrace_3898966 : CollatzResearch.WordTrace tailWord_3898966 prefixEnd_3898966 2002043613538097511293989 := by
  unfold tailWord_3898966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887935799544971701479297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94804648528479698149112501 8887935799544971701479297)
  ·
    refine ⟨6665951849658728776109473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8887935799544971701479297 6665951849658728776109473)
    ·
      refine ⟨4999463887244046582082105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6665951849658728776109473 4999463887244046582082105)
      ·
        refine ⟨3749597915433034936561579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4999463887244046582082105 3749597915433034936561579)
        ·
          refine ⟨5624396873149552404842369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749597915433034936561579 5624396873149552404842369)
          ·
            refine ⟨4218297654862164303631777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5624396873149552404842369 4218297654862164303631777)
            ·
              refine ⟨3163723241146623227723833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218297654862164303631777 3163723241146623227723833)
              ·
                refine ⟨2372792430859967420792875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3163723241146623227723833 2372792430859967420792875)
                ·
                  refine ⟨3559188646289951131189313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372792430859967420792875 3559188646289951131189313)
                  ·
                    refine ⟨2669391484717463348391985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559188646289951131189313 2669391484717463348391985)
                    ·
                      refine ⟨2002043613538097511293989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669391484717463348391985 2002043613538097511293989)
                      ·
                        rfl

theorem cell23_3898966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3898966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898966 prefixEnd_3898966 := by exact prefixLift 3898966
  have htrace : WordTrace (prefixWord ++ tailWord_3898966) baseStart_3898966 baseEnd_3898966 := by
    simpa [prefixWord, tailWord_3898966, baseEnd_3898966] using wordTrace_append hprefix tailTrace_3898966
  have hstable : (prefixWord ++ tailWord_3898966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898966).length < 2 ^ (prefixWord ++ tailWord_3898966).sum := by decide
  have hdescent : baseEnd_3898966 < baseStart_3898966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3898970 : Nat := 118140960795 + 3898970 * 2 ^ 59
def prefixEnd_3898970 : Nat := 4983230072969 + 3 ^ 40 * 3898970 * 2
def baseEnd_3898970 : Nat := 2002045667460715495643969

theorem tailTrace_3898970 : CollatzResearch.WordTrace tailWord_3898970 prefixEnd_3898970 2002045667460715495643969 := by
  unfold tailWord_3898970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35551779671176263976703591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94804745789803370604542909 35551779671176263976703591)
  ·
    refine ⟨53327669506764395965055387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35551779671176263976703591 53327669506764395965055387)
    ·
      refine ⟨79991504260146593947583081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53327669506764395965055387 79991504260146593947583081)
      ·
        refine ⟨59993628195109945460687311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79991504260146593947583081 59993628195109945460687311)
        ·
          refine ⟨89990442292664918191030967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59993628195109945460687311 89990442292664918191030967)
          ·
            refine ⟨134985663438997377286546451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89990442292664918191030967 134985663438997377286546451)
            ·
              refine ⟨202478495158496065929819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134985663438997377286546451 202478495158496065929819677)
              ·
                refine ⟨75929435684436024723682379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202478495158496065929819677 75929435684436024723682379)
                ·
                  refine ⟨113894153526654037085523569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75929435684436024723682379 113894153526654037085523569)
                  ·
                    refine ⟨85420615144990527814142677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113894153526654037085523569 85420615144990527814142677)
                    ·
                      refine ⟨2002045667460715495643969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85420615144990527814142677 2002045667460715495643969)
                      ·
                        rfl

theorem cell23_3898970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3898970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898970 prefixEnd_3898970 := by exact prefixLift 3898970
  have htrace : WordTrace (prefixWord ++ tailWord_3898970) baseStart_3898970 baseEnd_3898970 := by
    simpa [prefixWord, tailWord_3898970, baseEnd_3898970] using wordTrace_append hprefix tailTrace_3898970
  have hstable : (prefixWord ++ tailWord_3898970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898970).length < 2 ^ (prefixWord ++ tailWord_3898970).sum := by decide
  have hdescent : baseEnd_3898970 < baseStart_3898970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3898984 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3898984 : Nat := 118140960795 + 3898984 * 2 ^ 59
def prefixEnd_3898984 : Nat := 4983230072969 + 3 ^ 40 * 3898984 * 2
def baseEnd_3898984 : Nat := 2002052856189878440868905

theorem tailTrace_3898984 : CollatzResearch.WordTrace tailWord_3898984 prefixEnd_3898984 2002052856189878440868905 := by
  unfold tailWord_3898984
  simp only [CollatzResearch.WordTrace]
  refine ⟨71103814653327168148912003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94805086204436224198549337 71103814653327168148912003)
  ·
    refine ⟨106655721979990752223368005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71103814653327168148912003 106655721979990752223368005)
    ·
      refine ⟨19997947871248266041881501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106655721979990752223368005 19997947871248266041881501)
      ·
        refine ⟨7499230451718099765705563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19997947871248266041881501 7499230451718099765705563)
        ·
          refine ⟨11248845677577149648558345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499230451718099765705563 11248845677577149648558345)
          ·
            refine ⟨8436634258182862236418759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11248845677577149648558345 8436634258182862236418759)
            ·
              refine ⟨12654951387274293354628139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8436634258182862236418759 12654951387274293354628139)
              ·
                refine ⟨18982427080911440031942209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12654951387274293354628139 18982427080911440031942209)
                ·
                  refine ⟨14236820310683580023956657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18982427080911440031942209 14236820310683580023956657)
                  ·
                    refine ⟨10677615233012685017967493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14236820310683580023956657 10677615233012685017967493)
                    ·
                      refine ⟨2002052856189878440868905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10677615233012685017967493 2002052856189878440868905)
                      ·
                        rfl

theorem cell23_3898984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3898984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3898984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3898984 prefixEnd_3898984 := by exact prefixLift 3898984
  have htrace : WordTrace (prefixWord ++ tailWord_3898984) baseStart_3898984 baseEnd_3898984 := by
    simpa [prefixWord, tailWord_3898984, baseEnd_3898984] using wordTrace_append hprefix tailTrace_3898984
  have hstable : (prefixWord ++ tailWord_3898984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3898984).length < 2 ^ (prefixWord ++ tailWord_3898984).sum := by decide
  have hdescent : baseEnd_3898984 < baseStart_3898984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3898984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899077 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_3899077 : Nat := 118140960795 + 3899077 * 2 ^ 59
def prefixEnd_3899077 : Nat := 4983230072969 + 3 ^ 40 * 3899077 * 2
def baseEnd_3899077 : Nat := 2002100609890746577005977

theorem tailTrace_3899077 : CollatzResearch.WordTrace tailWord_3899077 prefixEnd_3899077 2002100609890746577005977 := by
  unfold tailWord_3899077
  simp only [CollatzResearch.WordTrace]
  refine ⟨142211021295317413180959485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94807347530211608787306323 142211021295317413180959485)
  ·
    refine ⟨53329132985744029942859807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142211021295317413180959485 53329132985744029942859807)
    ·
      refine ⟨79993699478616044914289711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53329132985744029942859807 79993699478616044914289711)
      ·
        refine ⟨119990549217924067371434567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79993699478616044914289711 119990549217924067371434567)
        ·
          refine ⟨179985823826886101057151851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119990549217924067371434567 179985823826886101057151851)
          ·
            refine ⟨269978735740329151585727777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179985823826886101057151851 269978735740329151585727777)
            ·
              refine ⟨202484051805246863689295833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269978735740329151585727777 202484051805246863689295833)
              ·
                refine ⟨151863038853935147766971875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202484051805246863689295833 151863038853935147766971875)
                ·
                  refine ⟨227794558280902721650457813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151863038853935147766971875 227794558280902721650457813)
                  ·
                    refine ⟨5338934959708657538682605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227794558280902721650457813 5338934959708657538682605)
                    ·
                      refine ⟨2002100609890746577005977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5338934959708657538682605 2002100609890746577005977)
                      ·
                        rfl

theorem cell23_3899077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_3899077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899077 prefixEnd_3899077 := by exact prefixLift 3899077
  have htrace : WordTrace (prefixWord ++ tailWord_3899077) baseStart_3899077 baseEnd_3899077 := by
    simpa [prefixWord, tailWord_3899077, baseEnd_3899077] using wordTrace_append hprefix tailTrace_3899077
  have hstable : (prefixWord ++ tailWord_3899077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899077).length < 2 ^ (prefixWord ++ tailWord_3899077).sum := by decide
  have hdescent : baseEnd_3899077 < baseStart_3899077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899078 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3899078 : Nat := 118140960795 + 3899078 * 2 ^ 59
def prefixEnd_3899078 : Nat := 4983230072969 + 3 ^ 40 * 3899078 * 2
def baseEnd_3899078 : Nat := 2002101123371401073093473

theorem tailTrace_3899078 : CollatzResearch.WordTrace tailWord_3899078 prefixEnd_3899078 2002101123371401073093473 := by
  unfold tailWord_3899078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4444095555259805948492059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94807371845542526901163925 4444095555259805948492059)
  ·
    refine ⟨6666143332889708922738089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4444095555259805948492059 6666143332889708922738089)
    ·
      refine ⟨4999607499667281692053567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6666143332889708922738089 4999607499667281692053567)
      ·
        refine ⟨7499411249500922538080351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999607499667281692053567 7499411249500922538080351)
        ·
          refine ⟨11249116874251383807120527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7499411249500922538080351 11249116874251383807120527)
          ·
            refine ⟨16873675311377075710680791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11249116874251383807120527 16873675311377075710680791)
            ·
              refine ⟨25310512967065613566021187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16873675311377075710680791 25310512967065613566021187)
              ·
                refine ⟨37965769450598420349031781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25310512967065613566021187 37965769450598420349031781)
                ·
                  refine ⟨7118581771987203815443459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37965769450598420349031781 7118581771987203815443459)
                  ·
                    refine ⟨10677872657980805723165189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7118581771987203815443459 10677872657980805723165189)
                    ·
                      refine ⟨2002101123371401073093473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10677872657980805723165189 2002101123371401073093473)
                      ·
                        rfl

theorem cell23_3899078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3899078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899078 prefixEnd_3899078 := by exact prefixLift 3899078
  have htrace : WordTrace (prefixWord ++ tailWord_3899078) baseStart_3899078 baseEnd_3899078 := by
    simpa [prefixWord, tailWord_3899078, baseEnd_3899078] using wordTrace_append hprefix tailTrace_3899078
  have hstable : (prefixWord ++ tailWord_3899078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899078).length < 2 ^ (prefixWord ++ tailWord_3899078).sum := by decide
  have hdescent : baseEnd_3899078 < baseStart_3899078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899104 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2]
def baseStart_3899104 : Nat := 118140960795 + 3899104 * 2 ^ 59
def prefixEnd_3899104 : Nat := 4983230072969 + 3 ^ 40 * 3899104 * 2
def baseEnd_3899104 : Nat := 2002114473868417971368353

theorem tailTrace_3899104 : CollatzResearch.WordTrace tailWord_3899104 prefixEnd_3899104 2002114473868417971368353 := by
  unfold tailWord_3899104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71106003033109798396096183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94808004044146397861461577 71106003033109798396096183)
  ·
    refine ⟨106659004549664697594144275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71106003033109798396096183 106659004549664697594144275)
    ·
      refine ⟨159988506824497046391216413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106659004549664697594144275 159988506824497046391216413)
      ·
        refine ⟨59995690059186392396706155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159988506824497046391216413 59995690059186392396706155)
        ·
          refine ⟨89993535088779588595059233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59995690059186392396706155 89993535088779588595059233)
          ·
            refine ⟨67495151316584691446294425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89993535088779588595059233 67495151316584691446294425)
            ·
              refine ⟨50621363487438518584720819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67495151316584691446294425 50621363487438518584720819)
              ·
                refine ⟨75932045231157777877081229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50621363487438518584720819 75932045231157777877081229)
                ·
                  refine ⟨28474516961684166703905461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75932045231157777877081229 28474516961684166703905461)
                  ·
                    refine ⟨2669485965157890628491137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28474516961684166703905461 2669485965157890628491137)
                    ·
                      refine ⟨2002114473868417971368353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669485965157890628491137 2002114473868417971368353)
                      ·
                        rfl

theorem cell23_3899104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_3899104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899104 prefixEnd_3899104 := by exact prefixLift 3899104
  have htrace : WordTrace (prefixWord ++ tailWord_3899104) baseStart_3899104 baseEnd_3899104 := by
    simpa [prefixWord, tailWord_3899104, baseEnd_3899104] using wordTrace_append hprefix tailTrace_3899104
  have hstable : (prefixWord ++ tailWord_3899104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899104).length < 2 ^ (prefixWord ++ tailWord_3899104).sum := by decide
  have hdescent : baseEnd_3899104 < baseStart_3899104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899121 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_3899121 : Nat := 118140960795 + 3899121 * 2 ^ 59
def prefixEnd_3899121 : Nat := 4983230072969 + 3 ^ 40 * 3899121 * 2
def baseEnd_3899121 : Nat := 2002123203039544404855775

theorem tailTrace_3899121 : CollatzResearch.WordTrace tailWord_3899121 prefixEnd_3899121 2002123203039544404855775 := by
  unfold tailWord_3899121
  simp only [CollatzResearch.WordTrace]
  refine ⟨142212626107158008695561217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94808417404772005797040811 142212626107158008695561217)
  ·
    refine ⟨106659469580368506521670913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142212626107158008695561217 106659469580368506521670913)
    ·
      refine ⟨79994602185276379891253185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106659469580368506521670913 79994602185276379891253185)
      ·
        refine ⟨59995951638957284918439889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79994602185276379891253185 59995951638957284918439889)
        ·
          refine ⟨44996963729217963688829917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59995951638957284918439889 44996963729217963688829917)
          ·
            refine ⟨16873861398456736383311219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44996963729217963688829917 16873861398456736383311219)
            ·
              refine ⟨25310792097685104574966829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16873861398456736383311219 25310792097685104574966829)
              ·
                refine ⟨9491547036631914215612561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25310792097685104574966829 9491547036631914215612561)
                ·
                  refine ⟨7118660277473935661709421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491547036631914215612561 7118660277473935661709421)
                  ·
                    refine ⟨2669497604052725873141033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7118660277473935661709421 2669497604052725873141033)
                    ·
                      refine ⟨2002123203039544404855775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669497604052725873141033 2002123203039544404855775)
                      ·
                        rfl

theorem cell23_3899121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_3899121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899121 prefixEnd_3899121 := by exact prefixLift 3899121
  have htrace : WordTrace (prefixWord ++ tailWord_3899121) baseStart_3899121 baseEnd_3899121 := by
    simpa [prefixWord, tailWord_3899121, baseEnd_3899121] using wordTrace_append hprefix tailTrace_3899121
  have hstable : (prefixWord ++ tailWord_3899121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899121).length < 2 ^ (prefixWord ++ tailWord_3899121).sum := by decide
  have hdescent : baseEnd_3899121 < baseStart_3899121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899127 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 6]
def baseStart_3899127 : Nat := 118140960795 + 3899127 * 2 ^ 59
def prefixEnd_3899127 : Nat := 4983230072969 + 3 ^ 40 * 3899127 * 2
def baseEnd_3899127 : Nat := 667375427974490460460249

theorem tailTrace_3899127 : CollatzResearch.WordTrace tailWord_3899127 prefixEnd_3899127 667375427974490460460249 := by
  unfold tailWord_3899127
  simp only [CollatzResearch.WordTrace]
  refine ⟨142212844945136271720279635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94808563296757514480186423 142212844945136271720279635)
  ·
    refine ⟨213319267417704407580419453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142212844945136271720279635 213319267417704407580419453)
    ·
      refine ⟨79994725281639152842657295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213319267417704407580419453 79994725281639152842657295)
      ·
        refine ⟨119992087922458729263985943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79994725281639152842657295 119992087922458729263985943)
        ·
          refine ⟨179988131883688093895978915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119992087922458729263985943 179988131883688093895978915)
          ·
            refine ⟨269982197825532140843968373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179988131883688093895978915 269982197825532140843968373)
            ·
              refine ⟨25310831046143638204122035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269982197825532140843968373 25310831046143638204122035)
              ·
                refine ⟨37966246569215457306183053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25310831046143638204122035 37966246569215457306183053)
                ·
                  refine ⟨14237342463455796489818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37966246569215457306183053 14237342463455796489818645)
                  ·
                    refine ⟨667375427974490460460249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14237342463455796489818645 667375427974490460460249)
                    ·
                      rfl

theorem cell23_3899127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_3899127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899127 prefixEnd_3899127 := by exact prefixLift 3899127
  have htrace : WordTrace (prefixWord ++ tailWord_3899127) baseStart_3899127 baseEnd_3899127 := by
    simpa [prefixWord, tailWord_3899127, baseEnd_3899127] using wordTrace_append hprefix tailTrace_3899127
  have hstable : (prefixWord ++ tailWord_3899127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899127).length < 2 ^ (prefixWord ++ tailWord_3899127).sum := by decide
  have hdescent : baseEnd_3899127 < baseStart_3899127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899138 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_3899138 : Nat := 118140960795 + 3899138 * 2 ^ 59
def prefixEnd_3899138 : Nat := 4983230072969 + 3 ^ 40 * 3899138 * 2
def baseEnd_3899138 : Nat := 2002131932210670838343197

theorem tailTrace_3899138 : CollatzResearch.WordTrace tailWord_3899138 prefixEnd_3899138 2002131932210670838343197 := by
  unfold tailWord_3899138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35553311537024105149732517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94808830765397613732620045 35553311537024105149732517)
  ·
    refine ⟨6666245913192019715574847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35553311537024105149732517 6666245913192019715574847)
    ·
      refine ⟨9999368869788029573362271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6666245913192019715574847 9999368869788029573362271)
      ·
        refine ⟨14999053304682044360043407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9999368869788029573362271 14999053304682044360043407)
        ·
          refine ⟨22498579957023066540065111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999053304682044360043407 22498579957023066540065111)
          ·
            refine ⟨33747869935534599810097667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22498579957023066540065111 33747869935534599810097667)
            ·
              refine ⟨50621804903301899715146501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33747869935534599810097667 50621804903301899715146501)
              ·
                refine ⟨9491588419369106196589969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50621804903301899715146501 9491588419369106196589969)
                ·
                  refine ⟨7118691314526829647442477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9491588419369106196589969 7118691314526829647442477)
                  ·
                    refine ⟨2669509242947561117790929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7118691314526829647442477 2669509242947561117790929)
                    ·
                      refine ⟨2002131932210670838343197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669509242947561117790929 2002131932210670838343197)
                      ·
                        rfl

theorem cell23_3899138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_3899138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899138 prefixEnd_3899138 := by exact prefixLift 3899138
  have htrace : WordTrace (prefixWord ++ tailWord_3899138) baseStart_3899138 baseEnd_3899138 := by
    simpa [prefixWord, tailWord_3899138, baseEnd_3899138] using wordTrace_append hprefix tailTrace_3899138
  have hstable : (prefixWord ++ tailWord_3899138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899138).length < 2 ^ (prefixWord ++ tailWord_3899138).sum := by decide
  have hdescent : baseEnd_3899138 < baseStart_3899138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899147 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_3899147 : Nat := 118140960795 + 3899147 * 2 ^ 59
def prefixEnd_3899147 : Nat := 4983230072969 + 3 ^ 40 * 3899147 * 2
def baseEnd_3899147 : Nat := 2002136553536561303130655

theorem tailTrace_3899147 : CollatzResearch.WordTrace tailWord_3899147 prefixEnd_3899147 2002136553536561303130655 := by
  unfold tailWord_3899147
  simp only [CollatzResearch.WordTrace]
  refine ⟨142213574405063815136007695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94809049603375876757338463 142213574405063815136007695)
  ·
    refine ⟨213320361607595722704011543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142213574405063815136007695 213320361607595722704011543)
    ·
      refine ⟨319980542411393584056017315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213320361607595722704011543 319980542411393584056017315)
      ·
        refine ⟨479970813617090376084025973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319980542411393584056017315 479970813617090376084025973)
        ·
          refine ⟨44997263776602222757877435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 479970813617090376084025973 44997263776602222757877435)
          ·
            refine ⟨67495895664903334136816153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44997263776602222757877435 67495895664903334136816153)
            ·
              refine ⟨50621921748677500602612115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67495895664903334136816153 50621921748677500602612115)
              ·
                refine ⟨75932882623016250903918173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50621921748677500602612115 75932882623016250903918173)
                ·
                  refine ⟨28474830983631094088969315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75932882623016250903918173 28474830983631094088969315)
                  ·
                    refine ⟨42712246475446641133453973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28474830983631094088969315 42712246475446641133453973)
                    ·
                      refine ⟨2002136553536561303130655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42712246475446641133453973 2002136553536561303130655)
                      ·
                        rfl

theorem cell23_3899147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_3899147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899147 prefixEnd_3899147 := by exact prefixLift 3899147
  have htrace : WordTrace (prefixWord ++ tailWord_3899147) baseStart_3899147 baseEnd_3899147 := by
    simpa [prefixWord, tailWord_3899147, baseEnd_3899147] using wordTrace_append hprefix tailTrace_3899147
  have hstable : (prefixWord ++ tailWord_3899147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899147).length < 2 ^ (prefixWord ++ tailWord_3899147).sum := by decide
  have hdescent : baseEnd_3899147 < baseStart_3899147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899168 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3899168 : Nat := 118140960795 + 3899168 * 2 ^ 59
def prefixEnd_3899168 : Nat := 4983230072969 + 3 ^ 40 * 3899168 * 2
def baseEnd_3899168 : Nat := 2002147336630305720968059

theorem tailTrace_3899168 : CollatzResearch.WordTrace tailWord_3899168 prefixEnd_3899168 2002147336630305720968059 := by
  unfold tailWord_3899168
  simp only [CollatzResearch.WordTrace]
  refine ⟨71107170168993867861261079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94809560225325157148348105 71107170168993867861261079)
  ·
    refine ⟨106660755253490801791891619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71107170168993867861261079 106660755253490801791891619)
    ·
      refine ⟨159991132880236202687837429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106660755253490801791891619 159991132880236202687837429)
      ·
        refine ⟨14999168707522144001984759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159991132880236202687837429 14999168707522144001984759)
        ·
          refine ⟨22498753061283216002977139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999168707522144001984759 22498753061283216002977139)
          ·
            refine ⟨33748129591924824004465709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22498753061283216002977139 33748129591924824004465709)
            ·
              refine ⟨12655548596971809001674641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33748129591924824004465709 12655548596971809001674641)
              ·
                refine ⟨9491661447728856751255981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12655548596971809001674641 9491661447728856751255981)
                ·
                  refine ⟨3559373042898321281720993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9491661447728856751255981 3559373042898321281720993)
                  ·
                    refine ⟨2669529782173740961290745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559373042898321281720993 2669529782173740961290745)
                    ·
                      refine ⟨2002147336630305720968059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669529782173740961290745 2002147336630305720968059)
                      ·
                        rfl

theorem cell23_3899168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3899168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899168 prefixEnd_3899168 := by exact prefixLift 3899168
  have htrace : WordTrace (prefixWord ++ tailWord_3899168) baseStart_3899168 baseEnd_3899168 := by
    simpa [prefixWord, tailWord_3899168, baseEnd_3899168] using wordTrace_append hprefix tailTrace_3899168
  have hstable : (prefixWord ++ tailWord_3899168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899168).length < 2 ^ (prefixWord ++ tailWord_3899168).sum := by decide
  have hdescent : baseEnd_3899168 < baseStart_3899168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899182 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3899182 : Nat := 118140960795 + 3899182 * 2 ^ 59
def prefixEnd_3899182 : Nat := 4983230072969 + 3 ^ 40 * 3899182 * 2
def baseEnd_3899182 : Nat := 667384841786489555397665

theorem tailTrace_3899182 : CollatzResearch.WordTrace tailWord_3899182 prefixEnd_3899182 667384841786489555397665 := by
  unfold tailWord_3899182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776856369992127014191475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94809900639958010742354533 17776856369992127014191475)
  ·
    refine ⟨26665284554988190521287213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17776856369992127014191475 26665284554988190521287213)
    ·
      refine ⟨9999481708120571445482705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26665284554988190521287213 9999481708120571445482705)
      ·
        refine ⟨7499611281090428584112029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9999481708120571445482705 7499611281090428584112029)
        ·
          refine ⟨2812354230408910719042011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7499611281090428584112029 2812354230408910719042011)
          ·
            refine ⟨4218531345613366078563017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812354230408910719042011 4218531345613366078563017)
            ·
              refine ⟨3163898509210024558922263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218531345613366078563017 3163898509210024558922263)
              ·
                refine ⟨4745847763815036838383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3163898509210024558922263 4745847763815036838383395)
                ·
                  refine ⟨7118771645722555257575093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4745847763815036838383395 7118771645722555257575093)
                  ·
                    refine ⟨667384841786489555397665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7118771645722555257575093 667384841786489555397665)
                    ·
                      rfl

theorem cell23_3899182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3899182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899182 prefixEnd_3899182 := by exact prefixLift 3899182
  have htrace : WordTrace (prefixWord ++ tailWord_3899182) baseStart_3899182 baseEnd_3899182 := by
    simpa [prefixWord, tailWord_3899182, baseEnd_3899182] using wordTrace_append hprefix tailTrace_3899182
  have hstable : (prefixWord ++ tailWord_3899182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899182).length < 2 ^ (prefixWord ++ tailWord_3899182).sum := by decide
  have hdescent : baseEnd_3899182 < baseStart_3899182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899185 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_3899185 : Nat := 118140960795 + 3899185 * 2 ^ 59
def prefixEnd_3899185 : Nat := 4983230072969 + 3 ^ 40 * 3899185 * 2
def baseEnd_3899185 : Nat := 2002156065801432154455481

theorem tailTrace_3899185 : CollatzResearch.WordTrace tailWord_3899185 prefixEnd_3899185 2002156065801432154455481 := by
  unfold tailWord_3899185
  simp only [CollatzResearch.WordTrace]
  refine ⟨142214960378926147625891009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94809973585950765083927339 142214960378926147625891009)
  ·
    refine ⟨106661220284194610719418257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142214960378926147625891009 106661220284194610719418257)
    ·
      refine ⟨79995915213145958039563693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106661220284194610719418257 79995915213145958039563693)
      ·
        refine ⟨29998468204929734264836385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79995915213145958039563693 29998468204929734264836385)
        ·
          refine ⟨22498851153697300698627289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29998468204929734264836385 22498851153697300698627289)
          ·
            refine ⟨16874138365272975523970467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22498851153697300698627289 16874138365272975523970467)
            ·
              refine ⟨25311207547909463285955701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16874138365272975523970467 25311207547909463285955701)
              ·
                refine ⟨2372925707616512183058347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25311207547909463285955701 2372925707616512183058347)
                ·
                  refine ⟨3559388561424768274587521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2372925707616512183058347 3559388561424768274587521)
                  ·
                    refine ⟨2669541421068576205940641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559388561424768274587521 2669541421068576205940641)
                    ·
                      refine ⟨2002156065801432154455481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669541421068576205940641 2002156065801432154455481)
                      ·
                        rfl

theorem cell23_3899185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_3899185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899185 prefixEnd_3899185 := by exact prefixLift 3899185
  have htrace : WordTrace (prefixWord ++ tailWord_3899185) baseStart_3899185 baseEnd_3899185 := by
    simpa [prefixWord, tailWord_3899185, baseEnd_3899185] using wordTrace_append hprefix tailTrace_3899185
  have hstable : (prefixWord ++ tailWord_3899185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899185).length < 2 ^ (prefixWord ++ tailWord_3899185).sum := by decide
  have hdescent : baseEnd_3899185 < baseStart_3899185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899218 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3899218 : Nat := 118140960795 + 3899218 * 2 ^ 59
def prefixEnd_3899218 : Nat := 4983230072969 + 3 ^ 40 * 3899218 * 2
def baseEnd_3899218 : Nat := 2002173010663030525342829

theorem tailTrace_3899218 : CollatzResearch.WordTrace tailWord_3899218 prefixEnd_3899218 2002173010663030525342829 := by
  unfold tailWord_3899218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35554040996951648565460577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94810775991871062841228205 35554040996951648565460577)
  ·
    refine ⟨26665530747713736424095433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35554040996951648565460577 26665530747713736424095433)
    ·
      refine ⟨19999148060785302318071575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26665530747713736424095433 19999148060785302318071575)
      ·
        refine ⟨29998722091177953477107363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19999148060785302318071575 29998722091177953477107363)
        ·
          refine ⟨44998083136766930215661045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29998722091177953477107363 44998083136766930215661045)
          ·
            refine ⟨4218570294071899707718223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44998083136766930215661045 4218570294071899707718223)
            ·
              refine ⟨6327855441107849561577335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218570294071899707718223 6327855441107849561577335)
              ·
                refine ⟨9491783161661774342366003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6327855441107849561577335 9491783161661774342366003)
                ·
                  refine ⟨14237674742492661513549005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491783161661774342366003 14237674742492661513549005)
                  ·
                    refine ⟨5339128028434748067580877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14237674742492661513549005 5339128028434748067580877)
                    ·
                      refine ⟨2002173010663030525342829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339128028434748067580877 2002173010663030525342829)
                      ·
                        rfl

theorem cell23_3899218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3899218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899218 prefixEnd_3899218 := by exact prefixLift 3899218
  have htrace : WordTrace (prefixWord ++ tailWord_3899218) baseStart_3899218 baseEnd_3899218 := by
    simpa [prefixWord, tailWord_3899218, baseEnd_3899218] using wordTrace_append hprefix tailTrace_3899218
  have hstable : (prefixWord ++ tailWord_3899218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899218).length < 2 ^ (prefixWord ++ tailWord_3899218).sum := by decide
  have hdescent : baseEnd_3899218 < baseStart_3899218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899241 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 4, 2]
def baseStart_3899241 : Nat := 118140960795 + 3899241 * 2 ^ 59
def prefixEnd_3899241 : Nat := 4983230072969 + 3 ^ 40 * 3899241 * 2
def baseEnd_3899241 : Nat := 2002184820718083935355223

theorem tailTrace_3899241 : CollatzResearch.WordTrace tailWord_3899241 prefixEnd_3899241 2002184820718083935355223 := by
  unfold tailWord_3899241
  simp only [CollatzResearch.WordTrace]
  refine ⟨142217002866723269189929577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94811335244482179459953051 142217002866723269189929577)
  ·
    refine ⟨106662752150042451892447183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142217002866723269189929577 106662752150042451892447183)
    ·
      refine ⟨159994128225063677838670775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106662752150042451892447183 159994128225063677838670775)
      ·
        refine ⟨239991192337595516758006163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159994128225063677838670775 239991192337595516758006163)
        ·
          refine ⟨359986788506393275137009245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239991192337595516758006163 359986788506393275137009245)
          ·
            refine ⟨134995045689897478176378467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359986788506393275137009245 134995045689897478176378467)
            ·
              refine ⟨202492568534846217264567701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134995045689897478176378467 202492568534846217264567701)
              ·
                refine ⟨9491839150070916434276611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202492568534846217264567701 9491839150070916434276611)
                ·
                  refine ⟨14237758725106374651414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9491839150070916434276611 14237758725106374651414917)
                  ·
                    refine ⟨2669579760957445247140297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14237758725106374651414917 2669579760957445247140297)
                    ·
                      refine ⟨2002184820718083935355223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669579760957445247140297 2002184820718083935355223)
                      ·
                        rfl

theorem cell23_3899241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4, 2].length) (baseStart_3899241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899241 prefixEnd_3899241 := by exact prefixLift 3899241
  have htrace : WordTrace (prefixWord ++ tailWord_3899241) baseStart_3899241 baseEnd_3899241 := by
    simpa [prefixWord, tailWord_3899241, baseEnd_3899241] using wordTrace_append hprefix tailTrace_3899241
  have hstable : (prefixWord ++ tailWord_3899241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899241).length < 2 ^ (prefixWord ++ tailWord_3899241).sum := by decide
  have hdescent : baseEnd_3899241 < baseStart_3899241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899244 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_3899244 : Nat := 118140960795 + 3899244 * 2 ^ 59
def prefixEnd_3899244 : Nat := 4983230072969 + 3 ^ 40 * 3899244 * 2
def baseEnd_3899244 : Nat := 2002186361160047423617709

theorem tailTrace_3899244 : CollatzResearch.WordTrace tailWord_3899244 prefixEnd_3899244 2002186361160047423617709 := by
  unfold tailWord_3899244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71108556142856200351144393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94811408190474933801525857 71108556142856200351144393)
  ·
    refine ⟨53331417107142150263358295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71108556142856200351144393 53331417107142150263358295)
    ·
      refine ⟨79997125660713225395037443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331417107142150263358295 79997125660713225395037443)
      ·
        refine ⟨119995688491069838092556165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79997125660713225395037443 119995688491069838092556165)
        ·
          refine ⟨22499191592075594642354281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119995688491069838092556165 22499191592075594642354281)
          ·
            refine ⟨16874393694056695981765711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22499191592075594642354281 16874393694056695981765711)
            ·
              refine ⟨25311590541085043972648567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16874393694056695981765711 25311590541085043972648567)
              ·
                refine ⟨37967385811627565958972851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25311590541085043972648567 37967385811627565958972851)
                ·
                  refine ⟨56951078717441348938459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37967385811627565958972851 56951078717441348938459277)
                  ·
                    refine ⟨21356654519040505851922229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56951078717441348938459277 21356654519040505851922229)
                    ·
                      refine ⟨2002186361160047423617709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21356654519040505851922229 2002186361160047423617709)
                      ·
                        rfl

theorem cell23_3899244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_3899244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899244 prefixEnd_3899244 := by exact prefixLift 3899244
  have htrace : WordTrace (prefixWord ++ tailWord_3899244) baseStart_3899244 baseEnd_3899244 := by
    simpa [prefixWord, tailWord_3899244, baseEnd_3899244] using wordTrace_append hprefix tailTrace_3899244
  have hstable : (prefixWord ++ tailWord_3899244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899244).length < 2 ^ (prefixWord ++ tailWord_3899244).sum := by decide
  have hdescent : baseEnd_3899244 < baseStart_3899244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899258 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_3899258 : Nat := 118140960795 + 3899258 * 2 ^ 59
def prefixEnd_3899258 : Nat := 4983230072969 + 3 ^ 40 * 3899258 * 2
def baseEnd_3899258 : Nat := 2002193549889210368842645

theorem tailTrace_3899258 : CollatzResearch.WordTrace tailWord_3899258 prefixEnd_3899258 2002193549889210368842645 := by
  unfold tailWord_3899258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35554405726915420273324607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94811748605107787395532285 35554405726915420273324607)
  ·
    refine ⟨53331608590373130409986911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35554405726915420273324607 53331608590373130409986911)
    ·
      refine ⟨79997412885559695614980367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331608590373130409986911 79997412885559695614980367)
      ·
        refine ⟨119996119328339543422470551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79997412885559695614980367 119996119328339543422470551)
        ·
          refine ⟨179994178992509315133705827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119996119328339543422470551 179994178992509315133705827)
          ·
            refine ⟨269991268488763972700558741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179994178992509315133705827 269991268488763972700558741)
            ·
              refine ⟨12655840710410811220338691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269991268488763972700558741 12655840710410811220338691)
              ·
                refine ⟨18983761065616216830508037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12655840710410811220338691 18983761065616216830508037)
                ·
                  refine ⟨3559455199803040655720257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18983761065616216830508037 3559455199803040655720257)
                  ·
                    refine ⟨2669591399852280491790193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559455199803040655720257 2669591399852280491790193)
                    ·
                      refine ⟨2002193549889210368842645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669591399852280491790193 2002193549889210368842645)
                      ·
                        rfl

theorem cell23_3899258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_3899258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899258 prefixEnd_3899258 := by exact prefixLift 3899258
  have htrace : WordTrace (prefixWord ++ tailWord_3899258) baseStart_3899258 baseEnd_3899258 := by
    simpa [prefixWord, tailWord_3899258, baseEnd_3899258] using wordTrace_append hprefix tailTrace_3899258
  have hstable : (prefixWord ++ tailWord_3899258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899258).length < 2 ^ (prefixWord ++ tailWord_3899258).sum := by decide
  have hdescent : baseEnd_3899258 < baseStart_3899258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899301 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_3899301 : Nat := 118140960795 + 3899301 * 2 ^ 59
def prefixEnd_3899301 : Nat := 4983230072969 + 3 ^ 40 * 3899301 * 2
def baseEnd_3899301 : Nat := 2002215629557353700604947

theorem tailTrace_3899301 : CollatzResearch.WordTrace tailWord_3899301 prefixEnd_3899301 2002215629557353700604947 := by
  unfold tailWord_3899301
  simp only [CollatzResearch.WordTrace]
  refine ⟨142219191246505899437113757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94812794164337266291409171 142219191246505899437113757)
  ·
    refine ⟨53332196717439712288917659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142219191246505899437113757 53332196717439712288917659)
    ·
      refine ⟨79998295076159568433376489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53332196717439712288917659 79998295076159568433376489)
      ·
        refine ⟨59998721307119676325032367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79998295076159568433376489 59998721307119676325032367)
        ·
          refine ⟨89998081960679514487548551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59998721307119676325032367 89998081960679514487548551)
          ·
            refine ⟨134997122941019271731322827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89998081960679514487548551 134997122941019271731322827)
            ·
              refine ⟨202495684411528907596984241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134997122941019271731322827 202495684411528907596984241)
              ·
                refine ⟨151871763308646680697738181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202495684411528907596984241 151871763308646680697738181)
                ·
                  refine ⟨28475955620371252630825909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151871763308646680697738181 28475955620371252630825909)
                  ·
                    refine ⟨2669620839409804934139929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28475955620371252630825909 2669620839409804934139929)
                    ·
                      refine ⟨2002215629557353700604947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669620839409804934139929 2002215629557353700604947)
                      ·
                        rfl

theorem cell23_3899301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_3899301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899301 prefixEnd_3899301 := by exact prefixLift 3899301
  have htrace : WordTrace (prefixWord ++ tailWord_3899301) baseStart_3899301 baseEnd_3899301 := by
    simpa [prefixWord, tailWord_3899301, baseEnd_3899301] using wordTrace_append hprefix tailTrace_3899301
  have hstable : (prefixWord ++ tailWord_3899301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899301).length < 2 ^ (prefixWord ++ tailWord_3899301).sum := by decide
  have hdescent : baseEnd_3899301 < baseStart_3899301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899348 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_3899348 : Nat := 118140960795 + 3899348 * 2 ^ 59
def prefixEnd_3899348 : Nat := 4983230072969 + 3 ^ 40 * 3899348 * 2
def baseEnd_3899348 : Nat := 2002239763148115016717231

theorem tailTrace_3899348 : CollatzResearch.WordTrace tailWord_3899348 prefixEnd_3899348 2002239763148115016717231 := by
  unfold tailWord_3899348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71110452738667813232037349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94813936984890417642716465 71110452738667813232037349)
  ·
    refine ⟨13333209888500214981007003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71110452738667813232037349 13333209888500214981007003)
    ·
      refine ⟨19999814832750322471510505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13333209888500214981007003 19999814832750322471510505)
      ·
        refine ⟨14999861124562741853632879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19999814832750322471510505 14999861124562741853632879)
        ·
          refine ⟨22499791686844112780449319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14999861124562741853632879 22499791686844112780449319)
          ·
            refine ⟨33749687530266169170673979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22499791686844112780449319 33749687530266169170673979)
            ·
              refine ⟨50624531295399253756010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33749687530266169170673979 50624531295399253756010969)
              ·
                refine ⟨37968398471549440317008227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50624531295399253756010969 37968398471549440317008227)
                ·
                  refine ⟨56952597707324160475512341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37968398471549440317008227 56952597707324160475512341)
                  ·
                    refine ⟨2669653017530820022289641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56952597707324160475512341 2669653017530820022289641)
                    ·
                      refine ⟨2002239763148115016717231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669653017530820022289641 2002239763148115016717231)
                      ·
                        rfl

theorem cell23_3899348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_3899348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899348 prefixEnd_3899348 := by exact prefixLift 3899348
  have htrace : WordTrace (prefixWord ++ tailWord_3899348) baseStart_3899348 baseEnd_3899348 := by
    simpa [prefixWord, tailWord_3899348, baseEnd_3899348] using wordTrace_append hprefix tailTrace_3899348
  have hstable : (prefixWord ++ tailWord_3899348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899348).length < 2 ^ (prefixWord ++ tailWord_3899348).sum := by decide
  have hdescent : baseEnd_3899348 < baseStart_3899348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899351 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_3899351 : Nat := 118140960795 + 3899351 * 2 ^ 59
def prefixEnd_3899351 : Nat := 4983230072969 + 3 ^ 40 * 3899351 * 2
def baseEnd_3899351 : Nat := 2002241303590078504979717

theorem tailTrace_3899351 : CollatzResearch.WordTrace tailWord_3899351 prefixEnd_3899351 2002241303590078504979717 := by
  unfold tailWord_3899351
  simp only [CollatzResearch.WordTrace]
  refine ⟨142221014896324757976433907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94814009930883171984289271 142221014896324757976433907)
  ·
    refine ⟨213331522344487136964650861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142221014896324757976433907 213331522344487136964650861)
    ·
      refine ⟨79999320879182676361744073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213331522344487136964650861 79999320879182676361744073)
      ·
        refine ⟨59999490659387007271308055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79999320879182676361744073 59999490659387007271308055)
        ·
          refine ⟨89999235989080510906962083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59999490659387007271308055 89999235989080510906962083)
          ·
            refine ⟨134998853983620766360443125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89999235989080510906962083 134998853983620766360443125)
            ·
              refine ⟨12656142560964446846291543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134998853983620766360443125 12656142560964446846291543)
              ·
                refine ⟨18984213841446670269437315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656142560964446846291543 18984213841446670269437315)
                ·
                  refine ⟨28476320762170005404155973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18984213841446670269437315 28476320762170005404155973)
                  ·
                    refine ⟨5339310142906876013279245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28476320762170005404155973 5339310142906876013279245)
                    ·
                      refine ⟨2002241303590078504979717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339310142906876013279245 2002241303590078504979717)
                      ·
                        rfl

theorem cell23_3899351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_3899351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899351 prefixEnd_3899351 := by exact prefixLift 3899351
  have htrace : WordTrace (prefixWord ++ tailWord_3899351) baseStart_3899351 baseEnd_3899351 := by
    simpa [prefixWord, tailWord_3899351, baseEnd_3899351] using wordTrace_append hprefix tailTrace_3899351
  have hstable : (prefixWord ++ tailWord_3899351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899351).length < 2 ^ (prefixWord ++ tailWord_3899351).sum := by decide
  have hdescent : baseEnd_3899351 < baseStart_3899351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899388 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 6]
def baseStart_3899388 : Nat := 118140960795 + 3899388 * 2 ^ 59
def prefixEnd_3899388 : Nat := 4983230072969 + 3 ^ 40 * 3899388 * 2
def baseEnd_3899388 : Nat := 222473366930477206690783

theorem tailTrace_3899388 : CollatzResearch.WordTrace tailWord_3899388 prefixEnd_3899388 222473366930477206690783 := by
  unfold tailWord_3899388
  simp only [CollatzResearch.WordTrace]
  refine ⟨71111182198595356647765409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94814909598127142197020545 71111182198595356647765409)
  ·
    refine ⟨53333386648946517485824057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71111182198595356647765409 53333386648946517485824057)
    ·
      refine ⟨40000039986709888114368043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53333386648946517485824057 40000039986709888114368043)
      ·
        refine ⟨60000059980064832171552065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40000039986709888114368043 60000059980064832171552065)
        ·
          refine ⟨45000044985048624128664049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60000059980064832171552065 45000044985048624128664049)
          ·
            refine ⟨33750033738786468096498037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45000044985048624128664049 33750033738786468096498037)
            ·
              refine ⟨3164065663011231384046691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33750033738786468096498037 3164065663011231384046691)
              ·
                refine ⟨4746098494516847076070037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164065663011231384046691 4746098494516847076070037)
                ·
                  refine ⟨222473366930477206690783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4746098494516847076070037 222473366930477206690783)
                  ·
                    rfl

theorem cell23_3899388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_3899388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899388 prefixEnd_3899388 := by exact prefixLift 3899388
  have htrace : WordTrace (prefixWord ++ tailWord_3899388) baseStart_3899388 baseEnd_3899388 := by
    simpa [prefixWord, tailWord_3899388, baseEnd_3899388] using wordTrace_append hprefix tailTrace_3899388
  have hstable : (prefixWord ++ tailWord_3899388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899388).length < 2 ^ (prefixWord ++ tailWord_3899388).sum := by decide
  have hdescent : baseEnd_3899388 < baseStart_3899388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899418 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_3899418 : Nat := 118140960795 + 3899418 * 2 ^ 59
def prefixEnd_3899418 : Nat := 4983230072969 + 3 ^ 40 * 3899418 * 2
def baseEnd_3899418 : Nat := 667425235597976580947303

theorem tailTrace_3899418 : CollatzResearch.WordTrace tailWord_3899418 prefixEnd_3899418 667425235597976580947303 := by
  unfold tailWord_3899418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35555864646770507104780727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94815639058054685612748605 35555864646770507104780727)
  ·
    refine ⟨53333796970155760657171091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35555864646770507104780727 53333796970155760657171091)
    ·
      refine ⟨80000695455233640985756637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53333796970155760657171091 80000695455233640985756637)
      ·
        refine ⟨30000260795712615369658739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80000695455233640985756637 30000260795712615369658739)
        ·
          refine ⟨45000391193568923054488109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30000260795712615369658739 45000391193568923054488109)
          ·
            refine ⟨16875146697588346145433041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45000391193568923054488109 16875146697588346145433041)
            ·
              refine ⟨12656360023191259609074781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16875146697588346145433041 12656360023191259609074781)
              ·
                refine ⟨4746135008696722353403043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12656360023191259609074781 4746135008696722353403043)
                ·
                  refine ⟨7119202513045083530104565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746135008696722353403043 7119202513045083530104565)
                  ·
                    refine ⟨667425235597976580947303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7119202513045083530104565 667425235597976580947303)
                    ·
                      rfl

theorem cell23_3899418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_3899418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899418 prefixEnd_3899418 := by exact prefixLift 3899418
  have htrace : WordTrace (prefixWord ++ tailWord_3899418) baseStart_3899418 baseEnd_3899418 := by
    simpa [prefixWord, tailWord_3899418, baseEnd_3899418] using wordTrace_append hprefix tailTrace_3899418
  have hstable : (prefixWord ++ tailWord_3899418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899418).length < 2 ^ (prefixWord ++ tailWord_3899418).sum := by decide
  have hdescent : baseEnd_3899418 < baseStart_3899418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899455 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 3, 2, 2]
def baseStart_3899455 : Nat := 118140960795 + 3899455 * 2 ^ 59
def prefixEnd_3899455 : Nat := 4983230072969 + 3 ^ 40 * 3899455 * 2
def baseEnd_3899455 : Nat := 2002294705578146098079239

theorem tailTrace_3899455 : CollatzResearch.WordTrace tailWord_3899455 prefixEnd_3899455 2002294705578146098079239 := by
  unfold tailWord_3899455
  simp only [CollatzResearch.WordTrace]
  refine ⟨142224808087947983738219819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94816538725298655825479879 142224808087947983738219819)
  ·
    refine ⟨213337212131921975607329729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142224808087947983738219819 213337212131921975607329729)
    ·
      refine ⟨160002909098941481705497297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213337212131921975607329729 160002909098941481705497297)
      ·
        refine ⟨120002181824206111279122973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160002909098941481705497297 120002181824206111279122973)
        ·
          refine ⟨45000818184077291729671115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120002181824206111279122973 45000818184077291729671115)
          ·
            refine ⟨67501227276115937594506673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45000818184077291729671115 67501227276115937594506673)
            ·
              refine ⟨50625920457086953195880005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67501227276115937594506673 50625920457086953195880005)
              ·
                refine ⟨9492360085703803724227501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50625920457086953195880005 9492360085703803724227501)
                ·
                  refine ⟨3559635032138926396585313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9492360085703803724227501 3559635032138926396585313)
                  ·
                    refine ⟨2669726274104194797438985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559635032138926396585313 2669726274104194797438985)
                    ·
                      refine ⟨2002294705578146098079239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669726274104194797438985 2002294705578146098079239)
                      ·
                        rfl

theorem cell23_3899455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_3899455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899455 prefixEnd_3899455 := by exact prefixLift 3899455
  have htrace : WordTrace (prefixWord ++ tailWord_3899455) baseStart_3899455 baseEnd_3899455 := by
    simpa [prefixWord, tailWord_3899455, baseEnd_3899455] using wordTrace_append hprefix tailTrace_3899455
  have hstable : (prefixWord ++ tailWord_3899455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899455).length < 2 ^ (prefixWord ++ tailWord_3899455).sum := by decide
  have hdescent : baseEnd_3899455 < baseStart_3899455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899491 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 7]
def baseStart_3899491 : Nat := 118140960795 + 3899491 * 2 ^ 59
def prefixEnd_3899491 : Nat := 4983230072969 + 3 ^ 40 * 3899491 * 2
def baseEnd_3899491 : Nat := 667437730293902652409691

theorem tailTrace_3899491 : CollatzResearch.WordTrace tailWord_3899491 prefixEnd_3899491 667437730293902652409691 := by
  unfold tailWord_3899491
  simp only [CollatzResearch.WordTrace]
  refine ⟨142226121115817561886530327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94817414077211707924353551 142226121115817561886530327)
  ·
    refine ⟨213339181673726342829795491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142226121115817561886530327 213339181673726342829795491)
    ·
      refine ⟨320008772510589514244693237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213339181673726342829795491 320008772510589514244693237)
      ·
        refine ⟨30000822422867766960439991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320008772510589514244693237 30000822422867766960439991)
        ·
          refine ⟨45001233634301650440659987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30000822422867766960439991 45001233634301650440659987)
          ·
            refine ⟨67501850451452475660989981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45001233634301650440659987 67501850451452475660989981)
            ·
              refine ⟨25313193919294678372871243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67501850451452475660989981 25313193919294678372871243)
              ·
                refine ⟨37969790878942017559306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25313193919294678372871243 37969790878942017559306865)
                ·
                  refine ⟨28477343159206513169480149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37969790878942017559306865 28477343159206513169480149)
                  ·
                    refine ⟨667437730293902652409691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28477343159206513169480149 667437730293902652409691)
                    ·
                      rfl

theorem cell23_3899491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_3899491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899491 prefixEnd_3899491 := by exact prefixLift 3899491
  have htrace : WordTrace (prefixWord ++ tailWord_3899491) baseStart_3899491 baseEnd_3899491 := by
    simpa [prefixWord, tailWord_3899491, baseEnd_3899491] using wordTrace_append hprefix tailTrace_3899491
  have hstable : (prefixWord ++ tailWord_3899491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899491).length < 2 ^ (prefixWord ++ tailWord_3899491).sum := by decide
  have hdescent : baseEnd_3899491 < baseStart_3899491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899505 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_3899505 : Nat := 118140960795 + 3899505 * 2 ^ 59
def prefixEnd_3899505 : Nat := 4983230072969 + 3 ^ 40 * 3899505 * 2
def baseEnd_3899505 : Nat := 2002320379610870902454009

theorem tailTrace_3899505 : CollatzResearch.WordTrace tailWord_3899505 prefixEnd_3899505 2002320379610870902454009 := by
  unfold tailWord_3899505
  simp only [CollatzResearch.WordTrace]
  refine ⟨142226631737766842277539969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94817754491844561518359979 142226631737766842277539969)
  ·
    refine ⟨106669973803325131708154977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142226631737766842277539969 106669973803325131708154977)
    ·
      refine ⟨80002480352493848781116233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106669973803325131708154977 80002480352493848781116233)
      ·
        refine ⟨60001860264370386585837175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80002480352493848781116233 60001860264370386585837175)
        ·
          refine ⟨90002790396555579878755763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60001860264370386585837175 90002790396555579878755763)
          ·
            refine ⟨135004185594833369818133645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90002790396555579878755763 135004185594833369818133645)
            ·
              refine ⟨50626569598062513681800117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135004185594833369818133645 50626569598062513681800117)
              ·
                refine ⟨4746240899818360657668761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50626569598062513681800117 4746240899818360657668761)
                ·
                  refine ⟨3559680674863770493251571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746240899818360657668761 3559680674863770493251571)
                  ·
                    refine ⟨5339521012295655739877357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559680674863770493251571 5339521012295655739877357)
                    ·
                      refine ⟨2002320379610870902454009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339521012295655739877357 2002320379610870902454009)
                      ·
                        rfl

theorem cell23_3899505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_3899505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899505 prefixEnd_3899505 := by exact prefixLift 3899505
  have htrace : WordTrace (prefixWord ++ tailWord_3899505) baseStart_3899505 baseEnd_3899505 := by
    simpa [prefixWord, tailWord_3899505, baseEnd_3899505] using wordTrace_append hprefix tailTrace_3899505
  have hstable : (prefixWord ++ tailWord_3899505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899505).length < 2 ^ (prefixWord ++ tailWord_3899505).sum := by decide
  have hdescent : baseEnd_3899505 < baseStart_3899505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899538 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3899538 : Nat := 118140960795 + 3899538 * 2 ^ 59
def prefixEnd_3899538 : Nat := 4983230072969 + 3 ^ 40 * 3899538 * 2
def baseEnd_3899538 : Nat := 667445774824156424447119

theorem tailTrace_3899538 : CollatzResearch.WordTrace tailWord_3899538 prefixEnd_3899538 667445774824156424447119 := by
  unfold tailWord_3899538
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556958836661822228372817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94818556897764859275660845 35556958836661822228372817)
  ·
    refine ⟨26667719127496366671279613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35556958836661822228372817 26667719127496366671279613)
    ·
      refine ⟨10000394672811137501729855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26667719127496366671279613 10000394672811137501729855)
      ·
        refine ⟨15000592009216706252594783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000394672811137501729855 15000592009216706252594783)
        ·
          refine ⟨22500888013825059378892175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15000592009216706252594783 22500888013825059378892175)
          ·
            refine ⟨33751332020737589068338263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22500888013825059378892175 33751332020737589068338263)
            ·
              refine ⟨50626998031106383602507395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33751332020737589068338263 50626998031106383602507395)
              ·
                refine ⟨75940497046659575403761093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50626998031106383602507395 75940497046659575403761093)
                ·
                  refine ⟨14238843196248670388205205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75940497046659575403761093 14238843196248670388205205)
                  ·
                    refine ⟨667445774824156424447119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14238843196248670388205205 667445774824156424447119)
                    ·
                      rfl

theorem cell23_3899538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3899538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899538 prefixEnd_3899538 := by exact prefixLift 3899538
  have htrace : WordTrace (prefixWord ++ tailWord_3899538) baseStart_3899538 baseEnd_3899538 := by
    simpa [prefixWord, tailWord_3899538, baseEnd_3899538] using wordTrace_append hprefix tailTrace_3899538
  have hstable : (prefixWord ++ tailWord_3899538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899538).length < 2 ^ (prefixWord ++ tailWord_3899538).sum := by decide
  have hdescent : baseEnd_3899538 < baseStart_3899538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899578 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_3899578 : Nat := 118140960795 + 3899578 * 2 ^ 59
def prefixEnd_3899578 : Nat := 4983230072969 + 3 ^ 40 * 3899578 * 2
def baseEnd_3899578 : Nat := 2002357863698649116841173

theorem tailTrace_3899578 : CollatzResearch.WordTrace tailWord_3899578 prefixEnd_3899578 2002357863698649116841173 := by
  unfold tailWord_3899578
  simp only [CollatzResearch.WordTrace]
  refine ⟨35557323566625593936236847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94819529511001583829964925 35557323566625593936236847)
  ·
    refine ⟨53335985349938390904355271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35557323566625593936236847 53335985349938390904355271)
    ·
      refine ⟨80003978024907586356532907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53335985349938390904355271 80003978024907586356532907)
      ·
        refine ⟨120005967037361379534799361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80003978024907586356532907 120005967037361379534799361)
        ·
          refine ⟨90004475278021034651099521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120005967037361379534799361 90004475278021034651099521)
          ·
            refine ⟨67503356458515775988324641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90004475278021034651099521 67503356458515775988324641)
            ·
              refine ⟨50627517343886831991243481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67503356458515775988324641 50627517343886831991243481)
              ·
                refine ⟨37970638007915123993432611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50627517343886831991243481 37970638007915123993432611)
                ·
                  refine ⟨56955957011872685990148917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37970638007915123993432611 56955957011872685990148917)
                  ·
                    refine ⟨5339620969863064311576461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56955957011872685990148917 5339620969863064311576461)
                    ·
                      refine ⟨2002357863698649116841173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339620969863064311576461 2002357863698649116841173)
                      ·
                        rfl

theorem cell23_3899578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_3899578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899578 prefixEnd_3899578 := by exact prefixLift 3899578
  have htrace : WordTrace (prefixWord ++ tailWord_3899578) baseStart_3899578 baseEnd_3899578 := by
    simpa [prefixWord, tailWord_3899578, baseEnd_3899578] using wordTrace_append hprefix tailTrace_3899578
  have hstable : (prefixWord ++ tailWord_3899578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899578).length < 2 ^ (prefixWord ++ tailWord_3899578).sum := by decide
  have hdescent : baseEnd_3899578 < baseStart_3899578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899608 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3899608 : Nat := 118140960795 + 3899608 * 2 ^ 59
def prefixEnd_3899608 : Nat := 4983230072969 + 3 ^ 40 * 3899608 * 2
def baseEnd_3899608 : Nat := 2002373268118283999466035

theorem tailTrace_3899608 : CollatzResearch.WordTrace tailWord_3899608 prefixEnd_3899608 2002373268118283999466035 := by
  unfold tailWord_3899608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71115194228196845434269739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94820258970929127245692985 71115194228196845434269739)
  ·
    refine ⟨106672791342295268151404609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71115194228196845434269739 106672791342295268151404609)
    ·
      refine ⟨80004593506721451113553457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106672791342295268151404609 80004593506721451113553457)
      ·
        refine ⟨60003445130041088335165093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80004593506721451113553457 60003445130041088335165093)
        ·
          refine ⟨11250645961882704062843455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60003445130041088335165093 11250645961882704062843455)
          ·
            refine ⟨16875968942824056094265183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250645961882704062843455 16875968942824056094265183)
            ·
              refine ⟨25313953414236084141397775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16875968942824056094265183 25313953414236084141397775)
              ·
                refine ⟨37970930121354126212096663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25313953414236084141397775 37970930121354126212096663)
                ·
                  refine ⟨56956395182031189318144995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37970930121354126212096663 56956395182031189318144995)
                  ·
                    refine ⟨85434592773046783977217493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56956395182031189318144995 85434592773046783977217493)
                    ·
                      refine ⟨2002373268118283999466035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85434592773046783977217493 2002373268118283999466035)
                      ·
                        rfl

theorem cell23_3899608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3899608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899608 prefixEnd_3899608 := by exact prefixLift 3899608
  have htrace : WordTrace (prefixWord ++ tailWord_3899608) baseStart_3899608 baseEnd_3899608 := by
    simpa [prefixWord, tailWord_3899608, baseEnd_3899608] using wordTrace_append hprefix tailTrace_3899608
  have hstable : (prefixWord ++ tailWord_3899608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899608).length < 2 ^ (prefixWord ++ tailWord_3899608).sum := by decide
  have hdescent : baseEnd_3899608 < baseStart_3899608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899613 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3899613 : Nat := 118140960795 + 3899613 * 2 ^ 59
def prefixEnd_3899613 : Nat := 4983230072969 + 3 ^ 40 * 3899613 * 2
def baseEnd_3899613 : Nat := 2002375835521556479903513

theorem tailTrace_3899613 : CollatzResearch.WordTrace tailWord_3899613 prefixEnd_3899613 2002375835521556479903513 := by
  unfold tailWord_3899613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142230570821375576722471493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94820380547583717814980995 142230570821375576722471493)
  ·
    refine ⟨26668232029007920635463405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142230570821375576722471493 26668232029007920635463405)
    ·
      refine ⟨10000587010877970238298777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26668232029007920635463405 10000587010877970238298777)
      ·
        refine ⟨7500440258158477678724083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10000587010877970238298777 7500440258158477678724083)
        ·
          refine ⟨11250660387237716518086125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500440258158477678724083 11250660387237716518086125)
          ·
            refine ⟨4218997645214143694282297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11250660387237716518086125 4218997645214143694282297)
            ·
              refine ⟨3164248233910607770711723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4218997645214143694282297 3164248233910607770711723)
              ·
                refine ⟨4746372350865911656067585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164248233910607770711723 4746372350865911656067585)
                ·
                  refine ⟨3559779263149433742050689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746372350865911656067585 3559779263149433742050689)
                  ·
                    refine ⟨2669834447362075306538017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3559779263149433742050689 2669834447362075306538017)
                    ·
                      refine ⟨2002375835521556479903513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669834447362075306538017 2002375835521556479903513)
                      ·
                        rfl

theorem cell23_3899613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3899613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899613 prefixEnd_3899613 := by exact prefixLift 3899613
  have htrace : WordTrace (prefixWord ++ tailWord_3899613) baseStart_3899613 baseEnd_3899613 := by
    simpa [prefixWord, tailWord_3899613, baseEnd_3899613] using wordTrace_append hprefix tailTrace_3899613
  have hstable : (prefixWord ++ tailWord_3899613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899613).length < 2 ^ (prefixWord ++ tailWord_3899613).sum := by decide
  have hdescent : baseEnd_3899613 < baseStart_3899613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899635 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4]
def baseStart_3899635 : Nat := 118140960795 + 3899635 * 2 ^ 59
def prefixEnd_3899635 : Nat := 4983230072969 + 3 ^ 40 * 3899635 * 2
def baseEnd_3899635 : Nat := 2002387132095955393828411

theorem tailTrace_3899635 : CollatzResearch.WordTrace tailWord_3899635 prefixEnd_3899635 2002387132095955393828411 := by
  unfold tailWord_3899635
  simp only [CollatzResearch.WordTrace]
  refine ⟨142231373227295874479772359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94820915484863916319848239 142231373227295874479772359)
  ·
    refine ⟨213347059840943811719658539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142231373227295874479772359 213347059840943811719658539)
    ·
      refine ⟨320020589761415717579487809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213347059840943811719658539 320020589761415717579487809)
      ·
        refine ⟨240015442321061788184615857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320020589761415717579487809 240015442321061788184615857)
        ·
          refine ⟨180011581740796341138461893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240015442321061788184615857 180011581740796341138461893)
          ·
            refine ⟨33752171576399313963461605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180011581740796341138461893 33752171576399313963461605)
            ·
              refine ⟨6328532170574871368149051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33752171576399313963461605 6328532170574871368149051)
              ·
                refine ⟨9492798255862307052223577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328532170574871368149051 9492798255862307052223577)
                ·
                  refine ⟨7119598691896730289167683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9492798255862307052223577 7119598691896730289167683)
                  ·
                    refine ⟨10679398037845095433751525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7119598691896730289167683 10679398037845095433751525)
                    ·
                      refine ⟨2002387132095955393828411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10679398037845095433751525 2002387132095955393828411)
                      ·
                        rfl

theorem cell23_3899635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_3899635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899635 prefixEnd_3899635 := by exact prefixLift 3899635
  have htrace : WordTrace (prefixWord ++ tailWord_3899635) baseStart_3899635 baseEnd_3899635 := by
    simpa [prefixWord, tailWord_3899635, baseEnd_3899635] using wordTrace_append hprefix tailTrace_3899635
  have hstable : (prefixWord ++ tailWord_3899635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899635).length < 2 ^ (prefixWord ++ tailWord_3899635).sum := by decide
  have hdescent : baseEnd_3899635 < baseStart_3899635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899658 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_3899658 : Nat := 118140960795 + 3899658 * 2 ^ 59
def prefixEnd_3899658 : Nat := 4983230072969 + 3 ^ 40 * 3899658 * 2
def baseEnd_3899658 : Nat := 222488771350112089315645

theorem tailTrace_3899658 : CollatzResearch.WordTrace tailWord_3899658 prefixEnd_3899658 222488771350112089315645 := by
  unfold tailWord_3899658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35558053026553137351964907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94821474737475032938573085 35558053026553137351964907)
  ·
    refine ⟨53337079539829706027947361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35558053026553137351964907 53337079539829706027947361)
    ·
      refine ⟨40002809654872279520960521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53337079539829706027947361 40002809654872279520960521)
      ·
        refine ⟨30002107241154209640720391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40002809654872279520960521 30002107241154209640720391)
        ·
          refine ⟨45003160861731314461080587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30002107241154209640720391 45003160861731314461080587)
          ·
            refine ⟨67504741292596971691620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45003160861731314461080587 67504741292596971691620881)
            ·
              refine ⟨50628555969447728768715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67504741292596971691620881 50628555969447728768715661)
              ·
                refine ⟨18985708488542898288268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50628555969447728768715661 18985708488542898288268373)
                ·
                  refine ⟨222488771350112089315645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18985708488542898288268373 222488771350112089315645)
                  ·
                    rfl

theorem cell23_3899658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_3899658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899658 prefixEnd_3899658 := by exact prefixLift 3899658
  have htrace : WordTrace (prefixWord ++ tailWord_3899658) baseStart_3899658 baseEnd_3899658 := by
    simpa [prefixWord, tailWord_3899658, baseEnd_3899658] using wordTrace_append hprefix tailTrace_3899658
  have hstable : (prefixWord ++ tailWord_3899658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899658).length < 2 ^ (prefixWord ++ tailWord_3899658).sum := by decide
  have hdescent : baseEnd_3899658 < baseStart_3899658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899719 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_3899719 : Nat := 118140960795 + 3899719 * 2 ^ 59
def prefixEnd_3899719 : Nat := 4983230072969 + 3 ^ 40 * 3899719 * 2
def baseEnd_3899719 : Nat := 2002430264470933065178025

theorem tailTrace_3899719 : CollatzResearch.WordTrace tailWord_3899719 prefixEnd_3899719 2002430264470933065178025 := by
  unfold tailWord_3899719
  simp only [CollatzResearch.WordTrace]
  refine ⟨142234436958991556825830211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94822957972661037883886807 142234436958991556825830211)
  ·
    refine ⟨213351655438487335238745317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142234436958991556825830211 213351655438487335238745317)
    ·
      refine ⟨40003435394716375357264747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213351655438487335238745317 40003435394716375357264747)
      ·
        refine ⟨60005153092074563035897121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40003435394716375357264747 60005153092074563035897121)
        ·
          refine ⟨45003864819055922276922841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60005153092074563035897121 45003864819055922276922841)
          ·
            refine ⟨33752898614291941707692131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45003864819055922276922841 33752898614291941707692131)
            ·
              refine ⟨50629347921437912561538197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33752898614291941707692131 50629347921437912561538197)
              ·
                refine ⟨2373250683817402151322103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50629347921437912561538197 2373250683817402151322103)
                ·
                  refine ⟨3559876025726103226983155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373250683817402151322103 3559876025726103226983155)
                  ·
                    refine ⟨5339814038589154840474733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3559876025726103226983155 5339814038589154840474733)
                    ·
                      refine ⟨2002430264470933065178025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339814038589154840474733 2002430264470933065178025)
                      ·
                        rfl

theorem cell23_3899719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_3899719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899719 prefixEnd_3899719 := by exact prefixLift 3899719
  have htrace : WordTrace (prefixWord ++ tailWord_3899719) baseStart_3899719 baseEnd_3899719 := by
    simpa [prefixWord, tailWord_3899719, baseEnd_3899719] using wordTrace_append hprefix tailTrace_3899719
  have hstable : (prefixWord ++ tailWord_3899719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899719).length < 2 ^ (prefixWord ++ tailWord_3899719).sum := by decide
  have hdescent : baseEnd_3899719 < baseStart_3899719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899752 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3899752 : Nat := 118140960795 + 3899752 * 2 ^ 59
def prefixEnd_3899752 : Nat := 4983230072969 + 3 ^ 40 * 3899752 * 2
def baseEnd_3899752 : Nat := 667482403110843812021791

theorem tailTrace_3899752 : CollatzResearch.WordTrace tailWord_3899752 prefixEnd_3899752 667482403110843812021791 := by
  unfold tailWord_3899752
  simp only [CollatzResearch.WordTrace]
  refine ⟨71117820283936001730890755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94823760378581335641187673 71117820283936001730890755)
  ·
    refine ⟨106676730425904002596336133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71117820283936001730890755 106676730425904002596336133)
    ·
      refine ⟨20001886954857000486813025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106676730425904002596336133 20001886954857000486813025)
      ·
        refine ⟨15001415216142750365109769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20001886954857000486813025 15001415216142750365109769)
        ·
          refine ⟨11251061412107062773832327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15001415216142750365109769 11251061412107062773832327)
          ·
            refine ⟨16876592118160594160748491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251061412107062773832327 16876592118160594160748491)
            ·
              refine ⟨25314888177240891241122737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876592118160594160748491 25314888177240891241122737)
              ·
                refine ⟨18986166132930668430842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25314888177240891241122737 18986166132930668430842053)
                ·
                  refine ⟨3559906149924500330782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18986166132930668430842053 3559906149924500330782885)
                  ·
                    refine ⟨667482403110843812021791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3559906149924500330782885 667482403110843812021791)
                    ·
                      rfl

theorem cell23_3899752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3899752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899752 prefixEnd_3899752 := by exact prefixLift 3899752
  have htrace : WordTrace (prefixWord ++ tailWord_3899752) baseStart_3899752 baseEnd_3899752 := by
    simpa [prefixWord, tailWord_3899752, baseEnd_3899752] using wordTrace_append hprefix tailTrace_3899752
  have hstable : (prefixWord ++ tailWord_3899752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899752).length < 2 ^ (prefixWord ++ tailWord_3899752).sum := by decide
  have hdescent : baseEnd_3899752 < baseStart_3899752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899762 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3899762 : Nat := 118140960795 + 3899762 * 2 ^ 59
def prefixEnd_3899762 : Nat := 4983230072969 + 3 ^ 40 * 3899762 * 2
def baseEnd_3899762 : Nat := 2002452344139076396940327

theorem tailTrace_3899762 : CollatzResearch.WordTrace tailWord_3899762 prefixEnd_3899762 2002452344139076396940327 := by
  unfold tailWord_3899762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559001324458943792411385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94824003531890516779763693 35559001324458943792411385)
  ·
    refine ⟨26669250993344207844308539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35559001324458943792411385 26669250993344207844308539)
    ·
      refine ⟨40003876490016311766462809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26669250993344207844308539 40003876490016311766462809)
      ·
        refine ⟨30002907367512233824847107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40003876490016311766462809 30002907367512233824847107)
        ·
          refine ⟨45004361051268350737270661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30002907367512233824847107 45004361051268350737270661)
          ·
            refine ⟨8438317697112815763238249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45004361051268350737270661 8438317697112815763238249)
            ·
              refine ⟨6328738272834611822428687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438317697112815763238249 6328738272834611822428687)
              ·
                refine ⟨9493107409251917733643031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6328738272834611822428687 9493107409251917733643031)
                ·
                  refine ⟨14239661113877876600464547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9493107409251917733643031 14239661113877876600464547)
                  ·
                    refine ⟨21359491670816814900696821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14239661113877876600464547 21359491670816814900696821)
                    ·
                      refine ⟨2002452344139076396940327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21359491670816814900696821 2002452344139076396940327)
                      ·
                        rfl

theorem cell23_3899762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3899762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899762 prefixEnd_3899762 := by exact prefixLift 3899762
  have htrace : WordTrace (prefixWord ++ tailWord_3899762) baseStart_3899762 baseEnd_3899762 := by
    simpa [prefixWord, tailWord_3899762, baseEnd_3899762] using wordTrace_append hprefix tailTrace_3899762
  have hstable : (prefixWord ++ tailWord_3899762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899762).length < 2 ^ (prefixWord ++ tailWord_3899762).sum := by decide
  have hdescent : baseEnd_3899762 < baseStart_3899762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899765 : List Nat := [1, 3, 4, 1, 2, 1, 11]
def baseStart_3899765 : Nat := 118140960795 + 3899765 * 2 ^ 59
def prefixEnd_3899765 : Nat := 4983230072969 + 3 ^ 40 * 3899765 * 2
def baseEnd_3899765 : Nat := 24721652896062220804973

theorem tailTrace_3899765 : CollatzResearch.WordTrace tailWord_3899765 prefixEnd_3899765 24721652896062220804973 := by
  unfold tailWord_3899765
  simp only [CollatzResearch.WordTrace]
  refine ⟨142236114716824906682004749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94824076477883271121336499 142236114716824906682004749)
  ·
    refine ⟨53338543018809340005751781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142236114716824906682004749 53338543018809340005751781)
    ·
      refine ⟨10000976816026751251078459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53338543018809340005751781 10000976816026751251078459)
      ·
        refine ⟨15001465224040126876617689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000976816026751251078459 15001465224040126876617689)
        ·
          refine ⟨11251098918030095157463267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15001465224040126876617689 11251098918030095157463267)
          ·
            refine ⟨16876648377045142736194901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11251098918030095157463267 16876648377045142736194901)
            ·
              refine ⟨24721652896062220804973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16876648377045142736194901 24721652896062220804973)
              ·
                rfl

theorem cell23_3899765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 11].length) (baseStart_3899765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899765 prefixEnd_3899765 := by exact prefixLift 3899765
  have htrace : WordTrace (prefixWord ++ tailWord_3899765) baseStart_3899765 baseEnd_3899765 := by
    simpa [prefixWord, tailWord_3899765, baseEnd_3899765] using wordTrace_append hprefix tailTrace_3899765
  have hstable : (prefixWord ++ tailWord_3899765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899765).length < 2 ^ (prefixWord ++ tailWord_3899765).sum := by decide
  have hdescent : baseEnd_3899765 < baseStart_3899765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899775 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_3899775 : Nat := 118140960795 + 3899775 * 2 ^ 59
def prefixEnd_3899775 : Nat := 4983230072969 + 3 ^ 40 * 3899775 * 2
def baseEnd_3899775 : Nat := 2002459019387584846077767

theorem tailTrace_3899775 : CollatzResearch.WordTrace tailWord_3899775 prefixEnd_3899775 2002459019387584846077767 := by
  unfold tailWord_3899775
  simp only [CollatzResearch.WordTrace]
  refine ⟨142236479446788678389868779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94824319631192452259912519 142236479446788678389868779)
  ·
    refine ⟨213354719170183017584803169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142236479446788678389868779 213354719170183017584803169)
    ·
      refine ⟨160016039377637263188602377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213354719170183017584803169 160016039377637263188602377)
      ·
        refine ⟨120012029533227947391451783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160016039377637263188602377 120012029533227947391451783)
        ·
          refine ⟨180018044299841921087177675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120012029533227947391451783 180018044299841921087177675)
          ·
            refine ⟨270027066449762881630766513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180018044299841921087177675 270027066449762881630766513)
            ·
              refine ⟨202520299837322161223074885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270027066449762881630766513 202520299837322161223074885)
              ·
                refine ⟨37972556219497905229326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202520299837322161223074885 37972556219497905229326541)
                ·
                  refine ⟨14239708582311714460997453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37972556219497905229326541 14239708582311714460997453)
                  ·
                    refine ⟨5339890718366892922874045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14239708582311714460997453 5339890718366892922874045)
                    ·
                      refine ⟨2002459019387584846077767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5339890718366892922874045 2002459019387584846077767)
                      ·
                        rfl

theorem cell23_3899775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_3899775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899775 prefixEnd_3899775 := by exact prefixLift 3899775
  have htrace : WordTrace (prefixWord ++ tailWord_3899775) baseStart_3899775 baseEnd_3899775 := by
    simpa [prefixWord, tailWord_3899775, baseEnd_3899775] using wordTrace_append hprefix tailTrace_3899775
  have hstable : (prefixWord ++ tailWord_3899775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899775).length < 2 ^ (prefixWord ++ tailWord_3899775).sum := by decide
  have hdescent : baseEnd_3899775 < baseStart_3899775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899786 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_3899786 : Nat := 118140960795 + 3899786 * 2 ^ 59
def prefixEnd_3899786 : Nat := 4983230072969 + 3 ^ 40 * 3899786 * 2
def baseEnd_3899786 : Nat := 667488222558261434346739

theorem tailTrace_3899786 : CollatzResearch.WordTrace tailWord_3899786 prefixEnd_3899786 667488222558261434346739 := by
  unfold tailWord_3899786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35559220162437206817129803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94824587099832551512346141 35559220162437206817129803)
  ·
    refine ⟨53338830243655810225694705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35559220162437206817129803 53338830243655810225694705)
    ·
      refine ⟨40004122682741857669271029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53338830243655810225694705 40004122682741857669271029)
      ·
        refine ⟨3750386501507049156494159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40004122682741857669271029 3750386501507049156494159)
        ·
          refine ⟨5625579752260573734741239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750386501507049156494159 5625579752260573734741239)
          ·
            refine ⟨8438369628390860602111859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625579752260573734741239 8438369628390860602111859)
            ·
              refine ⟨12657554442586290903167789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438369628390860602111859 12657554442586290903167789)
              ·
                refine ⟨4746582915969859088687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12657554442586290903167789 4746582915969859088687921)
                ·
                  refine ⟨3559937186977394316515941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4746582915969859088687921 3559937186977394316515941)
                  ·
                    refine ⟨667488222558261434346739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3559937186977394316515941 667488222558261434346739)
                    ·
                      rfl

theorem cell23_3899786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_3899786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899786 prefixEnd_3899786 := by exact prefixLift 3899786
  have htrace : WordTrace (prefixWord ++ tailWord_3899786) baseStart_3899786 baseEnd_3899786 := by
    simpa [prefixWord, tailWord_3899786, baseEnd_3899786] using wordTrace_append hprefix tailTrace_3899786
  have hstable : (prefixWord ++ tailWord_3899786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899786).length < 2 ^ (prefixWord ++ tailWord_3899786).sum := by decide
  have hdescent : baseEnd_3899786 < baseStart_3899786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_3899832 : Nat := 118140960795 + 3899832 * 2 ^ 59
def prefixEnd_3899832 : Nat := 4983230072969 + 3 ^ 40 * 3899832 * 2
def baseEnd_3899832 : Nat := 2002488287784891123065005

theorem tailTrace_3899832 : CollatzResearch.WordTrace tailWord_3899832 prefixEnd_3899832 2002488287784891123065005 := by
  unfold tailWord_3899832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71119279203791088562346875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94825705605054784749795833 71119279203791088562346875)
  ·
    refine ⟨106678918805686632843520313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71119279203791088562346875 106678918805686632843520313)
    ·
      refine ⟨80009189104264974632640235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106678918805686632843520313 80009189104264974632640235)
      ·
        refine ⟨120013783656397461948960353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80009189104264974632640235 120013783656397461948960353)
        ·
          refine ⟨90010337742298096461720265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120013783656397461948960353 90010337742298096461720265)
          ·
            refine ⟨67507753306723572346290199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90010337742298096461720265 67507753306723572346290199)
            ·
              refine ⟨101261629960085358519435299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67507753306723572346290199 101261629960085358519435299)
              ·
                refine ⟨151892444940128037779152949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101261629960085358519435299 151892444940128037779152949)
                ·
                  refine ⟨14239916713137003541795589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151892444940128037779152949 14239916713137003541795589)
                  ·
                    refine ⟨2669984383713188164086673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14239916713137003541795589 2669984383713188164086673)
                    ·
                      refine ⟨2002488287784891123065005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2669984383713188164086673 2002488287784891123065005)
                      ·
                        rfl

theorem cell23_3899832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_3899832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899832 prefixEnd_3899832 := by exact prefixLift 3899832
  have htrace : WordTrace (prefixWord ++ tailWord_3899832) baseStart_3899832 baseEnd_3899832 := by
    simpa [prefixWord, tailWord_3899832, baseEnd_3899832] using wordTrace_append hprefix tailTrace_3899832
  have hstable : (prefixWord ++ tailWord_3899832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899832).length < 2 ^ (prefixWord ++ tailWord_3899832).sum := by decide
  have hdescent : baseEnd_3899832 < baseStart_3899832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899895 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_3899895 : Nat := 118140960795 + 3899895 * 2 ^ 59
def prefixEnd_3899895 : Nat := 4983230072969 + 3 ^ 40 * 3899895 * 2
def baseEnd_3899895 : Nat := 2002520637066124376577215

theorem tailTrace_3899895 : CollatzResearch.WordTrace tailWord_3899895 prefixEnd_3899895 2002520637066124376577215 := by
  unfold tailWord_3899895
  simp only [CollatzResearch.WordTrace]
  refine ⟨142240856206353938884237139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94827237470902625922824759 142240856206353938884237139)
  ·
    refine ⟨213361284309530908326355709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142240856206353938884237139 213361284309530908326355709)
    ·
      refine ⟨80010481616074090622383391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213361284309530908326355709 80010481616074090622383391)
      ·
        refine ⟨120015722424111135933575087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80010481616074090622383391 120015722424111135933575087)
        ·
          refine ⟨180023583636166703900362631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120015722424111135933575087 180023583636166703900362631)
          ·
            refine ⟨270035375454250055850543947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180023583636166703900362631 270035375454250055850543947)
            ·
              refine ⟨405053063181375083775815921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270035375454250055850543947 405053063181375083775815921)
              ·
                refine ⟨303789797386031312831861941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405053063181375083775815921 303789797386031312831861941)
                ·
                  refine ⟨28480293504940435577987057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303789797386031312831861941 28480293504940435577987057)
                  ·
                    refine ⟨21360220128705326683490293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28480293504940435577987057 21360220128705326683490293)
                    ·
                      refine ⟨2002520637066124376577215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21360220128705326683490293 2002520637066124376577215)
                      ·
                        rfl

theorem cell23_3899895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_3899895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899895 prefixEnd_3899895 := by exact prefixLift 3899895
  have htrace : WordTrace (prefixWord ++ tailWord_3899895) baseStart_3899895 baseEnd_3899895 := by
    simpa [prefixWord, tailWord_3899895, baseEnd_3899895] using wordTrace_append hprefix tailTrace_3899895
  have hstable : (prefixWord ++ tailWord_3899895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899895).length < 2 ^ (prefixWord ++ tailWord_3899895).sum := by decide
  have hdescent : baseEnd_3899895 < baseStart_3899895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899939 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3899939 : Nat := 118140960795 + 3899939 * 2 ^ 59
def prefixEnd_3899939 : Nat := 4983230072969 + 3 ^ 40 * 3899939 * 2
def baseEnd_3899939 : Nat := 2002543230214922204427013

theorem tailTrace_3899939 : CollatzResearch.WordTrace tailWord_3899939 prefixEnd_3899939 2002543230214922204427013 := by
  unfold tailWord_3899939
  simp only [CollatzResearch.WordTrace]
  refine ⟨142242461018194534398838871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94828307345463022932559247 142242461018194534398838871)
  ·
    refine ⟨213363691527291801598258307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142242461018194534398838871 213363691527291801598258307)
    ·
      refine ⟨320045537290937702397387461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213363691527291801598258307 320045537290937702397387461)
      ·
        refine ⟨60008538242050819199510149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320045537290937702397387461 60008538242050819199510149)
        ·
          refine ⟨11251600920384528599908153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60008538242050819199510149 11251600920384528599908153)
          ·
            refine ⟨8438700690288396449931115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11251600920384528599908153 8438700690288396449931115)
            ·
              refine ⟨12658051035432594674896673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8438700690288396449931115 12658051035432594674896673)
              ·
                refine ⟨9493538276574446006172505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658051035432594674896673 9493538276574446006172505)
                ·
                  refine ⟨7120153707430834504629379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9493538276574446006172505 7120153707430834504629379)
                  ·
                    refine ⟨10680230561146251756944069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120153707430834504629379 10680230561146251756944069)
                    ·
                      refine ⟨2002543230214922204427013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10680230561146251756944069 2002543230214922204427013)
                      ·
                        rfl

theorem cell23_3899939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3899939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899939 prefixEnd_3899939 := by exact prefixLift 3899939
  have htrace : WordTrace (prefixWord ++ tailWord_3899939) baseStart_3899939 baseEnd_3899939 := by
    simpa [prefixWord, tailWord_3899939, baseEnd_3899939] using wordTrace_append hprefix tailTrace_3899939
  have hstable : (prefixWord ++ tailWord_3899939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899939).length < 2 ^ (prefixWord ++ tailWord_3899939).sum := by decide
  have hdescent : baseEnd_3899939 < baseStart_3899939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3899996 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 6]
def baseStart_3899996 : Nat := 118140960795 + 3899996 * 2 ^ 59
def prefixEnd_3899996 : Nat := 4983230072969 + 3 ^ 40 * 3899996 * 2
def baseEnd_3899996 : Nat := 222508055401358720157139

theorem tailTrace_3899996 : CollatzResearch.WordTrace tailWord_3899996 prefixEnd_3899996 222508055401358720157139 := by
  unfold tailWord_3899996
  simp only [CollatzResearch.WordTrace]
  refine ⟨71122269989494016566831921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94829693319325355422442561 71122269989494016566831921)
  ·
    refine ⟨53341702492120512425123941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71122269989494016566831921 53341702492120512425123941)
    ·
      refine ⟨10001569217272596079710739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53341702492120512425123941 10001569217272596079710739)
      ·
        refine ⟨15002353825908894119566109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10001569217272596079710739 15002353825908894119566109)
        ·
          refine ⟨5625882684715835294837291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15002353825908894119566109 5625882684715835294837291)
          ·
            refine ⟨8438824027073752942255937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625882684715835294837291 8438824027073752942255937)
            ·
              refine ⟨6329118020305314706691953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438824027073752942255937 6329118020305314706691953)
              ·
                refine ⟨4746838515228986030018965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329118020305314706691953 4746838515228986030018965)
                ·
                  refine ⟨222508055401358720157139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4746838515228986030018965 222508055401358720157139)
                  ·
                    rfl

theorem cell23_3899996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_3899996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3899996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3899996 prefixEnd_3899996 := by exact prefixLift 3899996
  have htrace : WordTrace (prefixWord ++ tailWord_3899996) baseStart_3899996 baseEnd_3899996 := by
    simpa [prefixWord, tailWord_3899996, baseEnd_3899996] using wordTrace_append hprefix tailTrace_3899996
  have hstable : (prefixWord ++ tailWord_3899996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3899996).length < 2 ^ (prefixWord ++ tailWord_3899996).sum := by decide
  have hdescent : baseEnd_3899996 < baseStart_3899996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3899996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900034 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3900034 : Nat := 118140960795 + 3900034 * 2 ^ 59
def prefixEnd_3900034 : Nat := 4983230072969 + 3 ^ 40 * 3900034 * 2
def baseEnd_3900034 : Nat := 667530670292366444246359

theorem tailTrace_3900034 : CollatzResearch.WordTrace tailWord_3900034 prefixEnd_3900034 667530670292366444246359 := by
  unfold tailWord_3900034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35561481488212591405886789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94830617301900243749031437 35561481488212591405886789)
  ·
    refine ⟨6667777779039860888603773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35561481488212591405886789 6667777779039860888603773)
    ·
      refine ⟨2500416667139947833226415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6667777779039860888603773 2500416667139947833226415)
      ·
        refine ⟨3750625000709921749839623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500416667139947833226415 3750625000709921749839623)
        ·
          refine ⟨5625937501064882624759435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750625000709921749839623 5625937501064882624759435)
          ·
            refine ⟨8438906251597323937139153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625937501064882624759435 8438906251597323937139153)
            ·
              refine ⟨6329179688697992952854365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8438906251597323937139153 6329179688697992952854365)
              ·
                refine ⟨2373442383261747357320387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6329179688697992952854365 2373442383261747357320387)
                ·
                  refine ⟨3560163574892621035980581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373442383261747357320387 3560163574892621035980581)
                  ·
                    refine ⟨667530670292366444246359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560163574892621035980581 667530670292366444246359)
                    ·
                      rfl

theorem cell23_3900034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3900034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900034 prefixEnd_3900034 := by exact prefixLift 3900034
  have htrace : WordTrace (prefixWord ++ tailWord_3900034) baseStart_3900034 baseEnd_3900034 := by
    simpa [prefixWord, tailWord_3900034, baseEnd_3900034] using wordTrace_append hprefix tailTrace_3900034
  have hstable : (prefixWord ++ tailWord_3900034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900034).length < 2 ^ (prefixWord ++ tailWord_3900034).sum := by decide
  have hdescent : baseEnd_3900034 < baseStart_3900034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900039 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 4, 4]
def baseStart_3900039 : Nat := 118140960795 + 3900039 * 2 ^ 59
def prefixEnd_3900039 : Nat := 4983230072969 + 3 ^ 40 * 3900039 * 2
def baseEnd_3900039 : Nat := 667531526093457271058851

theorem tailTrace_3900039 : CollatzResearch.WordTrace tailWord_3900039 prefixEnd_3900039 667531526093457271058851 := by
  unfold tailWord_3900039
  simp only [CollatzResearch.WordTrace]
  refine ⟨142246108317832251477479171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94830738878554834318319447 142246108317832251477479171)
  ·
    refine ⟨213369162476748377216218757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142246108317832251477479171 213369162476748377216218757)
    ·
      refine ⟨40006717964390320728041017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213369162476748377216218757 40006717964390320728041017)
      ·
        refine ⟨30005038473292740546030763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40006717964390320728041017 30005038473292740546030763)
        ·
          refine ⟨45007557709939110819046145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30005038473292740546030763 45007557709939110819046145)
          ·
            refine ⟨33755668282454333114284609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45007557709939110819046145 33755668282454333114284609)
            ·
              refine ⟨25316751211840749835713457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33755668282454333114284609 25316751211840749835713457)
              ·
                refine ⟨18987563408880562376785093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25316751211840749835713457 18987563408880562376785093)
                ·
                  refine ⟨3560168139165105445647205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18987563408880562376785093 3560168139165105445647205)
                  ·
                    refine ⟨667531526093457271058851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560168139165105445647205 667531526093457271058851)
                    ·
                      rfl

theorem cell23_3900039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_3900039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900039 prefixEnd_3900039 := by exact prefixLift 3900039
  have htrace : WordTrace (prefixWord ++ tailWord_3900039) baseStart_3900039 baseEnd_3900039 := by
    simpa [prefixWord, tailWord_3900039, baseEnd_3900039] using wordTrace_append hprefix tailTrace_3900039
  have hstable : (prefixWord ++ tailWord_3900039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900039).length < 2 ^ (prefixWord ++ tailWord_3900039).sum := by decide
  have hdescent : baseEnd_3900039 < baseStart_3900039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900046 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3900046 : Nat := 118140960795 + 3900046 * 2 ^ 59
def prefixEnd_3900046 : Nat := 4983230072969 + 3 ^ 40 * 3900046 * 2
def baseEnd_3900046 : Nat := 2002598172644953285789021

theorem tailTrace_3900046 : CollatzResearch.WordTrace tailWord_3900046 prefixEnd_3900046 2002598172644953285789021 := by
  unfold tailWord_3900046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780795453600861459122999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94830909085871261115322661 17780795453600861459122999)
  ·
    refine ⟨26671193180401292188684499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17780795453600861459122999 26671193180401292188684499)
    ·
      refine ⟨40006789770601938283026749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26671193180401292188684499 40006789770601938283026749)
      ·
        refine ⟨15002546163975726856135031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40006789770601938283026749 15002546163975726856135031)
        ·
          refine ⟨22503819245963590284202547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15002546163975726856135031 22503819245963590284202547)
          ·
            refine ⟨33755728868945385426303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22503819245963590284202547 33755728868945385426303821)
            ·
              refine ⟨12658398325854519534863933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33755728868945385426303821 12658398325854519534863933)
              ·
                refine ⟨4746899372195444825573975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12658398325854519534863933 4746899372195444825573975)
                ·
                  refine ⟨7120349058293167238360963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4746899372195444825573975 7120349058293167238360963)
                  ·
                    refine ⟨10680523587439750857541445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120349058293167238360963 10680523587439750857541445)
                    ·
                      refine ⟨2002598172644953285789021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10680523587439750857541445 2002598172644953285789021)
                      ·
                        rfl

theorem cell23_3900046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3900046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900046 prefixEnd_3900046 := by exact prefixLift 3900046
  have htrace : WordTrace (prefixWord ++ tailWord_3900046) baseStart_3900046 baseEnd_3900046 := by
    simpa [prefixWord, tailWord_3900046, baseEnd_3900046] using wordTrace_append hprefix tailTrace_3900046
  have hstable : (prefixWord ++ tailWord_3900046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900046).length < 2 ^ (prefixWord ++ tailWord_3900046).sum := by decide
  have hdescent : baseEnd_3900046 < baseStart_3900046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900096 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_3900096 : Nat := 118140960795 + 3900096 * 2 ^ 59
def prefixEnd_3900096 : Nat := 4983230072969 + 3 ^ 40 * 3900096 * 2
def baseEnd_3900096 : Nat := 2002623846677678090163791

theorem tailTrace_3900096 : CollatzResearch.WordTrace tailWord_3900096 prefixEnd_3900096 2002623846677678090163791 := by
  unfold tailWord_3900096
  simp only [CollatzResearch.WordTrace]
  refine ⟨71124093639312875106152071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94832124852417166808202761 71124093639312875106152071)
  ·
    refine ⟨106686140458969312659228107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71124093639312875106152071 106686140458969312659228107)
    ·
      refine ⟨160029210688453968988842161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106686140458969312659228107 160029210688453968988842161)
      ·
        refine ⟨120021908016340476741631621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160029210688453968988842161 120021908016340476741631621)
        ·
          refine ⟨22504107753063839389055929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120021908016340476741631621 22504107753063839389055929)
          ·
            refine ⟨16878080814797879541791947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22504107753063839389055929 16878080814797879541791947)
            ·
              refine ⟨25317121222196819312687921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16878080814797879541791947 25317121222196819312687921)
              ·
                refine ⟨18987840916647614484515941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25317121222196819312687921 18987840916647614484515941)
                ·
                  refine ⟨3560220171871427715846739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18987840916647614484515941 3560220171871427715846739)
                  ·
                    refine ⟨5340330257807141573770109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560220171871427715846739 5340330257807141573770109)
                    ·
                      refine ⟨2002623846677678090163791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5340330257807141573770109 2002623846677678090163791)
                      ·
                        rfl

theorem cell23_3900096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_3900096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900096 prefixEnd_3900096 := by exact prefixLift 3900096
  have htrace : WordTrace (prefixWord ++ tailWord_3900096) baseStart_3900096 baseEnd_3900096 := by
    simpa [prefixWord, tailWord_3900096, baseEnd_3900096] using wordTrace_append hprefix tailTrace_3900096
  have hstable : (prefixWord ++ tailWord_3900096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900096).length < 2 ^ (prefixWord ++ tailWord_3900096).sum := by decide
  have hdescent : baseEnd_3900096 < baseStart_3900096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900114 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_3900114 : Nat := 118140960795 + 3900114 * 2 ^ 59
def prefixEnd_3900114 : Nat := 4983230072969 + 3 ^ 40 * 3900114 * 2
def baseEnd_3900114 : Nat := 2002633089329459019738709

theorem tailTrace_3900114 : CollatzResearch.WordTrace tailWord_3900114 prefixEnd_3900114 2002633089329459019738709 := by
  unfold tailWord_3900114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35562210948140134821614849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94832562528373692857639597 35562210948140134821614849)
  ·
    refine ⟨26671658211105101116211137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35562210948140134821614849 26671658211105101116211137)
    ·
      refine ⟨20003743658328825837158353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26671658211105101116211137 20003743658328825837158353)
      ·
        refine ⟨15002807743746619377868765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20003743658328825837158353 15002807743746619377868765)
        ·
          refine ⟨5626052903904982266700787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15002807743746619377868765 5626052903904982266700787)
          ·
            refine ⟨8439079355857473400051181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626052903904982266700787 8439079355857473400051181)
            ·
              refine ⟨3164654758446552525019193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8439079355857473400051181 3164654758446552525019193)
              ·
                refine ⟨2373491068834914393764395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164654758446552525019193 2373491068834914393764395)
                ·
                  refine ⟨3560236603252371590646593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373491068834914393764395 3560236603252371590646593)
                  ·
                    refine ⟨2670177452439278692984945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560236603252371590646593 2670177452439278692984945)
                    ·
                      refine ⟨2002633089329459019738709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670177452439278692984945 2002633089329459019738709)
                      ·
                        rfl

theorem cell23_3900114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_3900114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900114 prefixEnd_3900114 := by exact prefixLift 3900114
  have htrace : WordTrace (prefixWord ++ tailWord_3900114) baseStart_3900114 baseEnd_3900114 := by
    simpa [prefixWord, tailWord_3900114, baseEnd_3900114] using wordTrace_append hprefix tailTrace_3900114
  have hstable : (prefixWord ++ tailWord_3900114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900114).length < 2 ^ (prefixWord ++ tailWord_3900114).sum := by decide
  have hdescent : baseEnd_3900114 < baseStart_3900114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900170 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_3900170 : Nat := 118140960795 + 3900170 * 2 ^ 59
def prefixEnd_3900170 : Nat := 4983230072969 + 3 ^ 40 * 3900170 * 2
def baseEnd_3900170 : Nat := 2002661844246110800638451

theorem tailTrace_3900170 : CollatzResearch.WordTrace tailWord_3900170 prefixEnd_3900170 2002661844246110800638451 := by
  unfold tailWord_3900170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35562721570089415212624491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94833924186905107233665309 35562721570089415212624491)
  ·
    refine ⟨53344082355134122818936737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35562721570089415212624491 53344082355134122818936737)
    ·
      refine ⟨40008061766350592114202553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53344082355134122818936737 40008061766350592114202553)
      ·
        refine ⟨30006046324762944085651915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40008061766350592114202553 30006046324762944085651915)
        ·
          refine ⟨45009069487144416128477873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30006046324762944085651915 45009069487144416128477873)
          ·
            refine ⟨33756802115358312096358405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45009069487144416128477873 33756802115358312096358405)
            ·
              refine ⟨6329400396629683518067201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33756802115358312096358405 6329400396629683518067201)
              ·
                refine ⟨4747050297472262638550401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329400396629683518067201 4747050297472262638550401)
                ·
                  refine ⟨3560287723104196978912801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747050297472262638550401 3560287723104196978912801)
                  ·
                    refine ⟨2670215792328147734184601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560287723104196978912801 2670215792328147734184601)
                    ·
                      refine ⟨2002661844246110800638451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670215792328147734184601 2002661844246110800638451)
                      ·
                        rfl

theorem cell23_3900170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_3900170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900170 prefixEnd_3900170 := by exact prefixLift 3900170
  have htrace : WordTrace (prefixWord ++ tailWord_3900170) baseStart_3900170 baseEnd_3900170 := by
    simpa [prefixWord, tailWord_3900170, baseEnd_3900170] using wordTrace_append hprefix tailTrace_3900170
  have hstable : (prefixWord ++ tailWord_3900170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900170).length < 2 ^ (prefixWord ++ tailWord_3900170).sum := by decide
  have hdescent : baseEnd_3900170 < baseStart_3900170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900186 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_3900186 : Nat := 118140960795 + 3900186 * 2 ^ 59
def prefixEnd_3900186 : Nat := 4983230072969 + 3 ^ 40 * 3900186 * 2
def baseEnd_3900186 : Nat := 2002670059936582738038377

theorem tailTrace_3900186 : CollatzResearch.WordTrace tailWord_3900186 prefixEnd_3900186 2002670059936582738038377 := by
  unfold tailWord_3900186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35562867462074923895770103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94834313232199797055386941 35562867462074923895770103)
  ·
    refine ⟨53344301193112385843655155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35562867462074923895770103 53344301193112385843655155)
    ·
      refine ⟨80016451789668578765482733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53344301193112385843655155 80016451789668578765482733)
      ·
        refine ⟨30006169421125717037056025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80016451789668578765482733 30006169421125717037056025)
        ·
          refine ⟨22504627065844287777792019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30006169421125717037056025 22504627065844287777792019)
          ·
            refine ⟨33756940598766431666688029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22504627065844287777792019 33756940598766431666688029)
            ·
              refine ⟨12658852724537411875008011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33756940598766431666688029 12658852724537411875008011)
              ·
                refine ⟨18988279086806117812512017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658852724537411875008011 18988279086806117812512017)
                ·
                  refine ⟨14241209315104588359384013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18988279086806117812512017 14241209315104588359384013)
                  ·
                    refine ⟨5340453493164220634769005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14241209315104588359384013 5340453493164220634769005)
                    ·
                      refine ⟨2002670059936582738038377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5340453493164220634769005 2002670059936582738038377)
                      ·
                        rfl

theorem cell23_3900186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_3900186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900186 prefixEnd_3900186 := by exact prefixLift 3900186
  have htrace : WordTrace (prefixWord ++ tailWord_3900186) baseStart_3900186 baseEnd_3900186 := by
    simpa [prefixWord, tailWord_3900186, baseEnd_3900186] using wordTrace_append hprefix tailTrace_3900186
  have hstable : (prefixWord ++ tailWord_3900186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900186).length < 2 ^ (prefixWord ++ tailWord_3900186).sum := by decide
  have hdescent : baseEnd_3900186 < baseStart_3900186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900343 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 2, 4]
def baseStart_3900343 : Nat := 118140960795 + 3900343 * 2 ^ 59
def prefixEnd_3900343 : Nat := 4983230072969 + 3 ^ 40 * 3900343 * 2
def baseEnd_3900343 : Nat := 667583558799779541258385

theorem tailTrace_3900343 : CollatzResearch.WordTrace tailWord_3900343 prefixEnd_3900343 667583558799779541258385 := by
  unfold tailWord_3900343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142257196108730911396545683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94838130739153940931030455 142257196108730911396545683)
  ·
    refine ⟨213385794163096367094818525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142257196108730911396545683 213385794163096367094818525)
    ·
      refine ⟨80019672811161137660556947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213385794163096367094818525 80019672811161137660556947)
      ·
        refine ⟨120029509216741706490835421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80019672811161137660556947 120029509216741706490835421)
        ·
          refine ⟨45011065956278139934063283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120029509216741706490835421 45011065956278139934063283)
          ·
            refine ⟨67516598934417209901094925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45011065956278139934063283 67516598934417209901094925)
            ·
              refine ⟨25318724600406453712910597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67516598934417209901094925 25318724600406453712910597)
              ·
                refine ⟨4747260862576210071170737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25318724600406453712910597 4747260862576210071170737)
                ·
                  refine ⟨3560445646932157553378053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747260862576210071170737 3560445646932157553378053)
                  ·
                    refine ⟨667583558799779541258385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560445646932157553378053 667583558799779541258385)
                    ·
                      rfl

theorem cell23_3900343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_3900343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900343 prefixEnd_3900343 := by exact prefixLift 3900343
  have htrace : WordTrace (prefixWord ++ tailWord_3900343) baseStart_3900343 baseEnd_3900343 := by
    simpa [prefixWord, tailWord_3900343, baseEnd_3900343] using wordTrace_append hprefix tailTrace_3900343
  have hstable : (prefixWord ++ tailWord_3900343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900343).length < 2 ^ (prefixWord ++ tailWord_3900343).sum := by decide
  have hdescent : baseEnd_3900343 < baseStart_3900343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900344 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_3900344 : Nat := 118140960795 + 3900344 * 2 ^ 59
def prefixEnd_3900344 : Nat := 4983230072969 + 3 ^ 40 * 3900344 * 2
def baseEnd_3900344 : Nat := 2002751189879993119862651

theorem tailTrace_3900344 : CollatzResearch.WordTrace tailWord_3900344 prefixEnd_3900344 2002751189879993119862651 := by
  unfold tailWord_3900344
  simp only [CollatzResearch.WordTrace]
  refine ⟨71128616290863644283666043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94838155054484859044888057 71128616290863644283666043)
  ·
    refine ⟨106692924436295466425499065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71128616290863644283666043 106692924436295466425499065)
    ·
      refine ⟨80019693327221599819124299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106692924436295466425499065 80019693327221599819124299)
      ·
        refine ⟨120029539990832399728686449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80019693327221599819124299 120029539990832399728686449)
        ·
          refine ⟨90022154993124299796514837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120029539990832399728686449 90022154993124299796514837)
          ·
            refine ⟨4219788515302701552961633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90022154993124299796514837 4219788515302701552961633)
            ·
              refine ⟨3164841386477026164721225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219788515302701552961633 3164841386477026164721225)
              ·
                refine ⟨2373631039857769623540919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164841386477026164721225 2373631039857769623540919)
                ·
                  refine ⟨3560446559786654435311379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373631039857769623540919 3560446559786654435311379)
                  ·
                    refine ⟨5340669839679981652967069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560446559786654435311379 5340669839679981652967069)
                    ·
                      refine ⟨2002751189879993119862651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5340669839679981652967069 2002751189879993119862651)
                      ·
                        rfl

theorem cell23_3900344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_3900344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900344 prefixEnd_3900344 := by exact prefixLift 3900344
  have htrace : WordTrace (prefixWord ++ tailWord_3900344) baseStart_3900344 baseEnd_3900344 := by
    simpa [prefixWord, tailWord_3900344, baseEnd_3900344] using wordTrace_append hprefix tailTrace_3900344
  have hstable : (prefixWord ++ tailWord_3900344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900344).length < 2 ^ (prefixWord ++ tailWord_3900344).sum := by decide
  have hdescent : baseEnd_3900344 < baseStart_3900344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900346 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3900346 : Nat := 118140960795 + 3900346 * 2 ^ 59
def prefixEnd_3900346 : Nat := 4983230072969 + 3 ^ 40 * 3900346 * 2
def baseEnd_3900346 : Nat := 2002752216841302112037641

theorem tailTrace_3900346 : CollatzResearch.WordTrace tailWord_3900346 prefixEnd_3900346 2002752216841302112037641 := by
  unfold tailWord_3900346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564326381930010727226223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94838203685146695272603261 35564326381930010727226223)
  ·
    refine ⟨53346489572895016090839335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35564326381930010727226223 53346489572895016090839335)
    ·
      refine ⟨80019734359342524136259003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53346489572895016090839335 80019734359342524136259003)
      ·
        refine ⟨120029601539013786204388505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80019734359342524136259003 120029601539013786204388505)
        ·
          refine ⟨90022201154260339653291379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120029601539013786204388505 90022201154260339653291379)
          ·
            refine ⟨135033301731390509479937069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90022201154260339653291379 135033301731390509479937069)
            ·
              refine ⟨50637488149271441054976401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135033301731390509479937069 50637488149271441054976401)
              ·
                refine ⟨37978116111953580791232301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50637488149271441054976401 37978116111953580791232301)
                ·
                  refine ⟨14241793541982592796712113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37978116111953580791232301 14241793541982592796712113)
                  ·
                    refine ⟨10681345156486944597534085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14241793541982592796712113 10681345156486944597534085)
                    ·
                      refine ⟨2002752216841302112037641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10681345156486944597534085 2002752216841302112037641)
                      ·
                        rfl

theorem cell23_3900346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3900346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900346 prefixEnd_3900346 := by exact prefixLift 3900346
  have htrace : WordTrace (prefixWord ++ tailWord_3900346) baseStart_3900346 baseEnd_3900346 := by
    simpa [prefixWord, tailWord_3900346, baseEnd_3900346] using wordTrace_append hprefix tailTrace_3900346
  have hstable : (prefixWord ++ tailWord_3900346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900346).length < 2 ^ (prefixWord ++ tailWord_3900346).sum := by decide
  have hdescent : baseEnd_3900346 < baseStart_3900346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900363 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4]
def baseStart_3900363 : Nat := 118140960795 + 3900363 * 2 ^ 59
def prefixEnd_3900363 : Nat := 4983230072969 + 3 ^ 40 * 3900363 * 2
def baseEnd_3900363 : Nat := 2002760946012428545525063

theorem tailTrace_3900363 : CollatzResearch.WordTrace tailWord_3900363 prefixEnd_3900363 2002760946012428545525063 := by
  unfold tailWord_3900363
  simp only [CollatzResearch.WordTrace]
  refine ⟨142257925568658454812273743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94838617045772303208182495 142257925568658454812273743)
  ·
    refine ⟨213386888352987682218410615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142257925568658454812273743 213386888352987682218410615)
    ·
      refine ⟨320080332529481523327615923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213386888352987682218410615 320080332529481523327615923)
      ·
        refine ⟨480120498794222284991423885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320080332529481523327615923 480120498794222284991423885)
        ·
          refine ⟨180045187047833356871783957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480120498794222284991423885 180045187047833356871783957)
          ·
            refine ⟨8439618142867188603364873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180045187047833356871783957 8439618142867188603364873)
            ·
              refine ⟨6329713607150391452523655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439618142867188603364873 6329713607150391452523655)
              ·
                refine ⟨9494570410725587178785483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329713607150391452523655 9494570410725587178785483)
                ·
                  refine ⟨14241855616088380768178225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9494570410725587178785483 14241855616088380768178225)
                  ·
                    refine ⟨10681391712066285576133669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14241855616088380768178225 10681391712066285576133669)
                    ·
                      refine ⟨2002760946012428545525063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10681391712066285576133669 2002760946012428545525063)
                      ·
                        rfl

theorem cell23_3900363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 4].length) (baseStart_3900363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900363 prefixEnd_3900363 := by exact prefixLift 3900363
  have htrace : WordTrace (prefixWord ++ tailWord_3900363) baseStart_3900363 baseEnd_3900363 := by
    simpa [prefixWord, tailWord_3900363, baseEnd_3900363] using wordTrace_append hprefix tailTrace_3900363
  have hstable : (prefixWord ++ tailWord_3900363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900363).length < 2 ^ (prefixWord ++ tailWord_3900363).sum := by decide
  have hdescent : baseEnd_3900363 < baseStart_3900363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900370 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3900370 : Nat := 118140960795 + 3900370 * 2 ^ 59
def prefixEnd_3900370 : Nat := 4983230072969 + 3 ^ 40 * 3900370 * 2
def baseEnd_3900370 : Nat := 2002764540377010018137531

theorem tailTrace_3900370 : CollatzResearch.WordTrace tailWord_3900370 prefixEnd_3900370 2002764540377010018137531 := by
  unfold tailWord_3900370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564545219908273751944641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94838787253088730005185709 35564545219908273751944641)
  ·
    refine ⟨26673408914931205313958481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35564545219908273751944641 26673408914931205313958481)
    ·
      refine ⟨20005056686198403985468861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26673408914931205313958481 20005056686198403985468861)
      ·
        refine ⟨7501896257324401494550823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20005056686198403985468861 7501896257324401494550823)
        ·
          refine ⟨11252844385986602241826235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501896257324401494550823 11252844385986602241826235)
          ·
            refine ⟨16879266578979903362739353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11252844385986602241826235 16879266578979903362739353)
            ·
              refine ⟨12659449934234927522054515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16879266578979903362739353 12659449934234927522054515)
              ·
                refine ⟨18989174901352391283081773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659449934234927522054515 18989174901352391283081773)
                ·
                  refine ⟨7120940588007146731155665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18989174901352391283081773 7120940588007146731155665)
                  ·
                    refine ⟨5340705441005360048366749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7120940588007146731155665 5340705441005360048366749)
                    ·
                      refine ⟨2002764540377010018137531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5340705441005360048366749 2002764540377010018137531)
                      ·
                        rfl

theorem cell23_3900370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3900370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900370 prefixEnd_3900370 := by exact prefixLift 3900370
  have htrace : WordTrace (prefixWord ++ tailWord_3900370) baseStart_3900370 baseEnd_3900370 := by
    simpa [prefixWord, tailWord_3900370, baseEnd_3900370] using wordTrace_append hprefix tailTrace_3900370
  have hstable : (prefixWord ++ tailWord_3900370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900370).length < 2 ^ (prefixWord ++ tailWord_3900370).sum := by decide
  have hdescent : baseEnd_3900370 < baseStart_3900370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900414 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3900414 : Nat := 118140960795 + 3900414 * 2 ^ 59
def prefixEnd_3900414 : Nat := 4983230072969 + 3 ^ 40 * 3900414 * 2
def baseEnd_3900414 : Nat := 2002787133525807845987329

theorem tailTrace_3900414 : CollatzResearch.WordTrace tailWord_3900414 prefixEnd_3900414 2002787133525807845987329 := by
  unfold tailWord_3900414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17782473211434211315297537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94839857127649127014920197 17782473211434211315297537)
  ·
    refine ⟨13336854908575658486473153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17782473211434211315297537 13336854908575658486473153)
    ·
      refine ⟨10002641181431743864854865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13336854908575658486473153 10002641181431743864854865)
      ·
        refine ⟨7501980886073807898641149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10002641181431743864854865 7501980886073807898641149)
        ·
          refine ⟨2813242832277677961990431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7501980886073807898641149 2813242832277677961990431)
          ·
            refine ⟨4219864248416516942985647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813242832277677961990431 4219864248416516942985647)
            ·
              refine ⟨6329796372624775414478471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219864248416516942985647 6329796372624775414478471)
              ·
                refine ⟨9494694558937163121717707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329796372624775414478471 9494694558937163121717707)
                ·
                  refine ⟨14242041838405744682576561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9494694558937163121717707 14242041838405744682576561)
                  ·
                    refine ⟨10681531378804308511932421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14242041838405744682576561 10681531378804308511932421)
                    ·
                      refine ⟨2002787133525807845987329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10681531378804308511932421 2002787133525807845987329)
                      ·
                        rfl

theorem cell23_3900414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3900414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900414 prefixEnd_3900414 := by exact prefixLift 3900414
  have htrace : WordTrace (prefixWord ++ tailWord_3900414) baseStart_3900414 baseEnd_3900414 := by
    simpa [prefixWord, tailWord_3900414, baseEnd_3900414] using wordTrace_append hprefix tailTrace_3900414
  have hstable : (prefixWord ++ tailWord_3900414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900414).length < 2 ^ (prefixWord ++ tailWord_3900414).sum := by decide
  have hdescent : baseEnd_3900414 < baseStart_3900414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900427 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 1, 3, 2]
def baseStart_3900427 : Nat := 118140960795 + 3900427 * 2 ^ 59
def prefixEnd_3900427 : Nat := 4983230072969 + 3 ^ 40 * 3900427 * 2
def baseEnd_3900427 : Nat := 2002793808774316295124769

theorem tailTrace_3900427 : CollatzResearch.WordTrace tailWord_3900427 prefixEnd_3900427 2002793808774316295124769 := by
  unfold tailWord_3900427
  simp only [CollatzResearch.WordTrace]
  refine ⟨142260259840426593742603535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94840173226951062495069023 142260259840426593742603535)
  ·
    refine ⟨213390389760639890613905303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142260259840426593742603535 213390389760639890613905303)
    ·
      refine ⟨320085584640959835920857955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213390389760639890613905303 320085584640959835920857955)
      ·
        refine ⟨480128376961439753881286933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320085584640959835920857955 480128376961439753881286933)
        ·
          refine ⟨22506017670067488463185325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 480128376961439753881286933 22506017670067488463185325)
          ·
            refine ⟨8439756626275308173694497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22506017670067488463185325 8439756626275308173694497)
            ·
              refine ⟨6329817469706481130270873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8439756626275308173694497 6329817469706481130270873)
              ·
                refine ⟨4747363102279860847703155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6329817469706481130270873 4747363102279860847703155)
                ·
                  refine ⟨7121044653419791271554733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747363102279860847703155 7121044653419791271554733)
                  ·
                    refine ⟨2670391745032421726833025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7121044653419791271554733 2670391745032421726833025)
                    ·
                      refine ⟨2002793808774316295124769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670391745032421726833025 2002793808774316295124769)
                      ·
                        rfl

theorem cell23_3900427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3, 2].length) (baseStart_3900427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900427 prefixEnd_3900427 := by exact prefixLift 3900427
  have htrace : WordTrace (prefixWord ++ tailWord_3900427) baseStart_3900427 baseEnd_3900427 := by
    simpa [prefixWord, tailWord_3900427, baseEnd_3900427] using wordTrace_append hprefix tailTrace_3900427
  have hstable : (prefixWord ++ tailWord_3900427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900427).length < 2 ^ (prefixWord ++ tailWord_3900427).sum := by decide
  have hdescent : baseEnd_3900427 < baseStart_3900427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900474 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_3900474 : Nat := 118140960795 + 3900474 * 2 ^ 59
def prefixEnd_3900474 : Nat := 4983230072969 + 3 ^ 40 * 3900474 * 2
def baseEnd_3900474 : Nat := 2002817942365077611237053

theorem tailTrace_3900474 : CollatzResearch.WordTrace tailWord_3900474 prefixEnd_3900474 2002817942365077611237053 := by
  unfold tailWord_3900474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35565493517814080192391119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94841316047504213846376317 35565493517814080192391119)
  ·
    refine ⟨53348240276721120288586679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35565493517814080192391119 53348240276721120288586679)
    ·
      refine ⟨80022360415081680432880019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53348240276721120288586679 80022360415081680432880019)
      ·
        refine ⟨120033540622622520649320029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80022360415081680432880019 120033540622622520649320029)
        ·
          refine ⟨45012577733483445243495011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120033540622622520649320029 45012577733483445243495011)
          ·
            refine ⟨67518866600225167865242517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45012577733483445243495011 67518866600225167865242517)
            ·
              refine ⟨3164946871885554743683243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67518866600225167865242517 3164946871885554743683243)
              ·
                refine ⟨4747420307828332115524865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3164946871885554743683243 4747420307828332115524865)
                ·
                  refine ⟨3560565230871249086643649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4747420307828332115524865 3560565230871249086643649)
                  ·
                    refine ⟨2670423923153436814982737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560565230871249086643649 2670423923153436814982737)
                    ·
                      refine ⟨2002817942365077611237053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670423923153436814982737 2002817942365077611237053)
                      ·
                        rfl

theorem cell23_3900474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_3900474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900474 prefixEnd_3900474 := by exact prefixLift 3900474
  have htrace : WordTrace (prefixWord ++ tailWord_3900474) baseStart_3900474 baseEnd_3900474 := by
    simpa [prefixWord, tailWord_3900474, baseEnd_3900474] using wordTrace_append hprefix tailTrace_3900474
  have hstable : (prefixWord ++ tailWord_3900474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900474).length < 2 ^ (prefixWord ++ tailWord_3900474).sum := by decide
  have hdescent : baseEnd_3900474 < baseStart_3900474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900514 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3900514 : Nat := 118140960795 + 3900514 * 2 ^ 59
def prefixEnd_3900514 : Nat := 4983230072969 + 3 ^ 40 * 3900514 * 2
def baseEnd_3900514 : Nat := 222537609065695272748541

theorem tailTrace_3900514 : CollatzResearch.WordTrace tailWord_3900514 prefixEnd_3900514 222537609065695272748541 := by
  unfold tailWord_3900514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35565858247777851900255149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94842288660740938400680397 35565858247777851900255149)
  ·
    refine ⟨13337196842916694462595681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35565858247777851900255149 13337196842916694462595681)
    ·
      refine ⟨10002897632187520846946761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13337196842916694462595681 10002897632187520846946761)
      ·
        refine ⟨7502173224140640635210071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10002897632187520846946761 7502173224140640635210071)
        ·
          refine ⟨11253259836210960952815107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502173224140640635210071 11253259836210960952815107)
          ·
            refine ⟨16879889754316441429222661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253259836210960952815107 16879889754316441429222661)
            ·
              refine ⟨3164979328934332767979249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16879889754316441429222661 3164979328934332767979249)
              ·
                refine ⟨2373734496700749575984437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164979328934332767979249 2373734496700749575984437)
                ·
                  refine ⟨222537609065695272748541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2373734496700749575984437 222537609065695272748541)
                  ·
                    rfl

theorem cell23_3900514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3900514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900514 prefixEnd_3900514 := by exact prefixLift 3900514
  have htrace : WordTrace (prefixWord ++ tailWord_3900514) baseStart_3900514 baseEnd_3900514 := by
    simpa [prefixWord, tailWord_3900514, baseEnd_3900514] using wordTrace_append hprefix tailTrace_3900514
  have hstable : (prefixWord ++ tailWord_3900514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900514).length < 2 ^ (prefixWord ++ tailWord_3900514).sum := by decide
  have hdescent : baseEnd_3900514 < baseStart_3900514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900523 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 9, 4]
def baseStart_3900523 : Nat := 118140960795 + 3900523 * 2 ^ 59
def prefixEnd_3900523 : Nat := 4983230072969 + 3 ^ 40 * 3900523 * 2
def baseEnd_3900523 : Nat := 667614367639049306508109

theorem tailTrace_3900523 : CollatzResearch.WordTrace tailWord_3900523 prefixEnd_3900523 667614367639049306508109 := by
  unfold tailWord_3900523
  simp only [CollatzResearch.WordTrace]
  refine ⟨142263761248078802138098223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94842507498719201425398815 142263761248078802138098223)
  ·
    refine ⟨213395641872118203207147335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142263761248078802138098223 213395641872118203207147335)
    ·
      refine ⟨320093462808177304810721003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213395641872118203207147335 320093462808177304810721003)
      ·
        refine ⟨480140194212265957216081505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320093462808177304810721003 480140194212265957216081505)
        ·
          refine ⟨360105145659199467912061129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480140194212265957216081505 360105145659199467912061129)
          ·
            refine ⟨270078859244399600934045847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360105145659199467912061129 270078859244399600934045847)
            ·
              refine ⟨405118288866599401401068771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270078859244399600934045847 405118288866599401401068771)
              ·
                refine ⟨607677433299899102101603157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405118288866599401401068771 607677433299899102101603157)
                ·
                  refine ⟨3560609960741596301376581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 607677433299899102101603157 3560609960741596301376581)
                  ·
                    refine ⟨667614367639049306508109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560609960741596301376581 667614367639049306508109)
                    ·
                      rfl

theorem cell23_3900523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 4].length) (baseStart_3900523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900523 prefixEnd_3900523 := by exact prefixLift 3900523
  have htrace : WordTrace (prefixWord ++ tailWord_3900523) baseStart_3900523 baseEnd_3900523 := by
    simpa [prefixWord, tailWord_3900523, baseEnd_3900523] using wordTrace_append hprefix tailTrace_3900523
  have hstable : (prefixWord ++ tailWord_3900523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900523).length < 2 ^ (prefixWord ++ tailWord_3900523).sum := by decide
  have hdescent : baseEnd_3900523 < baseStart_3900523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900540 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_3900540 : Nat := 118140960795 + 3900540 * 2 ^ 59
def prefixEnd_3900540 : Nat := 4983230072969 + 3 ^ 40 * 3900540 * 2
def baseEnd_3900540 : Nat := 667617277362758117670583

theorem tailTrace_3900540 : CollatzResearch.WordTrace tailWord_3900540 prefixEnd_3900540 667617277362758117670583 := by
  unfold tailWord_3900540
  simp only [CollatzResearch.WordTrace]
  refine ⟨71132190644508607020733537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94842920859344809360978049 71132190644508607020733537)
  ·
    refine ⟨53349142983381455265550153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71132190644508607020733537 53349142983381455265550153)
    ·
      refine ⟨40011857237536091449162615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53349142983381455265550153 40011857237536091449162615)
      ·
        refine ⟨60017785856304137173743923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40011857237536091449162615 60017785856304137173743923)
        ·
          refine ⟨90026678784456205760615885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60017785856304137173743923 90026678784456205760615885)
          ·
            refine ⟨33760004544171077160230957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90026678784456205760615885 33760004544171077160230957)
            ·
              refine ⟨12660001704064153935086609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33760004544171077160230957 12660001704064153935086609)
              ·
                refine ⟨9495001278048115451314957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660001704064153935086609 9495001278048115451314957)
                ·
                  refine ⟨3560625479268043294243109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495001278048115451314957 3560625479268043294243109)
                  ·
                    refine ⟨667617277362758117670583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560625479268043294243109 667617277362758117670583)
                    ·
                      rfl

theorem cell23_3900540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_3900540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900540 prefixEnd_3900540 := by exact prefixLift 3900540
  have htrace : WordTrace (prefixWord ++ tailWord_3900540) baseStart_3900540 baseEnd_3900540 := by
    simpa [prefixWord, tailWord_3900540, baseEnd_3900540] using wordTrace_append hprefix tailTrace_3900540
  have hstable : (prefixWord ++ tailWord_3900540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900540).length < 2 ^ (prefixWord ++ tailWord_3900540).sum := by decide
  have hdescent : baseEnd_3900540 < baseStart_3900540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900570 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_3900570 : Nat := 118140960795 + 3900570 * 2 ^ 59
def prefixEnd_3900570 : Nat := 4983230072969 + 3 ^ 40 * 3900570 * 2
def baseEnd_3900570 : Nat := 222540804056434359515179

theorem tailTrace_3900570 : CollatzResearch.WordTrace tailWord_3900570 prefixEnd_3900570 222540804056434359515179 := by
  unfold tailWord_3900570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566368869727132291264791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94843650319272352776706109 35566368869727132291264791)
  ·
    refine ⟨53349553304590698436897187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566368869727132291264791 53349553304590698436897187)
    ·
      refine ⟨80024329956886047655345781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53349553304590698436897187 80024329956886047655345781)
      ·
        refine ⟨7502280933458066967688667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80024329956886047655345781 7502280933458066967688667)
        ·
          refine ⟨11253421400187100451533001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502280933458066967688667 11253421400187100451533001)
          ·
            refine ⟨8440066050140325338649751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253421400187100451533001 8440066050140325338649751)
            ·
              refine ⟨12660099075210488007974627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440066050140325338649751 12660099075210488007974627)
              ·
                refine ⟨18990148612815732011961941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660099075210488007974627 18990148612815732011961941)
                ·
                  refine ⟨222540804056434359515179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18990148612815732011961941 222540804056434359515179)
                  ·
                    rfl

theorem cell23_3900570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_3900570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900570 prefixEnd_3900570 := by exact prefixLift 3900570
  have htrace : WordTrace (prefixWord ++ tailWord_3900570) baseStart_3900570 baseEnd_3900570 := by
    simpa [prefixWord, tailWord_3900570, baseEnd_3900570] using wordTrace_append hprefix tailTrace_3900570
  have hstable : (prefixWord ++ tailWord_3900570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900570).length < 2 ^ (prefixWord ++ tailWord_3900570).sum := by decide
  have hdescent : baseEnd_3900570 < baseStart_3900570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900573 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3900573 : Nat := 118140960795 + 3900573 * 2 ^ 59
def prefixEnd_3900573 : Nat := 4983230072969 + 3 ^ 40 * 3900573 * 2
def baseEnd_3900573 : Nat := 2002868776949872723899097

theorem tailTrace_3900573 : CollatzResearch.WordTrace tailWord_3900573 prefixEnd_3900573 2002868776949872723899097 := by
  unfold tailWord_3900573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142265584897897660677418373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94843723265265107118278915 142265584897897660677418373)
  ·
    refine ⟨26674797168355811377015945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142265584897897660677418373 26674797168355811377015945)
    ·
      refine ⟨20006097876266858532761959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26674797168355811377015945 20006097876266858532761959)
      ·
        refine ⟨30009146814400287799142939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20006097876266858532761959 30009146814400287799142939)
        ·
          refine ⟨45013720221600431698714409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009146814400287799142939 45013720221600431698714409)
          ·
            refine ⟨33760290166200323774035807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45013720221600431698714409 33760290166200323774035807)
            ·
              refine ⟨50640435249300485661053711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33760290166200323774035807 50640435249300485661053711)
              ·
                refine ⟨75960652873950728491580567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50640435249300485661053711 75960652873950728491580567)
                ·
                  refine ⟨113940979310926092737370851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75960652873950728491580567 113940979310926092737370851)
                  ·
                    refine ⟨170911468966389139106056277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113940979310926092737370851 170911468966389139106056277)
                    ·
                      refine ⟨2002868776949872723899097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 170911468966389139106056277 2002868776949872723899097)
                      ·
                        rfl

theorem cell23_3900573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3900573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900573 prefixEnd_3900573 := by exact prefixLift 3900573
  have htrace : WordTrace (prefixWord ++ tailWord_3900573) baseStart_3900573 baseEnd_3900573 := by
    simpa [prefixWord, tailWord_3900573, baseEnd_3900573] using wordTrace_append hprefix tailTrace_3900573
  have hstable : (prefixWord ++ tailWord_3900573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900573).length < 2 ^ (prefixWord ++ tailWord_3900573).sum := by decide
  have hdescent : baseEnd_3900573 < baseStart_3900573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900574 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3900574 : Nat := 118140960795 + 3900574 * 2 ^ 59
def prefixEnd_3900574 : Nat := 4983230072969 + 3 ^ 40 * 3900574 * 2
def baseEnd_3900574 : Nat := 667623096810175739995531

theorem tailTrace_3900574 : CollatzResearch.WordTrace tailWord_3900574 prefixEnd_3900574 667623096810175739995531 := by
  unfold tailWord_3900574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783202671361754731025597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94843747580596025232136517 17783202671361754731025597)
  ·
    refine ⟨6668701001760658024134599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17783202671361754731025597 6668701001760658024134599)
    ·
      refine ⟨10003051502640987036201899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6668701001760658024134599 10003051502640987036201899)
      ·
        refine ⟨15004577253961480554302849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10003051502640987036201899 15004577253961480554302849)
        ·
          refine ⟨11253432940471110415727137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15004577253961480554302849 11253432940471110415727137)
          ·
            refine ⟨8440074705353332811795353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253432940471110415727137 8440074705353332811795353)
            ·
              refine ⟨6330056029014999608846515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440074705353332811795353 6330056029014999608846515)
              ·
                refine ⟨9495084043522499413269773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330056029014999608846515 9495084043522499413269773)
                ·
                  refine ⟨3560656516320937279976165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495084043522499413269773 3560656516320937279976165)
                  ·
                    refine ⟨667623096810175739995531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560656516320937279976165 667623096810175739995531)
                    ·
                      rfl

theorem cell23_3900574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3900574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900574 prefixEnd_3900574 := by exact prefixLift 3900574
  have htrace : WordTrace (prefixWord ++ tailWord_3900574) baseStart_3900574 baseEnd_3900574 := by
    simpa [prefixWord, tailWord_3900574, baseEnd_3900574] using wordTrace_append hprefix tailTrace_3900574
  have hstable : (prefixWord ++ tailWord_3900574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900574).length < 2 ^ (prefixWord ++ tailWord_3900574).sum := by decide
  have hdescent : baseEnd_3900574 < baseStart_3900574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900613 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3900613 : Nat := 118140960795 + 3900613 * 2 ^ 59
def prefixEnd_3900613 : Nat := 4983230072969 + 3 ^ 40 * 3900613 * 2
def baseEnd_3900613 : Nat := 667629772058684189132971

theorem tailTrace_3900613 : CollatzResearch.WordTrace tailWord_3900613 prefixEnd_3900613 667629772058684189132971 := by
  unfold tailWord_3900613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142267043817752747508874493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94844695878501831672582995 142267043817752747508874493)
  ·
    refine ⟨53350141431657280315827935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142267043817752747508874493 53350141431657280315827935)
    ·
      refine ⟨80025212147485920473741903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53350141431657280315827935 80025212147485920473741903)
      ·
        refine ⟨120037818221228880710612855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80025212147485920473741903 120037818221228880710612855)
        ·
          refine ⟨180056727331843321065919283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120037818221228880710612855 180056727331843321065919283)
          ·
            refine ⟨270085090997764981598878925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180056727331843321065919283 270085090997764981598878925)
            ·
              refine ⟨101281909124161868099579597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270085090997764981598878925 101281909124161868099579597)
              ·
                refine ⟨37980715921560700537342349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101281909124161868099579597 37980715921560700537342349)
                ·
                  refine ⟨14242768470585262701503381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37980715921560700537342349 14242768470585262701503381)
                  ·
                    refine ⟨667629772058684189132971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14242768470585262701503381 667629772058684189132971)
                    ·
                      rfl

theorem cell23_3900613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3900613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900613 prefixEnd_3900613 := by exact prefixLift 3900613
  have htrace : WordTrace (prefixWord ++ tailWord_3900613) baseStart_3900613 baseEnd_3900613 := by
    simpa [prefixWord, tailWord_3900613, baseEnd_3900613] using wordTrace_append hprefix tailTrace_3900613
  have hstable : (prefixWord ++ tailWord_3900613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900613).length < 2 ^ (prefixWord ++ tailWord_3900613).sum := by decide
  have hdescent : baseEnd_3900613 < baseStart_3900613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900640 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3900640 : Nat := 118140960795 + 3900640 * 2 ^ 59
def prefixEnd_3900640 : Nat := 4983230072969 + 3 ^ 40 * 3900640 * 2
def baseEnd_3900640 : Nat := 2002903180153723961761289

theorem tailTrace_3900640 : CollatzResearch.WordTrace tailWord_3900640 prefixEnd_3900640 2002903180153723961761289 := by
  unfold tailWord_3900640
  simp only [CollatzResearch.WordTrace]
  refine ⟨71134014294327465560053687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94845352392436620746738249 71134014294327465560053687)
  ·
    refine ⟨106701021441491198340080531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71134014294327465560053687 106701021441491198340080531)
    ·
      refine ⟨160051532162236797510120797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106701021441491198340080531 160051532162236797510120797)
      ·
        refine ⟨60019324560838799066295299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160051532162236797510120797 60019324560838799066295299)
        ·
          refine ⟨90028986841258198599442949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60019324560838799066295299 90028986841258198599442949)
          ·
            refine ⟨16880435032735912237395553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90028986841258198599442949 16880435032735912237395553)
            ·
              refine ⟨12660326274551934178046665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880435032735912237395553 12660326274551934178046665)
              ·
                refine ⟨9495244705913950633534999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660326274551934178046665 9495244705913950633534999)
                ·
                  refine ⟨14242867058870925950302499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495244705913950633534999 14242867058870925950302499)
                  ·
                    refine ⟨21364300588306388925453749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14242867058870925950302499 21364300588306388925453749)
                    ·
                      refine ⟨2002903180153723961761289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21364300588306388925453749 2002903180153723961761289)
                      ·
                        rfl

theorem cell23_3900640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3900640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900640 prefixEnd_3900640 := by exact prefixLift 3900640
  have htrace : WordTrace (prefixWord ++ tailWord_3900640) baseStart_3900640 baseEnd_3900640 := by
    simpa [prefixWord, tailWord_3900640, baseEnd_3900640] using wordTrace_append hprefix tailTrace_3900640
  have hstable : (prefixWord ++ tailWord_3900640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900640).length < 2 ^ (prefixWord ++ tailWord_3900640).sum := by decide
  have hdescent : baseEnd_3900640 < baseStart_3900640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900650 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3900650 : Nat := 118140960795 + 3900650 * 2 ^ 59
def prefixEnd_3900650 : Nat := 4983230072969 + 3 ^ 40 * 3900650 * 2
def baseEnd_3900650 : Nat := 2002908314960268922636243

theorem tailTrace_3900650 : CollatzResearch.WordTrace tailWord_3900650 prefixEnd_3900650 2002908314960268922636243 := by
  unfold tailWord_3900650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35567098329654675706992851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94845595545745801885314269 35567098329654675706992851)
  ·
    refine ⟨53350647494482013560489277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35567098329654675706992851 53350647494482013560489277)
    ·
      refine ⟨20006492810430755085183479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53350647494482013560489277 20006492810430755085183479)
      ·
        refine ⟨30009739215646132627775219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20006492810430755085183479 30009739215646132627775219)
        ·
          refine ⟨45014608823469198941662829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009739215646132627775219 45014608823469198941662829)
          ·
            refine ⟨16880478308800949603123561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45014608823469198941662829 16880478308800949603123561)
            ·
              refine ⟨12660358731600712202342671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880478308800949603123561 12660358731600712202342671)
              ·
                refine ⟨18990538097401068303514007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660358731600712202342671 18990538097401068303514007)
                ·
                  refine ⟨28485807146101602455271011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18990538097401068303514007 28485807146101602455271011)
                  ·
                    refine ⟨42728710719152403682906517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28485807146101602455271011 42728710719152403682906517)
                    ·
                      refine ⟨2002908314960268922636243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42728710719152403682906517 2002908314960268922636243)
                      ·
                        rfl

theorem cell23_3900650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3900650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900650 prefixEnd_3900650 := by exact prefixLift 3900650
  have htrace : WordTrace (prefixWord ++ tailWord_3900650) baseStart_3900650 baseEnd_3900650 := by
    simpa [prefixWord, tailWord_3900650, baseEnd_3900650] using wordTrace_append hprefix tailTrace_3900650
  have hstable : (prefixWord ++ tailWord_3900650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900650).length < 2 ^ (prefixWord ++ tailWord_3900650).sum := by decide
  have hdescent : baseEnd_3900650 < baseStart_3900650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900654 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_3900654 : Nat := 118140960795 + 3900654 * 2 ^ 59
def prefixEnd_3900654 : Nat := 4983230072969 + 3 ^ 40 * 3900654 * 2
def baseEnd_3900654 : Nat := 2002910368882886906986225

theorem tailTrace_3900654 : CollatzResearch.WordTrace tailWord_3900654 prefixEnd_3900654 2002910368882886906986225 := by
  unfold tailWord_3900654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783567401325526438889627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94845692807069474340744677 17783567401325526438889627)
  ·
    refine ⟨26675351101988289658334441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17783567401325526438889627 26675351101988289658334441)
    ·
      refine ⟨20006513326491217243750831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26675351101988289658334441 20006513326491217243750831)
      ·
        refine ⟨30009769989736825865626247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20006513326491217243750831 30009769989736825865626247)
        ·
          refine ⟨45014654984605238798439371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009769989736825865626247 45014654984605238798439371)
          ·
            refine ⟨67521982476907858197659057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45014654984605238798439371 67521982476907858197659057)
            ·
              refine ⟨50641486857680893648244293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67521982476907858197659057 50641486857680893648244293)
              ·
                refine ⟨9495278785815167559045805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50641486857680893648244293 9495278785815167559045805)
                ·
                  refine ⟨3560729544680687834642177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495278785815167559045805 3560729544680687834642177)
                  ·
                    refine ⟨2670547158510515875981633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3560729544680687834642177 2670547158510515875981633)
                    ·
                      refine ⟨2002910368882886906986225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670547158510515875981633 2002910368882886906986225)
                      ·
                        rfl

theorem cell23_3900654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_3900654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900654 prefixEnd_3900654 := by exact prefixLift 3900654
  have htrace : WordTrace (prefixWord ++ tailWord_3900654) baseStart_3900654 baseEnd_3900654 := by
    simpa [prefixWord, tailWord_3900654, baseEnd_3900654] using wordTrace_append hprefix tailTrace_3900654
  have hstable : (prefixWord ++ tailWord_3900654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900654).length < 2 ^ (prefixWord ++ tailWord_3900654).sum := by decide
  have hdescent : baseEnd_3900654 < baseStart_3900654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_3900663 : Nat := 118140960795 + 3900663 * 2 ^ 59
def prefixEnd_3900663 : Nat := 4983230072969 + 3 ^ 40 * 3900663 * 2
def baseEnd_3900663 : Nat := 2002914990208777371773683

theorem tailTrace_3900663 : CollatzResearch.WordTrace tailWord_3900663 prefixEnd_3900663 2002914990208777371773683 := by
  unfold tailWord_3900663
  simp only [CollatzResearch.WordTrace]
  refine ⟨142268867467571606048194643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94845911645047737365463095 142268867467571606048194643)
  ·
    refine ⟨213403301201357409072291965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142268867467571606048194643 213403301201357409072291965)
    ·
      refine ⟨80026237950509028402109487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213403301201357409072291965 80026237950509028402109487)
      ·
        refine ⟨120039356925763542603164231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80026237950509028402109487 120039356925763542603164231)
        ·
          refine ⟨180059035388645313904746347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120039356925763542603164231 180059035388645313904746347)
          ·
            refine ⟨270088553082967970857119521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180059035388645313904746347 270088553082967970857119521)
            ·
              refine ⟨202566414812225978142839641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270088553082967970857119521 202566414812225978142839641)
              ·
                refine ⟨151924811109169483607129731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202566414812225978142839641 151924811109169483607129731)
                ·
                  refine ⟨227887216663754225410694597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151924811109169483607129731 227887216663754225410694597)
                  ·
                    refine ⟨42728853124453917264505237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227887216663754225410694597 42728853124453917264505237)
                    ·
                      refine ⟨2002914990208777371773683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42728853124453917264505237 2002914990208777371773683)
                      ·
                        rfl

theorem cell23_3900663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_3900663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900663 prefixEnd_3900663 := by exact prefixLift 3900663
  have htrace : WordTrace (prefixWord ++ tailWord_3900663) baseStart_3900663 baseEnd_3900663 := by
    simpa [prefixWord, tailWord_3900663, baseEnd_3900663] using wordTrace_append hprefix tailTrace_3900663
  have hstable : (prefixWord ++ tailWord_3900663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900663).length < 2 ^ (prefixWord ++ tailWord_3900663).sum := by decide
  have hdescent : baseEnd_3900663 < baseStart_3900663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900704 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3900704 : Nat := 118140960795 + 3900704 * 2 ^ 59
def prefixEnd_3900704 : Nat := 4983230072969 + 3 ^ 40 * 3900704 * 2
def baseEnd_3900704 : Nat := 2002936042915611711360995

theorem tailTrace_3900704 : CollatzResearch.WordTrace tailWord_3900704 prefixEnd_3900704 2002936042915611711360995 := by
  unfold tailWord_3900704
  simp only [CollatzResearch.WordTrace]
  refine ⟨71135181430211535025218583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94846908573615380033624777 71135181430211535025218583)
  ·
    refine ⟨106702772145317302537827875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71135181430211535025218583 106702772145317302537827875)
    ·
      refine ⟨160054158217975953806741813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106702772145317302537827875 160054158217975953806741813)
      ·
        refine ⟨15005077332935245669382045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160054158217975953806741813 15005077332935245669382045)
        ·
          refine ⟨5626903999850717126018267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15005077332935245669382045 5626903999850717126018267)
          ·
            refine ⟨8440355999776075689027401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626903999850717126018267 8440355999776075689027401)
            ·
              refine ⟨6330266999832056766770551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440355999776075689027401 6330266999832056766770551)
              ·
                refine ⟨9495400499748085150155827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330266999832056766770551 9495400499748085150155827)
                ·
                  refine ⟨14243100749622127725233741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495400499748085150155827 14243100749622127725233741)
                  ·
                    refine ⟨5341162781108297896962653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14243100749622127725233741 5341162781108297896962653)
                    ·
                      refine ⟨2002936042915611711360995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341162781108297896962653 2002936042915611711360995)
                      ·
                        rfl

theorem cell23_3900704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3900704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900704 prefixEnd_3900704 := by exact prefixLift 3900704
  have htrace : WordTrace (prefixWord ++ tailWord_3900704) baseStart_3900704 baseEnd_3900704 := by
    simpa [prefixWord, tailWord_3900704, baseEnd_3900704] using wordTrace_append hprefix tailTrace_3900704
  have hstable : (prefixWord ++ tailWord_3900704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900704).length < 2 ^ (prefixWord ++ tailWord_3900704).sum := by decide
  have hdescent : baseEnd_3900704 < baseStart_3900704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900730 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3900730 : Nat := 118140960795 + 3900730 * 2 ^ 59
def prefixEnd_3900730 : Nat := 4983230072969 + 3 ^ 40 * 3900730 * 2
def baseEnd_3900730 : Nat := 2002949393412628609635875

theorem tailTrace_3900730 : CollatzResearch.WordTrace tailWord_3900730 prefixEnd_3900730 2002949393412628609635875 := by
  unfold tailWord_3900730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35567827789582219122720911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94847540772219250993922429 35567827789582219122720911)
  ·
    refine ⟨53351741684373328684081367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35567827789582219122720911 53351741684373328684081367)
    ·
      refine ⟨80027612526559993026122051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53351741684373328684081367 80027612526559993026122051)
      ·
        refine ⟨120041418789839989539183077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80027612526559993026122051 120041418789839989539183077)
        ·
          refine ⟨22507766023094998038596827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120041418789839989539183077 22507766023094998038596827)
          ·
            refine ⟨33761649034642497057895241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22507766023094998038596827 33761649034642497057895241)
            ·
              refine ⟨25321236775981872793421431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33761649034642497057895241 25321236775981872793421431)
              ·
                refine ⟨37981855163972809190132147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25321236775981872793421431 37981855163972809190132147)
                ·
                  refine ⟨56972782745959213785198221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37981855163972809190132147 56972782745959213785198221)
                  ·
                    refine ⟨21364793529734705169449333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56972782745959213785198221 21364793529734705169449333)
                    ·
                      refine ⟨2002949393412628609635875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21364793529734705169449333 2002949393412628609635875)
                      ·
                        rfl

theorem cell23_3900730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3900730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900730 prefixEnd_3900730 := by exact prefixLift 3900730
  have htrace : WordTrace (prefixWord ++ tailWord_3900730) baseStart_3900730 baseEnd_3900730 := by
    simpa [prefixWord, tailWord_3900730, baseEnd_3900730] using wordTrace_append hprefix tailTrace_3900730
  have hstable : (prefixWord ++ tailWord_3900730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900730).length < 2 ^ (prefixWord ++ tailWord_3900730).sum := by decide
  have hdescent : baseEnd_3900730 < baseStart_3900730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900737 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3900737 : Nat := 118140960795 + 3900737 * 2 ^ 59
def prefixEnd_3900737 : Nat := 4983230072969 + 3 ^ 40 * 3900737 * 2
def baseEnd_3900737 : Nat := 667650995925736694082781

theorem tailTrace_3900737 : CollatzResearch.WordTrace tailWord_3900737 prefixEnd_3900737 667650995925736694082781 := by
  unfold tailWord_3900737
  simp only [CollatzResearch.WordTrace]
  refine ⟨142271566469303516686388465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94847710979535677790925643 142271566469303516686388465)
  ·
    refine ⟨106703674851977637514791349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142271566469303516686388465 106703674851977637514791349)
    ·
      refine ⟨10003469517372903517011689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106703674851977637514791349 10003469517372903517011689)
      ·
        refine ⟨7502602138029677637758767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10003469517372903517011689 7502602138029677637758767)
        ·
          refine ⟨11253903207044516456638151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502602138029677637758767 11253903207044516456638151)
          ·
            refine ⟨16880854810566774684957227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253903207044516456638151 16880854810566774684957227)
            ·
              refine ⟨25321282215850162027435841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16880854810566774684957227 25321282215850162027435841)
              ·
                refine ⟨18990961661887621520576881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25321282215850162027435841 18990961661887621520576881)
                ·
                  refine ⟨14243221246415716140432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18990961661887621520576881 14243221246415716140432661)
                  ·
                    refine ⟨667650995925736694082781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14243221246415716140432661 667650995925736694082781)
                    ·
                      rfl

theorem cell23_3900737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3900737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900737 prefixEnd_3900737 := by exact prefixLift 3900737
  have htrace : WordTrace (prefixWord ++ tailWord_3900737) baseStart_3900737 baseEnd_3900737 := by
    simpa [prefixWord, tailWord_3900737, baseEnd_3900737] using wordTrace_append hprefix tailTrace_3900737
  have hstable : (prefixWord ++ tailWord_3900737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900737).length < 2 ^ (prefixWord ++ tailWord_3900737).sum := by decide
  have hdescent : baseEnd_3900737 < baseStart_3900737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900757 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3900757 : Nat := 118140960795 + 3900757 * 2 ^ 59
def prefixEnd_3900757 : Nat := 4983230072969 + 3 ^ 40 * 3900757 * 2
def baseEnd_3900757 : Nat := 2002963257390300003998251

theorem tailTrace_3900757 : CollatzResearch.WordTrace tailWord_3900757 prefixEnd_3900757 2002963257390300003998251 := by
  unfold tailWord_3900757
  simp only [CollatzResearch.WordTrace]
  refine ⟨142272295929231060102116525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94848197286154040068077683 142272295929231060102116525)
  ·
    refine ⟨53352110973461647538293697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142272295929231060102116525 53352110973461647538293697)
    ·
      refine ⟨40014083230096235653720273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53352110973461647538293697 40014083230096235653720273)
      ·
        refine ⟨30010562422572176740290205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40014083230096235653720273 30010562422572176740290205)
        ·
          refine ⟨11253960908464566277608827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30010562422572176740290205 11253960908464566277608827)
          ·
            refine ⟨16880941362696849416413241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253960908464566277608827 16880941362696849416413241)
            ·
              refine ⟨12660706022022637062309931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880941362696849416413241 12660706022022637062309931)
              ·
                refine ⟨18991059033033955593464897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660706022022637062309931 18991059033033955593464897)
                ·
                  refine ⟨14243294274775466695098673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18991059033033955593464897 14243294274775466695098673)
                  ·
                    refine ⟨10682470706081600021324005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14243294274775466695098673 10682470706081600021324005)
                    ·
                      refine ⟨2002963257390300003998251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10682470706081600021324005 2002963257390300003998251)
                      ·
                        rfl

theorem cell23_3900757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3900757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900757 prefixEnd_3900757 := by exact prefixLift 3900757
  have htrace : WordTrace (prefixWord ++ tailWord_3900757) baseStart_3900757 baseEnd_3900757 := by
    simpa [prefixWord, tailWord_3900757, baseEnd_3900757] using wordTrace_append hprefix tailTrace_3900757
  have hstable : (prefixWord ++ tailWord_3900757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900757).length < 2 ^ (prefixWord ++ tailWord_3900757).sum := by decide
  have hdescent : baseEnd_3900757 < baseStart_3900757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900797 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3900797 : Nat := 118140960795 + 3900797 * 2 ^ 59
def prefixEnd_3900797 : Nat := 4983230072969 + 3 ^ 40 * 3900797 * 2
def baseEnd_3900797 : Nat := 667661265538826615832689

theorem tailTrace_3900797 : CollatzResearch.WordTrace tailWord_3900797 prefixEnd_3900797 667661265538826615832689 := by
  unfold tailWord_3900797
  simp only [CollatzResearch.WordTrace]
  refine ⟨142273754849086146933572645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94849169899390764622381763 142273754849086146933572645)
  ·
    refine ⟨26676329034203652550044871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142273754849086146933572645 26676329034203652550044871)
    ·
      refine ⟨40014493551305478825067307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26676329034203652550044871 40014493551305478825067307)
      ·
        refine ⟨60021740326958218237600961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40014493551305478825067307 60021740326958218237600961)
        ·
          refine ⟨45016305245218663678200721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60021740326958218237600961 45016305245218663678200721)
          ·
            refine ⟨33762228933913997758650541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45016305245218663678200721 33762228933913997758650541)
            ·
              refine ⟨12660835850217749159493953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33762228933913997758650541 12660835850217749159493953)
              ·
                refine ⟨9495626887663311869620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660835850217749159493953 9495626887663311869620465)
                ·
                  refine ⟨7121720165747483902215349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495626887663311869620465 7121720165747483902215349)
                  ·
                    refine ⟨667661265538826615832689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7121720165747483902215349 667661265538826615832689)
                    ·
                      rfl

theorem cell23_3900797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3900797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900797 prefixEnd_3900797 := by exact prefixLift 3900797
  have htrace : WordTrace (prefixWord ++ tailWord_3900797) baseStart_3900797 baseEnd_3900797 := by
    simpa [prefixWord, tailWord_3900797, baseEnd_3900797] using wordTrace_append hprefix tailTrace_3900797
  have hstable : (prefixWord ++ tailWord_3900797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900797).length < 2 ^ (prefixWord ++ tailWord_3900797).sum := by decide
  have hdescent : baseEnd_3900797 < baseStart_3900797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900801 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 7]
def baseStart_3900801 : Nat := 118140960795 + 3900801 * 2 ^ 59
def prefixEnd_3900801 : Nat := 4983230072969 + 3 ^ 40 * 3900801 * 2
def baseEnd_3900801 : Nat := 222553983393233092427561

theorem tailTrace_3900801 : CollatzResearch.WordTrace tailWord_3900801 prefixEnd_3900801 222553983393233092427561 := by
  unfold tailWord_3900801
  simp only [CollatzResearch.WordTrace]
  refine ⟨142273900741071655616718257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94849267160714437077812171 142273900741071655616718257)
  ·
    refine ⟨106705425555803741712538693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142273900741071655616718257 106705425555803741712538693)
    ·
      refine ⟨20007267291713201571101005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106705425555803741712538693 20007267291713201571101005)
      ·
        refine ⟨7502725234392450589162877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20007267291713201571101005 7502725234392450589162877)
        ·
          refine ⟨2813521962897168970936079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7502725234392450589162877 2813521962897168970936079)
          ·
            refine ⟨4220282944345753456404119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813521962897168970936079 4220282944345753456404119)
            ·
              refine ⟨6330424416518630184606179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220282944345753456404119 6330424416518630184606179)
              ·
                refine ⟨9495636624777945276909269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330424416518630184606179 9495636624777945276909269)
                ·
                  refine ⟨222553983393233092427561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9495636624777945276909269 222553983393233092427561)
                  ·
                    rfl

theorem cell23_3900801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_3900801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900801 prefixEnd_3900801 := by exact prefixLift 3900801
  have htrace : WordTrace (prefixWord ++ tailWord_3900801) baseStart_3900801 baseEnd_3900801 := by
    simpa [prefixWord, tailWord_3900801, baseEnd_3900801] using wordTrace_append hprefix tailTrace_3900801
  have hstable : (prefixWord ++ tailWord_3900801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900801).length < 2 ^ (prefixWord ++ tailWord_3900801).sum := by decide
  have hdescent : baseEnd_3900801 < baseStart_3900801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900807 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3900807 : Nat := 118140960795 + 3900807 * 2 ^ 59
def prefixEnd_3900807 : Nat := 4983230072969 + 3 ^ 40 * 3900807 * 2
def baseEnd_3900807 : Nat := 2002988931423024808373021

theorem tailTrace_3900807 : CollatzResearch.WordTrace tailWord_3900807 prefixEnd_3900807 2002988931423024808373021 := by
  unfold tailWord_3900807
  simp only [CollatzResearch.WordTrace]
  refine ⟨142274119579049918641436675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94849413052699945760957783 142274119579049918641436675)
  ·
    refine ⟨213411179368574877962155013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142274119579049918641436675 213411179368574877962155013)
    ·
      refine ⟨40014596131607789617904065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213411179368574877962155013 40014596131607789617904065)
      ·
        refine ⟨30010947098705842213428049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40014596131607789617904065 30010947098705842213428049)
        ·
          refine ⟨22508210324029381660071037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30010947098705842213428049 22508210324029381660071037)
          ·
            refine ⟨8440578871511018122526639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22508210324029381660071037 8440578871511018122526639)
            ·
              refine ⟨12660868307266527183789959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440578871511018122526639 12660868307266527183789959)
              ·
                refine ⟨18991302460899790775684939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660868307266527183789959 18991302460899790775684939)
                ·
                  refine ⟨28486953691349686163527409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991302460899790775684939 28486953691349686163527409)
                  ·
                    refine ⟨21365215268512264622645557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28486953691349686163527409 21365215268512264622645557)
                    ·
                      refine ⟨2002988931423024808373021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21365215268512264622645557 2002988931423024808373021)
                      ·
                        rfl

theorem cell23_3900807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3900807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900807 prefixEnd_3900807 := by exact prefixLift 3900807
  have htrace : WordTrace (prefixWord ++ tailWord_3900807) baseStart_3900807 baseEnd_3900807 := by
    simpa [prefixWord, tailWord_3900807, baseEnd_3900807] using wordTrace_append hprefix tailTrace_3900807
  have hstable : (prefixWord ++ tailWord_3900807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900807).length < 2 ^ (prefixWord ++ tailWord_3900807).sum := by decide
  have hdescent : baseEnd_3900807 < baseStart_3900807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900834 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3900834 : Nat := 118140960795 + 3900834 * 2 ^ 59
def prefixEnd_3900834 : Nat := 4983230072969 + 3 ^ 40 * 3900834 * 2
def baseEnd_3900834 : Nat := 2003002795400696202735397

theorem tailTrace_3900834 : CollatzResearch.WordTrace tailWord_3900834 prefixEnd_3900834 2003002795400696202735397 := by
  unfold tailWord_3900834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568776087488025563167389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94850069566634734835113037 35568776087488025563167389)
  ·
    refine ⟨13338291032808009586187771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35568776087488025563167389 13338291032808009586187771)
    ·
      refine ⟨20007436549212014379281657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338291032808009586187771 20007436549212014379281657)
      ·
        refine ⟨15005577411909010784461243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20007436549212014379281657 15005577411909010784461243)
        ·
          refine ⟨22508366117863516176691865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15005577411909010784461243 22508366117863516176691865)
          ·
            refine ⟨16881274588397637132518899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22508366117863516176691865 16881274588397637132518899)
            ·
              refine ⟨25321911882596455698778349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881274588397637132518899 25321911882596455698778349)
              ·
                refine ⟨9495716955973670887041881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25321911882596455698778349 9495716955973670887041881)
                ·
                  refine ⟨7121787716980253165281411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495716955973670887041881 7121787716980253165281411)
                  ·
                    refine ⟨10682681575470379747922117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7121787716980253165281411 10682681575470379747922117)
                    ·
                      refine ⟨2003002795400696202735397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10682681575470379747922117 2003002795400696202735397)
                      ·
                        rfl

theorem cell23_3900834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3900834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900834 prefixEnd_3900834 := by exact prefixLift 3900834
  have htrace : WordTrace (prefixWord ++ tailWord_3900834) baseStart_3900834 baseEnd_3900834 := by
    simpa [prefixWord, tailWord_3900834, baseEnd_3900834] using wordTrace_append hprefix tailTrace_3900834
  have hstable : (prefixWord ++ tailWord_3900834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900834).length < 2 ^ (prefixWord ++ tailWord_3900834).sum := by decide
  have hdescent : baseEnd_3900834 < baseStart_3900834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900861 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3900861 : Nat := 118140960795 + 3900861 * 2 ^ 59
def prefixEnd_3900861 : Nat := 4983230072969 + 3 ^ 40 * 3900861 * 2
def baseEnd_3900861 : Nat := 667672219792789199032591

theorem tailTrace_3900861 : CollatzResearch.WordTrace tailWord_3900861 prefixEnd_3900861 667672219792789199032591 := by
  unfold tailWord_3900861
  simp only [CollatzResearch.WordTrace]
  refine ⟨142276089120854285863902437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94850726080569523909268291 142276089120854285863902437)
  ·
    refine ⟨26676766710160178599481707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142276089120854285863902437 26676766710160178599481707)
    ·
      refine ⟨40015150065240267899222561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26676766710160178599481707 40015150065240267899222561)
      ·
        refine ⟨30011362548930200924416921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40015150065240267899222561 30011362548930200924416921)
        ·
          refine ⟨22508521911697650693312691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30011362548930200924416921 22508521911697650693312691)
          ·
            refine ⟨33762782867546476039969037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22508521911697650693312691 33762782867546476039969037)
            ·
              refine ⟨12661043575329928514988389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33762782867546476039969037 12661043575329928514988389)
              ·
                refine ⟨2373945670374361596560323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12661043575329928514988389 2373945670374361596560323)
                ·
                  refine ⟨3560918505561542394840485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2373945670374361596560323 3560918505561542394840485)
                  ·
                    refine ⟨667672219792789199032591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3560918505561542394840485 667672219792789199032591)
                    ·
                      rfl

theorem cell23_3900861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3900861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900861 prefixEnd_3900861 := by exact prefixLift 3900861
  have htrace : WordTrace (prefixWord ++ tailWord_3900861) baseStart_3900861 baseEnd_3900861 := by
    simpa [prefixWord, tailWord_3900861, baseEnd_3900861] using wordTrace_append hprefix tailTrace_3900861
  have hstable : (prefixWord ++ tailWord_3900861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900861).length < 2 ^ (prefixWord ++ tailWord_3900861).sum := by decide
  have hdescent : baseEnd_3900861 < baseStart_3900861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900904 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3900904 : Nat := 118140960795 + 3900904 * 2 ^ 59
def prefixEnd_3900904 : Nat := 4983230072969 + 3 ^ 40 * 3900904 * 2
def baseEnd_3900904 : Nat := 667679579682170309620025

theorem tailTrace_3900904 : CollatzResearch.WordTrace tailWord_3900904 prefixEnd_3900904 667679579682170309620025 := by
  unfold tailWord_3900904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71138828729849252103858883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94851771639799002805145177 71138828729849252103858883)
  ·
    refine ⟨106708243094773878155788325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71138828729849252103858883 106708243094773878155788325)
    ·
      refine ⟨20007795580270102154210311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106708243094773878155788325 20007795580270102154210311)
      ·
        refine ⟨30011693370405153231315467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007795580270102154210311 30011693370405153231315467)
        ·
          refine ⟨45017540055607729846973201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30011693370405153231315467 45017540055607729846973201)
          ·
            refine ⟨33763155041705797385229901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45017540055607729846973201 33763155041705797385229901)
            ·
              refine ⟨12661183140639674019461213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33763155041705797385229901 12661183140639674019461213)
              ·
                refine ⟨4747943677739877757297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12661183140639674019461213 4747943677739877757297955)
                ·
                  refine ⟨7121915516609816635946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747943677739877757297955 7121915516609816635946933)
                  ·
                    refine ⟨667679579682170309620025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7121915516609816635946933 667679579682170309620025)
                    ·
                      rfl

theorem cell23_3900904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3900904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900904 prefixEnd_3900904 := by exact prefixLift 3900904
  have htrace : WordTrace (prefixWord ++ tailWord_3900904) baseStart_3900904 baseEnd_3900904 := by
    simpa [prefixWord, tailWord_3900904, baseEnd_3900904] using wordTrace_append hprefix tailTrace_3900904
  have hstable : (prefixWord ++ tailWord_3900904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900904).length < 2 ^ (prefixWord ++ tailWord_3900904).sum := by decide
  have hdescent : baseEnd_3900904 < baseStart_3900904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900907 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4]
def baseStart_3900907 : Nat := 118140960795 + 3900907 * 2 ^ 59
def prefixEnd_3900907 : Nat := 4983230072969 + 3 ^ 40 * 3900907 * 2
def baseEnd_3900907 : Nat := 2003040279488474417122561

theorem tailTrace_3900907 : CollatzResearch.WordTrace tailWord_3900907 prefixEnd_3900907 2003040279488474417122561 := by
  unfold tailWord_3900907
  simp only [CollatzResearch.WordTrace]
  refine ⟨142277766878687635720076975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94851844585791757146717983 142277766878687635720076975)
  ·
    refine ⟨213416650318031453580115463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142277766878687635720076975 213416650318031453580115463)
    ·
      refine ⟨320124975477047180370173195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213416650318031453580115463 320124975477047180370173195)
      ·
        refine ⟨480187463215570770555259793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320124975477047180370173195 480187463215570770555259793)
        ·
          refine ⟨360140597411678077916444845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480187463215570770555259793 360140597411678077916444845)
          ·
            refine ⟨135052724029379279218666817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360140597411678077916444845 135052724029379279218666817)
            ·
              refine ⟨101289543022034459414000113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135052724029379279218666817 101289543022034459414000113)
              ·
                refine ⟨75967157266525844560500085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101289543022034459414000113 75967157266525844560500085)
                ·
                  refine ⟨7121920993736797927546883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75967157266525844560500085 7121920993736797927546883)
                  ·
                    refine ⟨10682881490605196891320325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7121920993736797927546883 10682881490605196891320325)
                    ·
                      refine ⟨2003040279488474417122561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10682881490605196891320325 2003040279488474417122561)
                      ·
                        rfl

theorem cell23_3900907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_3900907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900907 prefixEnd_3900907 := by exact prefixLift 3900907
  have htrace : WordTrace (prefixWord ++ tailWord_3900907) baseStart_3900907 baseEnd_3900907 := by
    simpa [prefixWord, tailWord_3900907, baseEnd_3900907] using wordTrace_append hprefix tailTrace_3900907
  have hstable : (prefixWord ++ tailWord_3900907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900907).length < 2 ^ (prefixWord ++ tailWord_3900907).sum := by decide
  have hdescent : baseEnd_3900907 < baseStart_3900907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900918 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3900918 : Nat := 118140960795 + 3900918 * 2 ^ 59
def prefixEnd_3900918 : Nat := 4983230072969 + 3 ^ 40 * 3900918 * 2
def baseEnd_3900918 : Nat := 2003045927775673874085011

theorem tailTrace_3900918 : CollatzResearch.WordTrace tailWord_3900918 prefixEnd_3900918 2003045927775673874085011 := by
  unfold tailWord_3900918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892385505102986537420463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94852112054431856399151605 8892385505102986537420463)
  ·
    refine ⟨13338578257654479806130695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8892385505102986537420463 13338578257654479806130695)
    ·
      refine ⟨20007867386481719709196043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338578257654479806130695 20007867386481719709196043)
      ·
        refine ⟨30011801079722579563794065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007867386481719709196043 30011801079722579563794065)
        ·
          refine ⟨22508850809791934672845549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30011801079722579563794065 22508850809791934672845549)
          ·
            refine ⟨8440819053671975502317081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22508850809791934672845549 8440819053671975502317081)
            ·
              refine ⟨6330614290253981626737811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440819053671975502317081 6330614290253981626737811)
              ·
                refine ⟨9495921435380972440106717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330614290253981626737811 9495921435380972440106717)
                ·
                  refine ⟨3560970538267864665040019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9495921435380972440106717 3560970538267864665040019)
                  ·
                    refine ⟨5341455807401796997560029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3560970538267864665040019 5341455807401796997560029)
                    ·
                      refine ⟨2003045927775673874085011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341455807401796997560029 2003045927775673874085011)
                      ·
                        rfl

theorem cell23_3900918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3900918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900918 prefixEnd_3900918 := by exact prefixLift 3900918
  have htrace : WordTrace (prefixWord ++ tailWord_3900918) baseStart_3900918 baseEnd_3900918 := by
    simpa [prefixWord, tailWord_3900918, baseEnd_3900918] using wordTrace_append hprefix tailTrace_3900918
  have hstable : (prefixWord ++ tailWord_3900918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900918).length < 2 ^ (prefixWord ++ tailWord_3900918).sum := by decide
  have hdescent : baseEnd_3900918 < baseStart_3900918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900927 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_3900927 : Nat := 118140960795 + 3900927 * 2 ^ 59
def prefixEnd_3900927 : Nat := 4983230072969 + 3 ^ 40 * 3900927 * 2
def baseEnd_3900927 : Nat := 2003050549101564338872469

theorem tailTrace_3900927 : CollatzResearch.WordTrace tailWord_3900927 prefixEnd_3900927 2003050549101564338872469 := by
  unfold tailWord_3900927
  simp only [CollatzResearch.WordTrace]
  refine ⟨142278496338615179135805035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94852330892410119423870023 142278496338615179135805035)
  ·
    refine ⟨213417744507922768703707553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142278496338615179135805035 213417744507922768703707553)
    ·
      refine ⟨160063308380942076527780665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213417744507922768703707553 160063308380942076527780665)
      ·
        refine ⟨120047481285706557395835499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160063308380942076527780665 120047481285706557395835499)
        ·
          refine ⟨180071221928559836093753249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120047481285706557395835499 180071221928559836093753249)
          ·
            refine ⟨135053416446419877070314937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180071221928559836093753249 135053416446419877070314937)
            ·
              refine ⟨101290062334814907802736203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135053416446419877070314937 101290062334814907802736203)
              ·
                refine ⟨151935093502222361704104305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101290062334814907802736203 151935093502222361704104305)
                ·
                  refine ⟨113951320126666771278078229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151935093502222361704104305 113951320126666771278078229)
                  ·
                    refine ⟨5341468130937504903659917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113951320126666771278078229 5341468130937504903659917)
                    ·
                      refine ⟨2003050549101564338872469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341468130937504903659917 2003050549101564338872469)
                      ·
                        rfl

theorem cell23_3900927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_3900927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900927 prefixEnd_3900927 := by exact prefixLift 3900927
  have htrace : WordTrace (prefixWord ++ tailWord_3900927) baseStart_3900927 baseEnd_3900927 := by
    simpa [prefixWord, tailWord_3900927, baseEnd_3900927] using wordTrace_append hprefix tailTrace_3900927
  have hstable : (prefixWord ++ tailWord_3900927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900927).length < 2 ^ (prefixWord ++ tailWord_3900927).sum := by decide
  have hdescent : baseEnd_3900927 < baseStart_3900927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900937 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_3900937 : Nat := 118140960795 + 3900937 * 2 ^ 59
def prefixEnd_3900937 : Nat := 4983230072969 + 3 ^ 40 * 3900937 * 2
def baseEnd_3900937 : Nat := 2003055683908109299747423

theorem tailTrace_3900937 : CollatzResearch.WordTrace tailWord_3900937 prefixEnd_3900937 2003055683908109299747423 := by
  unfold tailWord_3900937
  simp only [CollatzResearch.WordTrace]
  refine ⟨142278861068578950843669065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94852574045719300562446043 142278861068578950843669065)
  ·
    refine ⟨106709145801434213132751799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142278861068578950843669065 106709145801434213132751799)
    ·
      refine ⟨160063718702151319699127699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106709145801434213132751799 160063718702151319699127699)
      ·
        refine ⟨240095578053226979548691549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160063718702151319699127699 240095578053226979548691549)
        ·
          refine ⟨90035841769960117330759331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240095578053226979548691549 90035841769960117330759331)
          ·
            refine ⟨135053762654940175996138997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90035841769960117330759331 135053762654940175996138997)
            ·
              refine ⟨12661290248900641499638031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135053762654940175996138997 12661290248900641499638031)
              ·
                refine ⟨18991935373350962249457047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12661290248900641499638031 18991935373350962249457047)
                ·
                  refine ⟨28487903060026443374185571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991935373350962249457047 28487903060026443374185571)
                  ·
                    refine ⟨42731854590039665061278357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28487903060026443374185571 42731854590039665061278357)
                    ·
                      refine ⟨2003055683908109299747423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42731854590039665061278357 2003055683908109299747423)
                      ·
                        rfl

theorem cell23_3900937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_3900937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900937 prefixEnd_3900937 := by exact prefixLift 3900937
  have htrace : WordTrace (prefixWord ++ tailWord_3900937) baseStart_3900937 baseEnd_3900937 := by
    simpa [prefixWord, tailWord_3900937, baseEnd_3900937] using wordTrace_append hprefix tailTrace_3900937
  have hstable : (prefixWord ++ tailWord_3900937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900937).length < 2 ^ (prefixWord ++ tailWord_3900937).sum := by decide
  have hdescent : baseEnd_3900937 < baseStart_3900937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900947 : List Nat := [1, 1, 1, 2, 1, 7, 1, 9]
def baseStart_3900947 : Nat := 118140960795 + 3900947 * 2 ^ 59
def prefixEnd_3900947 : Nat := 4983230072969 + 3 ^ 40 * 3900947 * 2
def baseEnd_3900947 : Nat := 74187437730172380023051

theorem tailTrace_3900947 : CollatzResearch.WordTrace tailWord_3900947 prefixEnd_3900947 74187437730172380023051 := by
  unfold tailWord_3900947
  simp only [CollatzResearch.WordTrace]
  refine ⟨142279225798542722551533095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94852817199028481701022063 142279225798542722551533095)
  ·
    refine ⟨213418838697814083827299643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142279225798542722551533095 213418838697814083827299643)
    ·
      refine ⟨320128258046721125740949465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213418838697814083827299643 320128258046721125740949465)
      ·
        refine ⟨240096193535040844305712099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320128258046721125740949465 240096193535040844305712099)
        ·
          refine ⟨360144290302561266458568149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240096193535040844305712099 360144290302561266458568149)
          ·
            refine ⟨8440881803966279682622691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 360144290302561266458568149 8440881803966279682622691)
            ·
              refine ⟨12661322705949419523934037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8440881803966279682622691 12661322705949419523934037)
              ·
                refine ⟨74187437730172380023051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12661322705949419523934037 74187437730172380023051)
                ·
                  rfl

theorem cell23_3900947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 9].length) (baseStart_3900947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900947 prefixEnd_3900947 := by exact prefixLift 3900947
  have htrace : WordTrace (prefixWord ++ tailWord_3900947) baseStart_3900947 baseEnd_3900947 := by
    simpa [prefixWord, tailWord_3900947, baseEnd_3900947] using wordTrace_append hprefix tailTrace_3900947
  have hstable : (prefixWord ++ tailWord_3900947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900947).length < 2 ^ (prefixWord ++ tailWord_3900947).sum := by decide
  have hdescent : baseEnd_3900947 < baseStart_3900947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900952 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_3900952 : Nat := 118140960795 + 3900952 * 2 ^ 59
def prefixEnd_3900952 : Nat := 4983230072969 + 3 ^ 40 * 3900952 * 2
def baseEnd_3900952 : Nat := 2003063386117926741059855

theorem tailTrace_3900952 : CollatzResearch.WordTrace tailWord_3900952 prefixEnd_3900952 2003063386117926741059855 := by
  unfold tailWord_3900952
  simp only [CollatzResearch.WordTrace]
  refine ⟨71139704081762304202732555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94852938775683072270310073 71139704081762304202732555)
  ·
    refine ⟨106709556122643456304098833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71139704081762304202732555 106709556122643456304098833)
    ·
      refine ⟨80032167091982592228074125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106709556122643456304098833 80032167091982592228074125)
      ·
        refine ⟨30012062659493472085527797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80032167091982592228074125 30012062659493472085527797)
        ·
          refine ⟨2813630874327513008018231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30012062659493472085527797 2813630874327513008018231)
          ·
            refine ⟨4220446311491269512027347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813630874327513008018231 4220446311491269512027347)
            ·
              refine ⟨6330669467236904268041021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4220446311491269512027347 6330669467236904268041021)
              ·
                refine ⟨2374001050213839100515383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6330669467236904268041021 2374001050213839100515383)
                ·
                  refine ⟨3561001575320758650773075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374001050213839100515383 3561001575320758650773075)
                  ·
                    refine ⟨5341502362981137976159613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3561001575320758650773075 5341502362981137976159613)
                    ·
                      refine ⟨2003063386117926741059855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341502362981137976159613 2003063386117926741059855)
                      ·
                        rfl

theorem cell23_3900952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_3900952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900952 prefixEnd_3900952 := by exact prefixLift 3900952
  have htrace : WordTrace (prefixWord ++ tailWord_3900952) baseStart_3900952 baseEnd_3900952 := by
    simpa [prefixWord, tailWord_3900952, baseEnd_3900952] using wordTrace_append hprefix tailTrace_3900952
  have hstable : (prefixWord ++ tailWord_3900952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900952).length < 2 ^ (prefixWord ++ tailWord_3900952).sum := by decide
  have hdescent : baseEnd_3900952 < baseStart_3900952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900961 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3900961 : Nat := 118140960795 + 3900961 * 2 ^ 59
def prefixEnd_3900961 : Nat := 4983230072969 + 3 ^ 40 * 3900961 * 2
def baseEnd_3900961 : Nat := 2003068007443817205847313

theorem tailTrace_3900961 : CollatzResearch.WordTrace tailWord_3900961 prefixEnd_3900961 2003068007443817205847313 := by
  unfold tailWord_3900961
  simp only [CollatzResearch.WordTrace]
  refine ⟨142279736420492002942542737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94853157613661335295028491 142279736420492002942542737)
  ·
    refine ⟨106709802315369002206907053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142279736420492002942542737 106709802315369002206907053)
    ·
      refine ⟨40016175868263375827590145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106709802315369002206907053 40016175868263375827590145)
      ·
        refine ⟨30012131901197531870692609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40016175868263375827590145 30012131901197531870692609)
        ·
          refine ⟨22509098925898148903019457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30012131901197531870692609 22509098925898148903019457)
          ·
            refine ⟨16881824194423611677264593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22509098925898148903019457 16881824194423611677264593)
            ·
              refine ⟨12661368145817708757948445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16881824194423611677264593 12661368145817708757948445)
              ·
                refine ⟨4748013054681640784230667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12661368145817708757948445 4748013054681640784230667)
                ·
                  refine ⟨7122019582022461176346001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748013054681640784230667 7122019582022461176346001)
                  ·
                    refine ⟨5341514686516845882259501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7122019582022461176346001 5341514686516845882259501)
                    ·
                      refine ⟨2003068007443817205847313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341514686516845882259501 2003068007443817205847313)
                      ·
                        rfl

theorem cell23_3900961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3900961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900961 prefixEnd_3900961 := by exact prefixLift 3900961
  have htrace : WordTrace (prefixWord ++ tailWord_3900961) baseStart_3900961 baseEnd_3900961 := by
    simpa [prefixWord, tailWord_3900961, baseEnd_3900961] using wordTrace_append hprefix tailTrace_3900961
  have hstable : (prefixWord ++ tailWord_3900961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900961).length < 2 ^ (prefixWord ++ tailWord_3900961).sum := by decide
  have hdescent : baseEnd_3900961 < baseStart_3900961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3900977 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_3900977 : Nat := 118140960795 + 3900977 * 2 ^ 59
def prefixEnd_3900977 : Nat := 4983230072969 + 3 ^ 40 * 3900977 * 2
def baseEnd_3900977 : Nat := 667692074378096381082413

theorem tailTrace_3900977 : CollatzResearch.WordTrace tailWord_3900977 prefixEnd_3900977 667692074378096381082413 := by
  unfold tailWord_3900977
  simp only [CollatzResearch.WordTrace]
  refine ⟨142280319988434037675125185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94853546658956025116750123 142280319988434037675125185)
  ·
    refine ⟨106710239991325528256343889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142280319988434037675125185 106710239991325528256343889)
    ·
      refine ⟨80032679993494146192257917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106710239991325528256343889 80032679993494146192257917)
      ·
        refine ⟨30012254997560304822096719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80032679993494146192257917 30012254997560304822096719)
        ·
          refine ⟨45018382496340457233145079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30012254997560304822096719 45018382496340457233145079)
          ·
            refine ⟨67527573744510685849717619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45018382496340457233145079 67527573744510685849717619)
            ·
              refine ⟨101291360616766028774576429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67527573744510685849717619 101291360616766028774576429)
              ·
                refine ⟨37984260231287260790466161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101291360616766028774576429 37984260231287260790466161)
                ·
                  refine ⟨28488195173465445592849621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37984260231287260790466161 28488195173465445592849621)
                  ·
                    refine ⟨667692074378096381082413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28488195173465445592849621 667692074378096381082413)
                    ·
                      rfl

theorem cell23_3900977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_3900977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3900977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3900977 prefixEnd_3900977 := by exact prefixLift 3900977
  have htrace : WordTrace (prefixWord ++ tailWord_3900977) baseStart_3900977 baseEnd_3900977 := by
    simpa [prefixWord, tailWord_3900977, baseEnd_3900977] using wordTrace_append hprefix tailTrace_3900977
  have hstable : (prefixWord ++ tailWord_3900977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3900977).length < 2 ^ (prefixWord ++ tailWord_3900977).sum := by decide
  have hdescent : baseEnd_3900977 < baseStart_3900977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3900977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901007 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 6]
def baseStart_3901007 : Nat := 118140960795 + 3901007 * 2 ^ 59
def prefixEnd_3901007 : Nat := 4983230072969 + 3 ^ 40 * 3901007 * 2
def baseEnd_3901007 : Nat := 667697209184641341957367

theorem tailTrace_3901007 : CollatzResearch.WordTrace tailWord_3901007 prefixEnd_3901007 667697209184641341957367 := by
  unfold tailWord_3901007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142281414178325352798717275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94854276118883568532478183 142281414178325352798717275)
  ·
    refine ⟨213422121267488029198075913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142281414178325352798717275 213422121267488029198075913)
    ·
      refine ⟨160066590950616021898556935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213422121267488029198075913 160066590950616021898556935)
      ·
        refine ⟨240099886425924032847835403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160066590950616021898556935 240099886425924032847835403)
        ·
          refine ⟨360149829638886049271753105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240099886425924032847835403 360149829638886049271753105)
          ·
            refine ⟨270112372229164536953814829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360149829638886049271753105 270112372229164536953814829)
            ·
              refine ⟨101292139585936701357680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270112372229164536953814829 101292139585936701357680561)
              ·
                refine ⟨75969104689452526018260421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101292139585936701357680561 75969104689452526018260421)
                ·
                  refine ⟨14244207129272348628423829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75969104689452526018260421 14244207129272348628423829)
                  ·
                    refine ⟨667697209184641341957367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14244207129272348628423829 667697209184641341957367)
                    ·
                      rfl

theorem cell23_3901007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_3901007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901007 prefixEnd_3901007 := by exact prefixLift 3901007
  have htrace : WordTrace (prefixWord ++ tailWord_3901007) baseStart_3901007 baseEnd_3901007 := by
    simpa [prefixWord, tailWord_3901007, baseEnd_3901007] using wordTrace_append hprefix tailTrace_3901007
  have hstable : (prefixWord ++ tailWord_3901007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901007).length < 2 ^ (prefixWord ++ tailWord_3901007).sum := by decide
  have hdescent : baseEnd_3901007 < baseStart_3901007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901104 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_3901104 : Nat := 118140960795 + 3901104 * 2 ^ 59
def prefixEnd_3901104 : Nat := 4983230072969 + 3 ^ 40 * 3901104 * 2
def baseEnd_3901104 : Nat := 2003141435177410146359155

theorem tailTrace_3901104 : CollatzResearch.WordTrace tailWord_3901104 prefixEnd_3901104 2003141435177410146359155 := by
  unfold tailWord_3901104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71142476029486969182499183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94856634705982625576665577 71142476029486969182499183)
  ·
    refine ⟨106713714044230453773748775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71142476029486969182499183 106713714044230453773748775)
    ·
      refine ⟨160070571066345680660623163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106713714044230453773748775 160070571066345680660623163)
      ·
        refine ⟨240105856599518520990934745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160070571066345680660623163 240105856599518520990934745)
        ·
          refine ⟨180079392449638890743201059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240105856599518520990934745 180079392449638890743201059)
          ·
            refine ⟨270119088674458336114801589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180079392449638890743201059 270119088674458336114801589)
            ·
              refine ⟨25323664563230469010762649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270119088674458336114801589 25323664563230469010762649)
              ·
                refine ⟨18992748422422851758071987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25323664563230469010762649 18992748422422851758071987)
                ·
                  refine ⟨28489122633634277637107981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18992748422422851758071987 28489122633634277637107981)
                  ·
                    refine ⟨10683420987612854113915493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28489122633634277637107981 10683420987612854113915493)
                    ·
                      refine ⟨2003141435177410146359155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10683420987612854113915493 2003141435177410146359155)
                      ·
                        rfl

theorem cell23_3901104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_3901104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901104 prefixEnd_3901104 := by exact prefixLift 3901104
  have htrace : WordTrace (prefixWord ++ tailWord_3901104) baseStart_3901104 baseEnd_3901104 := by
    simpa [prefixWord, tailWord_3901104, baseEnd_3901104] using wordTrace_append hprefix tailTrace_3901104
  have hstable : (prefixWord ++ tailWord_3901104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901104).length < 2 ^ (prefixWord ++ tailWord_3901104).sum := by decide
  have hdescent : baseEnd_3901104 < baseStart_3901104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901138 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3901138 : Nat := 118140960795 + 3901138 * 2 ^ 59
def prefixEnd_3901138 : Nat := 4983230072969 + 3 ^ 40 * 3901138 * 2
def baseEnd_3901138 : Nat := 2003158893519663013333999

theorem tailTrace_3901138 : CollatzResearch.WordTrace tailWord_3901138 prefixEnd_3901138 2003158893519663013333999 := by
  unfold tailWord_3901138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571548035212690542934017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94857461427233841447824045 35571548035212690542934017)
  ·
    refine ⟨26678661026409517907200513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35571548035212690542934017 26678661026409517907200513)
    ·
      refine ⟨20008995769807138430400385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26678661026409517907200513 20008995769807138430400385)
      ·
        refine ⟨15006746827355353822800289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20008995769807138430400385 15006746827355353822800289)
        ·
          refine ⟨11255060120516515367100217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15006746827355353822800289 11255060120516515367100217)
          ·
            refine ⟨8441295090387386525325163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255060120516515367100217 8441295090387386525325163)
            ·
              refine ⟨12661942635581079787987745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441295090387386525325163 12661942635581079787987745)
              ·
                refine ⟨9496456976685809840990809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12661942635581079787987745 9496456976685809840990809)
                ·
                  refine ⟨7122342732514357380743107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496456976685809840990809 7122342732514357380743107)
                  ·
                    refine ⟨10683514098771536071114661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7122342732514357380743107 10683514098771536071114661)
                    ·
                      refine ⟨2003158893519663013333999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10683514098771536071114661 2003158893519663013333999)
                      ·
                        rfl

theorem cell23_3901138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3901138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901138 prefixEnd_3901138 := by exact prefixLift 3901138
  have htrace : WordTrace (prefixWord ++ tailWord_3901138) baseStart_3901138 baseEnd_3901138 := by
    simpa [prefixWord, tailWord_3901138, baseEnd_3901138] using wordTrace_append hprefix tailTrace_3901138
  have hstable : (prefixWord ++ tailWord_3901138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901138).length < 2 ^ (prefixWord ++ tailWord_3901138).sum := by decide
  have hdescent : baseEnd_3901138 < baseStart_3901138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901144 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 8]
def baseStart_3901144 : Nat := 118140960795 + 3901144 * 2 ^ 59
def prefixEnd_3901144 : Nat := 4983230072969 + 3 ^ 40 * 3901144 * 2
def baseEnd_3901144 : Nat := 222573552711509998873219

theorem tailTrace_3901144 : CollatzResearch.WordTrace tailWord_3901144 prefixEnd_3901144 222573552711509998873219 := by
  unfold tailWord_3901144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71143205489414512598227243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94857607319219350130969657 71143205489414512598227243)
  ·
    refine ⟨106714808234121768897340865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71143205489414512598227243 106714808234121768897340865)
    ·
      refine ⟨80036106175591326673005649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106714808234121768897340865 80036106175591326673005649)
      ·
        refine ⟨60027079631693495004754237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80036106175591326673005649 60027079631693495004754237)
        ·
          refine ⟨22510154861885060626782839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60027079631693495004754237 22510154861885060626782839)
          ·
            refine ⟨33765232292827590940174259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22510154861885060626782839 33765232292827590940174259)
            ·
              refine ⟨50647848439241386410261389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33765232292827590940174259 50647848439241386410261389)
              ·
                refine ⟨18992943164715519903848021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50647848439241386410261389 18992943164715519903848021)
                ·
                  refine ⟨222573552711509998873219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18992943164715519903848021 222573552711509998873219)
                  ·
                    rfl

theorem cell23_3901144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_3901144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901144 prefixEnd_3901144 := by exact prefixLift 3901144
  have htrace : WordTrace (prefixWord ++ tailWord_3901144) baseStart_3901144 baseEnd_3901144 := by
    simpa [prefixWord, tailWord_3901144, baseEnd_3901144] using wordTrace_append hprefix tailTrace_3901144
  have hstable : (prefixWord ++ tailWord_3901144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901144).length < 2 ^ (prefixWord ++ tailWord_3901144).sum := by decide
  have hdescent : baseEnd_3901144 < baseStart_3901144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901164 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_3901164 : Nat := 118140960795 + 3901164 * 2 ^ 59
def prefixEnd_3901164 : Nat := 4983230072969 + 3 ^ 40 * 3901164 * 2
def baseEnd_3901164 : Nat := 2003172244016679911608879

theorem tailTrace_3901164 : CollatzResearch.WordTrace tailWord_3901164 prefixEnd_3901164 2003172244016679911608879 := by
  unfold tailWord_3901164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71143570219378284306091273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94858093625837712408121697 71143570219378284306091273)
  ·
    refine ⟨53357677664533713229568455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71143570219378284306091273 53357677664533713229568455)
    ·
      refine ⟨80036516496800569844352683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53357677664533713229568455 80036516496800569844352683)
      ·
        refine ⟨120054774745200854766529025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80036516496800569844352683 120054774745200854766529025)
        ·
          refine ⟨90041081058900641074896769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120054774745200854766529025 90041081058900641074896769)
          ·
            refine ⟨67530810794175480806172577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90041081058900641074896769 67530810794175480806172577)
            ·
              refine ⟨50648108095631610604629433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67530810794175480806172577 50648108095631610604629433)
              ·
                refine ⟨37986081071723707953472075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50648108095631610604629433 37986081071723707953472075)
                ·
                  refine ⟨56979121607585561930208113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37986081071723707953472075 56979121607585561930208113)
                  ·
                    refine ⟨42734341205689171447656085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56979121607585561930208113 42734341205689171447656085)
                    ·
                      refine ⟨2003172244016679911608879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42734341205689171447656085 2003172244016679911608879)
                      ·
                        rfl

theorem cell23_3901164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_3901164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901164 prefixEnd_3901164 := by exact prefixLift 3901164
  have htrace : WordTrace (prefixWord ++ tailWord_3901164) baseStart_3901164 baseEnd_3901164 := by
    simpa [prefixWord, tailWord_3901164, baseEnd_3901164] using wordTrace_append hprefix tailTrace_3901164
  have hstable : (prefixWord ++ tailWord_3901164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901164).length < 2 ^ (prefixWord ++ tailWord_3901164).sum := by decide
  have hdescent : baseEnd_3901164 < baseStart_3901164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901172 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3901172 : Nat := 118140960795 + 3901172 * 2 ^ 59
def prefixEnd_3901172 : Nat := 4983230072969 + 3 ^ 40 * 3901172 * 2
def baseEnd_3901172 : Nat := 2003176351861915880308843

theorem tailTrace_3901172 : CollatzResearch.WordTrace tailWord_3901172 prefixEnd_3901172 2003176351861915880308843 := by
  unfold tailWord_3901172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71143716111363792989236885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94858288148485057318982513 71143716111363792989236885)
  ·
    refine ⟨3334861692720177796370479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71143716111363792989236885 3334861692720177796370479)
    ·
      refine ⟨5002292539080266694555719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3334861692720177796370479 5002292539080266694555719)
      ·
        refine ⟨7503438808620400041833579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002292539080266694555719 7503438808620400041833579)
        ·
          refine ⟨11255158212930600062750369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503438808620400041833579 11255158212930600062750369)
          ·
            refine ⟨8441368659697950047062777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255158212930600062750369 8441368659697950047062777)
            ·
              refine ⟨6331026494773462535297083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441368659697950047062777 6331026494773462535297083)
              ·
                refine ⟨9496539742160193802945625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331026494773462535297083 9496539742160193802945625)
                ·
                  refine ⟨7122404806620145352209219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496539742160193802945625 7122404806620145352209219)
                  ·
                    refine ⟨10683607209930218028313829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7122404806620145352209219 10683607209930218028313829)
                    ·
                      refine ⟨2003176351861915880308843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10683607209930218028313829 2003176351861915880308843)
                      ·
                        rfl

theorem cell23_3901172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3901172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901172 prefixEnd_3901172 := by exact prefixLift 3901172
  have htrace : WordTrace (prefixWord ++ tailWord_3901172) baseStart_3901172 baseEnd_3901172 := by
    simpa [prefixWord, tailWord_3901172, baseEnd_3901172] using wordTrace_append hprefix tailTrace_3901172
  have hstable : (prefixWord ++ tailWord_3901172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901172).length < 2 ^ (prefixWord ++ tailWord_3901172).sum := by decide
  have hdescent : baseEnd_3901172 < baseStart_3901172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901190 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3901190 : Nat := 118140960795 + 3901190 * 2 ^ 59
def prefixEnd_3901190 : Nat := 4983230072969 + 3 ^ 40 * 3901190 * 2
def baseEnd_3901190 : Nat := 222576177168188534431529

theorem tailTrace_3901190 : CollatzResearch.WordTrace tailWord_3901190 prefixEnd_3901190 222576177168188534431529 := by
  unfold tailWord_3901190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446502773020699220394657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94858725824441583368419349 4446502773020699220394657)
  ·
    refine ⟨3334877079765524415295993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4446502773020699220394657 3334877079765524415295993)
    ·
      refine ⟨2501157809824143311471995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334877079765524415295993 2501157809824143311471995)
      ·
        refine ⟨3751736714736214967207993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501157809824143311471995 3751736714736214967207993)
        ·
          refine ⟨2813802536052161225405995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751736714736214967207993 2813802536052161225405995)
          ·
            refine ⟨4220703804078241838108993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2813802536052161225405995 4220703804078241838108993)
            ·
              refine ⟨3165527853058681378581745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220703804078241838108993 3165527853058681378581745)
              ·
                refine ⟨2374145889794011033936309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165527853058681378581745 2374145889794011033936309)
                ·
                  refine ⟨222576177168188534431529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2374145889794011033936309 222576177168188534431529)
                  ·
                    rfl

theorem cell23_3901190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3901190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901190 prefixEnd_3901190 := by exact prefixLift 3901190
  have htrace : WordTrace (prefixWord ++ tailWord_3901190) baseStart_3901190 baseEnd_3901190 := by
    simpa [prefixWord, tailWord_3901190, baseEnd_3901190] using wordTrace_append hprefix tailTrace_3901190
  have hstable : (prefixWord ++ tailWord_3901190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901190).length < 2 ^ (prefixWord ++ tailWord_3901190).sum := by decide
  have hdescent : baseEnd_3901190 < baseStart_3901190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901221 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3901221 : Nat := 118140960795 + 3901221 * 2 ^ 59
def prefixEnd_3901221 : Nat := 4983230072969 + 3 ^ 40 * 3901221 * 2
def baseEnd_3901221 : Nat := 667733837471328729532039

theorem tailTrace_3901221 : CollatzResearch.WordTrace tailWord_3901221 prefixEnd_3901221 667733837471328729532039 := by
  unfold tailWord_3901221
  simp only [CollatzResearch.WordTrace]
  refine ⟨142289219399550067347007517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94859479599700044898005011 142289219399550067347007517)
  ·
    refine ⟨53358457274831275255127819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142289219399550067347007517 53358457274831275255127819)
    ·
      refine ⟨80037685912246912882691729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53358457274831275255127819 80037685912246912882691729)
      ·
        refine ⟨60028264434185184662018797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80037685912246912882691729 60028264434185184662018797)
        ·
          refine ⟨22510599162819444248257049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60028264434185184662018797 22510599162819444248257049)
          ·
            refine ⟨16882949372114583186192787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22510599162819444248257049 16882949372114583186192787)
            ·
              refine ⟨25324424058171874779289181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16882949372114583186192787 25324424058171874779289181)
              ·
                refine ⟨9496659021814453042233443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25324424058171874779289181 9496659021814453042233443)
                ·
                  refine ⟨14244988532721679563350165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496659021814453042233443 14244988532721679563350165)
                  ·
                    refine ⟨667733837471328729532039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14244988532721679563350165 667733837471328729532039)
                    ·
                      rfl

theorem cell23_3901221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3901221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901221 prefixEnd_3901221 := by exact prefixLift 3901221
  have htrace : WordTrace (prefixWord ++ tailWord_3901221) baseStart_3901221 baseEnd_3901221 := by
    simpa [prefixWord, tailWord_3901221, baseEnd_3901221] using wordTrace_append hprefix tailTrace_3901221
  have hstable : (prefixWord ++ tailWord_3901221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901221).length < 2 ^ (prefixWord ++ tailWord_3901221).sum := by decide
  have hdescent : baseEnd_3901221 < baseStart_3901221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901245 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3901245 : Nat := 118140960795 + 3901245 * 2 ^ 59
def prefixEnd_3901245 : Nat := 4983230072969 + 3 ^ 40 * 3901245 * 2
def baseEnd_3901245 : Nat := 2003213835949694094696007

theorem tailTrace_3901245 : CollatzResearch.WordTrace tailWord_3901245 prefixEnd_3901245 2003213835949694094696007 := by
  unfold tailWord_3901245
  simp only [CollatzResearch.WordTrace]
  refine ⟨142290094751463119445881189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94860063167642079630587459 142290094751463119445881189)
  ·
    refine ⟨26679392765899334896102723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142290094751463119445881189 26679392765899334896102723)
    ·
      refine ⟨40019089148849002344154085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26679392765899334896102723 40019089148849002344154085)
      ·
        refine ⟨7503579215409187939528891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40019089148849002344154085 7503579215409187939528891)
        ·
          refine ⟨11255368823113781909293337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503579215409187939528891 11255368823113781909293337)
          ·
            refine ⟨8441526617335336431970003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255368823113781909293337 8441526617335336431970003)
            ·
              refine ⟨12662289926003004647955005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441526617335336431970003 12662289926003004647955005)
              ·
                refine ⟨4748358722251126742983127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12662289926003004647955005 4748358722251126742983127)
                ·
                  refine ⟨7122538083376690114474691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748358722251126742983127 7122538083376690114474691)
                  ·
                    refine ⟨10683807125065035171712037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7122538083376690114474691 10683807125065035171712037)
                    ·
                      refine ⟨2003213835949694094696007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10683807125065035171712037 2003213835949694094696007)
                      ·
                        rfl

theorem cell23_3901245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3901245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901245 prefixEnd_3901245 := by exact prefixLift 3901245
  have htrace : WordTrace (prefixWord ++ tailWord_3901245) baseStart_3901245 baseEnd_3901245 := by
    simpa [prefixWord, tailWord_3901245, baseEnd_3901245] using wordTrace_append hprefix tailTrace_3901245
  have hstable : (prefixWord ++ tailWord_3901245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901245).length < 2 ^ (prefixWord ++ tailWord_3901245).sum := by decide
  have hdescent : baseEnd_3901245 < baseStart_3901245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901282 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3901282 : Nat := 118140960795 + 3901282 * 2 ^ 59
def prefixEnd_3901282 : Nat := 4983230072969 + 3 ^ 40 * 3901282 * 2
def baseEnd_3901282 : Nat := 2003232834733910449933337

theorem tailTrace_3901282 : CollatzResearch.WordTrace tailWord_3901282 prefixEnd_3901282 2003232834733910449933337 := by
  unfold tailWord_3901282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35572861063082268691244525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94860962834886049843318733 35572861063082268691244525)
  ·
    refine ⟨13339822898655850759216697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35572861063082268691244525 13339822898655850759216697)
    ·
      refine ⟨10004867173991888069412523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13339822898655850759216697 10004867173991888069412523)
      ·
        refine ⟨15007300760987832104118785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10004867173991888069412523 15007300760987832104118785)
        ·
          refine ⟨11255475570740874078089089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15007300760987832104118785 11255475570740874078089089)
          ·
            refine ⟨8441606678055655558566817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255475570740874078089089 8441606678055655558566817)
            ·
              refine ⟨6331205008541741668925113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441606678055655558566817 6331205008541741668925113)
              ·
                refine ⟨4748403756406306251693835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6331205008541741668925113 4748403756406306251693835)
                ·
                  refine ⟨7122605634609459377540753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748403756406306251693835 7122605634609459377540753)
                  ·
                    refine ⟨5341954225957094533155565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7122605634609459377540753 5341954225957094533155565)
                    ·
                      refine ⟨2003232834733910449933337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5341954225957094533155565 2003232834733910449933337)
                      ·
                        rfl

theorem cell23_3901282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3901282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901282 prefixEnd_3901282 := by exact prefixLift 3901282
  have htrace : WordTrace (prefixWord ++ tailWord_3901282) baseStart_3901282 baseEnd_3901282 := by
    simpa [prefixWord, tailWord_3901282, baseEnd_3901282] using wordTrace_append hprefix tailTrace_3901282
  have hstable : (prefixWord ++ tailWord_3901282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901282).length < 2 ^ (prefixWord ++ tailWord_3901282).sum := by decide
  have hdescent : baseEnd_3901282 < baseStart_3901282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901305 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 1, 3, 2]
def baseStart_3901305 : Nat := 118140960795 + 3901305 * 2 ^ 59
def prefixEnd_3901305 : Nat := 4983230072969 + 3 ^ 40 * 3901305 * 2
def baseEnd_3901305 : Nat := 2003244644788963859945731

theorem tailTrace_3901305 : CollatzResearch.WordTrace tailWord_3901305 prefixEnd_3901305 2003244644788963859945731 := by
  unfold tailWord_3901305
  simp only [CollatzResearch.WordTrace]
  refine ⟨142292283131245749693065369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94861522087497166462043579 142292283131245749693065369)
  ·
    refine ⟨106719212348434312269799027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142292283131245749693065369 106719212348434312269799027)
    ·
      refine ⟨160078818522651468404698541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106719212348434312269799027 160078818522651468404698541)
      ·
        refine ⟨60029556945994300651761953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160078818522651468404698541 60029556945994300651761953)
        ·
          refine ⟨45022167709495725488821465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60029556945994300651761953 45022167709495725488821465)
          ·
            refine ⟨33766625782121794116616099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45022167709495725488821465 33766625782121794116616099)
            ·
              refine ⟨50649938673182691174924149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33766625782121794116616099 50649938673182691174924149)
              ·
                refine ⟨4748431750610877297649139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50649938673182691174924149 4748431750610877297649139)
                ·
                  refine ⟨7122647625916315946473709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748431750610877297649139 7122647625916315946473709)
                  ·
                    refine ⟨2670992859718618479927641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7122647625916315946473709 2670992859718618479927641)
                    ·
                      refine ⟨2003244644788963859945731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670992859718618479927641 2003244644788963859945731)
                      ·
                        rfl

theorem cell23_3901305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_3901305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901305 prefixEnd_3901305 := by exact prefixLift 3901305
  have htrace : WordTrace (prefixWord ++ tailWord_3901305) baseStart_3901305 baseEnd_3901305 := by
    simpa [prefixWord, tailWord_3901305, baseEnd_3901305] using wordTrace_append hprefix tailTrace_3901305
  have hstable : (prefixWord ++ tailWord_3901305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901305).length < 2 ^ (prefixWord ++ tailWord_3901305).sum := by decide
  have hdescent : baseEnd_3901305 < baseStart_3901305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901313 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3901313 : Nat := 118140960795 + 3901313 * 2 ^ 59
def prefixEnd_3901313 : Nat := 4983230072969 + 3 ^ 40 * 3901313 * 2
def baseEnd_3901313 : Nat := 2003248752634199828645695

theorem tailTrace_3901313 : CollatzResearch.WordTrace tailWord_3901313 prefixEnd_3901313 2003248752634199828645695 := by
  unfold tailWord_3901313
  simp only [CollatzResearch.WordTrace]
  refine ⟨142292574915216767059356593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94861716610144511372904395 142292574915216767059356593)
  ·
    refine ⟨106719431186412575294517445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142292574915216767059356593 106719431186412575294517445)
    ·
      refine ⟨20009893347452357867722021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106719431186412575294517445 20009893347452357867722021)
      ·
        refine ⟨3751855002647317100197879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20009893347452357867722021 3751855002647317100197879)
        ·
          refine ⟨5627782503970975650296819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751855002647317100197879 5627782503970975650296819)
          ·
            refine ⟨8441673755956463475445229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627782503970975650296819 8441673755956463475445229)
            ·
              refine ⟨3165627658483673803291961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8441673755956463475445229 3165627658483673803291961)
              ·
                refine ⟨2374220743862755352468971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165627658483673803291961 2374220743862755352468971)
                ·
                  refine ⟨3561331115794133028703457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374220743862755352468971 3561331115794133028703457)
                  ·
                    refine ⟨2670998336845599771527593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3561331115794133028703457 2670998336845599771527593)
                    ·
                      refine ⟨2003248752634199828645695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2670998336845599771527593 2003248752634199828645695)
                      ·
                        rfl

theorem cell23_3901313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3901313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901313 prefixEnd_3901313 := by exact prefixLift 3901313
  have htrace : WordTrace (prefixWord ++ tailWord_3901313) baseStart_3901313 baseEnd_3901313 := by
    simpa [prefixWord, tailWord_3901313, baseEnd_3901313] using wordTrace_append hprefix tailTrace_3901313
  have hstable : (prefixWord ++ tailWord_3901313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901313).length < 2 ^ (prefixWord ++ tailWord_3901313).sum := by decide
  have hdescent : baseEnd_3901313 < baseStart_3901313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901321 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_3901321 : Nat := 118140960795 + 3901321 * 2 ^ 59
def prefixEnd_3901321 : Nat := 4983230072969 + 3 ^ 40 * 3901321 * 2
def baseEnd_3901321 : Nat := 2003252860479435797345657

theorem tailTrace_3901321 : CollatzResearch.WordTrace tailWord_3901321 prefixEnd_3901321 2003252860479435797345657 := by
  unfold tailWord_3901321
  simp only [CollatzResearch.WordTrace]
  refine ⟨142292866699187784425647817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94861911132791856283765211 142292866699187784425647817)
  ·
    refine ⟨106719650024390838319235863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142292866699187784425647817 106719650024390838319235863)
    ·
      refine ⟨160079475036586257478853795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106719650024390838319235863 160079475036586257478853795)
      ·
        refine ⟨240119212554879386218280693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160079475036586257478853795 240119212554879386218280693)
        ·
          refine ⟨22511176177019942457963815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240119212554879386218280693 22511176177019942457963815)
          ·
            refine ⟨33766764265529913686945723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22511176177019942457963815 33766764265529913686945723)
            ·
              refine ⟨50650146398294870530418585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33766764265529913686945723 50650146398294870530418585)
              ·
                refine ⟨37987609798721152897813939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50650146398294870530418585 37987609798721152897813939)
                ·
                  refine ⟨56981414698081729346720909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37987609798721152897813939 56981414698081729346720909)
                  ·
                    refine ⟨21368030511780648505020341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56981414698081729346720909 21368030511780648505020341)
                    ·
                      refine ⟨2003252860479435797345657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21368030511780648505020341 2003252860479435797345657)
                      ·
                        rfl

theorem cell23_3901321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_3901321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901321 prefixEnd_3901321 := by exact prefixLift 3901321
  have htrace : WordTrace (prefixWord ++ tailWord_3901321) baseStart_3901321 baseEnd_3901321 := by
    simpa [prefixWord, tailWord_3901321, baseEnd_3901321] using wordTrace_append hprefix tailTrace_3901321
  have hstable : (prefixWord ++ tailWord_3901321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901321).length < 2 ^ (prefixWord ++ tailWord_3901321).sum := by decide
  have hdescent : baseEnd_3901321 < baseStart_3901321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901331 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_3901331 : Nat := 118140960795 + 3901331 * 2 ^ 59
def prefixEnd_3901331 : Nat := 4983230072969 + 3 ^ 40 * 3901331 * 2
def baseEnd_3901331 : Nat := 2003257995285980758220611

theorem tailTrace_3901331 : CollatzResearch.WordTrace tailWord_3901331 prefixEnd_3901331 2003257995285980758220611 := by
  unfold tailWord_3901331
  simp only [CollatzResearch.WordTrace]
  refine ⟨142293231429151556133511847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94862154286101037422341231 142293231429151556133511847)
  ·
    refine ⟨213439847143727334200267771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142293231429151556133511847 213439847143727334200267771)
    ·
      refine ⟨320159770715591001300401657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213439847143727334200267771 320159770715591001300401657)
      ·
        refine ⟨240119828036693250975301243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320159770715591001300401657 240119828036693250975301243)
        ·
          refine ⟨360179742055039876462951865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240119828036693250975301243 360179742055039876462951865)
          ·
            refine ⟨270134806541279907347213899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360179742055039876462951865 270134806541279907347213899)
            ·
              refine ⟨405202209811919861020820849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270134806541279907347213899 405202209811919861020820849)
              ·
                refine ⟨303901657358939895765615637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405202209811919861020820849 303901657358939895765615637)
                ·
                  refine ⟨14245390188700307614013233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303901657358939895765615637 14245390188700307614013233)
                  ·
                    refine ⟨10684042641525230710509925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14245390188700307614013233 10684042641525230710509925)
                    ·
                      refine ⟨2003257995285980758220611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10684042641525230710509925 2003257995285980758220611)
                      ·
                        rfl

theorem cell23_3901331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_3901331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901331 prefixEnd_3901331 := by exact prefixLift 3901331
  have htrace : WordTrace (prefixWord ++ tailWord_3901331) baseStart_3901331 baseEnd_3901331 := by
    simpa [prefixWord, tailWord_3901331, baseEnd_3901331] using wordTrace_append hprefix tailTrace_3901331
  have hstable : (prefixWord ++ tailWord_3901331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901331).length < 2 ^ (prefixWord ++ tailWord_3901331).sum := by decide
  have hdescent : baseEnd_3901331 < baseStart_3901331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901338 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3901338 : Nat := 118140960795 + 3901338 * 2 ^ 59
def prefixEnd_3901338 : Nat := 4983230072969 + 3 ^ 40 * 3901338 * 2
def baseEnd_3901338 : Nat := 2003261589650562230833079

theorem tailTrace_3901338 : CollatzResearch.WordTrace tailWord_3901338 prefixEnd_3901338 2003261589650562230833079 := by
  unfold tailWord_3901338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35573371685031549082254167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94862324493417464219344445 35573371685031549082254167)
  ·
    refine ⟨53360057527547323623381251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35573371685031549082254167 53360057527547323623381251)
    ·
      refine ⟨80040086291320985435071877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53360057527547323623381251 80040086291320985435071877)
      ·
        refine ⟨15007516179622684769075977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80040086291320985435071877 15007516179622684769075977)
        ·
          refine ⟨11255637134717013576806983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15007516179622684769075977 11255637134717013576806983)
          ·
            refine ⟨16883455702075520365210475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255637134717013576806983 16883455702075520365210475)
            ·
              refine ⟨25325183553113280547815713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16883455702075520365210475 25325183553113280547815713)
              ·
                refine ⟨18993887664834960410861785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25325183553113280547815713 18993887664834960410861785)
                ·
                  refine ⟨14245415748626220308146339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18993887664834960410861785 14245415748626220308146339)
                  ·
                    refine ⟨21368123622939330462219509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14245415748626220308146339 21368123622939330462219509)
                    ·
                      refine ⟨2003261589650562230833079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21368123622939330462219509 2003261589650562230833079)
                      ·
                        rfl

theorem cell23_3901338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3901338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901338 prefixEnd_3901338 := by exact prefixLift 3901338
  have htrace : WordTrace (prefixWord ++ tailWord_3901338) baseStart_3901338 baseEnd_3901338 := by
    simpa [prefixWord, tailWord_3901338, baseEnd_3901338] using wordTrace_append hprefix tailTrace_3901338
  have hstable : (prefixWord ++ tailWord_3901338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901338).length < 2 ^ (prefixWord ++ tailWord_3901338).sum := by decide
  have hdescent : baseEnd_3901338 < baseStart_3901338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901368 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_3901368 : Nat := 118140960795 + 3901368 * 2 ^ 59
def prefixEnd_3901368 : Nat := 4983230072969 + 3 ^ 40 * 3901368 * 2
def baseEnd_3901368 : Nat := 2003276994070197113457941

theorem tailTrace_3901368 : CollatzResearch.WordTrace tailWord_3901368 prefixEnd_3901368 2003276994070197113457941 := by
  unfold tailWord_3901368
  simp only [CollatzResearch.WordTrace]
  refine ⟨71147290465008755726304379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94863053953345007635072505 71147290465008755726304379)
  ·
    refine ⟨106720935697513133589456569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71147290465008755726304379 106720935697513133589456569)
    ·
      refine ⟨80040701773134850192092427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106720935697513133589456569 80040701773134850192092427)
      ·
        refine ⟨120061052659702275288138641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80040701773134850192092427 120061052659702275288138641)
        ·
          refine ⟨90045789494776706466103981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120061052659702275288138641 90045789494776706466103981)
          ·
            refine ⟨33767171060541264924788993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90045789494776706466103981 33767171060541264924788993)
            ·
              refine ⟨25325378295405948693591745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33767171060541264924788993 25325378295405948693591745)
              ·
                refine ⟨18994033721554461520193809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25325378295405948693591745 18994033721554461520193809)
                ·
                  refine ⟨14245525291165846140145357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18994033721554461520193809 14245525291165846140145357)
                  ·
                    refine ⟨5342071984187192302554509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14245525291165846140145357 5342071984187192302554509)
                    ·
                      refine ⟨2003276994070197113457941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342071984187192302554509 2003276994070197113457941)
                      ·
                        rfl

theorem cell23_3901368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_3901368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901368 prefixEnd_3901368 := by exact prefixLift 3901368
  have htrace : WordTrace (prefixWord ++ tailWord_3901368) baseStart_3901368 baseEnd_3901368 := by
    simpa [prefixWord, tailWord_3901368, baseEnd_3901368] using wordTrace_append hprefix tailTrace_3901368
  have hstable : (prefixWord ++ tailWord_3901368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901368).length < 2 ^ (prefixWord ++ tailWord_3901368).sum := by decide
  have hdescent : baseEnd_3901368 < baseStart_3901368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901381 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3901381 : Nat := 118140960795 + 3901381 * 2 ^ 59
def prefixEnd_3901381 : Nat := 4983230072969 + 3 ^ 40 * 3901381 * 2
def baseEnd_3901381 : Nat := 2003283669318705562595381

theorem tailTrace_3901381 : CollatzResearch.WordTrace tailWord_3901381 prefixEnd_3901381 2003283669318705562595381 := by
  unfold tailWord_3901381
  simp only [CollatzResearch.WordTrace]
  refine ⟨142295055078970414672831997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94863370052646943115221331 142295055078970414672831997)
  ·
    refine ⟨53360645654613905502311999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142295055078970414672831997 53360645654613905502311999)
    ·
      refine ⟨80040968481920858253467999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53360645654613905502311999 80040968481920858253467999)
      ·
        refine ⟨120061452722881287380201999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80040968481920858253467999 120061452722881287380201999)
        ·
          refine ⟨180092179084321931070302999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120061452722881287380201999 180092179084321931070302999)
          ·
            refine ⟨270138268626482896605454499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180092179084321931070302999 270138268626482896605454499)
            ·
              refine ⟨405207402939724344908181749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270138268626482896605454499 405207402939724344908181749)
              ·
                refine ⟨37988194025599157335142039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405207402939724344908181749 37988194025599157335142039)
                ·
                  refine ⟨56982291038398736002713059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37988194025599157335142039 56982291038398736002713059)
                  ·
                    refine ⟨85473436557598104004069589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56982291038398736002713059 85473436557598104004069589)
                    ·
                      refine ⟨2003283669318705562595381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85473436557598104004069589 2003283669318705562595381)
                      ·
                        rfl

theorem cell23_3901381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3901381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901381 prefixEnd_3901381 := by exact prefixLift 3901381
  have htrace : WordTrace (prefixWord ++ tailWord_3901381) baseStart_3901381 baseEnd_3901381 := by
    simpa [prefixWord, tailWord_3901381, baseEnd_3901381] using wordTrace_append hprefix tailTrace_3901381
  have hstable : (prefixWord ++ tailWord_3901381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901381).length < 2 ^ (prefixWord ++ tailWord_3901381).sum := by decide
  have hdescent : baseEnd_3901381 < baseStart_3901381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901405 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3901405 : Nat := 118140960795 + 3901405 * 2 ^ 59
def prefixEnd_3901405 : Nat := 4983230072969 + 3 ^ 40 * 3901405 * 2
def baseEnd_3901405 : Nat := 667765330951471156231757

theorem tailTrace_3901405 : CollatzResearch.WordTrace tailWord_3901405 prefixEnd_3901405 667765330951471156231757 := by
  unfold tailWord_3901405
  simp only [CollatzResearch.WordTrace]
  refine ⟨142295930430883466771705669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94863953620588977847803779 142295930430883466771705669)
  ·
    refine ⟨26680486955790650019694813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142295930430883466771705669 26680486955790650019694813)
    ·
      refine ⟨10005182608421493757385555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26680486955790650019694813 10005182608421493757385555)
      ·
        refine ⟨15007773912632240636078333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10005182608421493757385555 15007773912632240636078333)
        ·
          refine ⟨5627915217237090238529375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15007773912632240636078333 5627915217237090238529375)
          ·
            refine ⟨8441872825855635357794063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627915217237090238529375 8441872825855635357794063)
            ·
              refine ⟨12662809238783453036691095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441872825855635357794063 12662809238783453036691095)
              ·
                refine ⟨18994213858175179555036643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12662809238783453036691095 18994213858175179555036643)
                ·
                  refine ⟨28491320787262769332554965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18994213858175179555036643 28491320787262769332554965)
                  ·
                    refine ⟨667765330951471156231757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28491320787262769332554965 667765330951471156231757)
                    ·
                      rfl

theorem cell23_3901405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3901405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901405 prefixEnd_3901405 := by exact prefixLift 3901405
  have htrace : WordTrace (prefixWord ++ tailWord_3901405) baseStart_3901405 baseEnd_3901405 := by
    simpa [prefixWord, tailWord_3901405, baseEnd_3901405] using wordTrace_append hprefix tailTrace_3901405
  have hstable : (prefixWord ++ tailWord_3901405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901405).length < 2 ^ (prefixWord ++ tailWord_3901405).sum := by decide
  have hdescent : baseEnd_3901405 < baseStart_3901405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901469 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3901469 : Nat := 118140960795 + 3901469 * 2 ^ 59
def prefixEnd_3901469 : Nat := 4983230072969 + 3 ^ 40 * 3901469 * 2
def baseEnd_3901469 : Nat := 667776285205433739431659

theorem tailTrace_3901469 : CollatzResearch.WordTrace tailWord_3901469 prefixEnd_3901469 667776285205433739431659 := by
  unfold tailWord_3901469
  simp only [CollatzResearch.WordTrace]
  refine ⟨142298264702651605702035461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94865509801767737134690307 142298264702651605702035461)
  ·
    refine ⟨26680924631747176069131649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142298264702651605702035461 26680924631747176069131649)
    ·
      refine ⟨20010693473810382051848737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26680924631747176069131649 20010693473810382051848737)
      ·
        refine ⟨15008020105357786538886553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20010693473810382051848737 15008020105357786538886553)
        ·
          refine ⟨11256015079018339904164915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15008020105357786538886553 11256015079018339904164915)
          ·
            refine ⟨16884022618527509856247373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256015079018339904164915 16884022618527509856247373)
            ·
              refine ⟨6331508481947816196092765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16884022618527509856247373 6331508481947816196092765)
              ·
                refine ⟨2374315680730431073534787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6331508481947816196092765 2374315680730431073534787)
                ·
                  refine ⟨3561473521095646610302181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374315680730431073534787 3561473521095646610302181)
                  ·
                    refine ⟨667776285205433739431659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561473521095646610302181 667776285205433739431659)
                    ·
                      rfl

theorem cell23_3901469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3901469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901469 prefixEnd_3901469 := by exact prefixLift 3901469
  have htrace : WordTrace (prefixWord ++ tailWord_3901469) baseStart_3901469 baseEnd_3901469 := by
    simpa [prefixWord, tailWord_3901469, baseEnd_3901469] using wordTrace_append hprefix tailTrace_3901469
  have hstable : (prefixWord ++ tailWord_3901469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901469).length < 2 ^ (prefixWord ++ tailWord_3901469).sum := by decide
  have hdescent : baseEnd_3901469 < baseStart_3901469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901479 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3901479 : Nat := 118140960795 + 3901479 * 2 ^ 59
def prefixEnd_3901479 : Nat := 4983230072969 + 3 ^ 40 * 3901479 * 2
def baseEnd_3901479 : Nat := 2003333990422846179169931

theorem tailTrace_3901479 : CollatzResearch.WordTrace tailWord_3901479 prefixEnd_3901479 2003333990422846179169931 := by
  unfold tailWord_3901479
  simp only [CollatzResearch.WordTrace]
  refine ⟨142298629432615377409899491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94865752955076918273266327 142298629432615377409899491)
  ·
    refine ⟨213447944148923066114849237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142298629432615377409899491 213447944148923066114849237)
    ·
      refine ⟨5002686190990384362066779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 213447944148923066114849237 5002686190990384362066779)
      ·
        refine ⟨7504029286485576543100169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002686190990384362066779 7504029286485576543100169)
        ·
          refine ⟨5628021964864182407325127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504029286485576543100169 5628021964864182407325127)
          ·
            refine ⟨8442032947296273610987691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628021964864182407325127 8442032947296273610987691)
            ·
              refine ⟨12663049420944410416481537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442032947296273610987691 12663049420944410416481537)
              ·
                refine ⟨9497287065708307812361153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663049420944410416481537 9497287065708307812361153)
                ·
                  refine ⟨7122965299281230859270865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497287065708307812361153 7122965299281230859270865)
                  ·
                    refine ⟨5342223974460923144453149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7122965299281230859270865 5342223974460923144453149)
                    ·
                      refine ⟨2003333990422846179169931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342223974460923144453149 2003333990422846179169931)
                      ·
                        rfl

theorem cell23_3901479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3901479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901479 prefixEnd_3901479 := by exact prefixLift 3901479
  have htrace : WordTrace (prefixWord ++ tailWord_3901479) baseStart_3901479 baseEnd_3901479 := by
    simpa [prefixWord, tailWord_3901479, baseEnd_3901479] using wordTrace_append hprefix tailTrace_3901479
  have hstable : (prefixWord ++ tailWord_3901479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901479).length < 2 ^ (prefixWord ++ tailWord_3901479).sum := by decide
  have hdescent : baseEnd_3901479 < baseStart_3901479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901486 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3901486 : Nat := 118140960795 + 3901486 * 2 ^ 59
def prefixEnd_3901486 : Nat := 4983230072969 + 3 ^ 40 * 3901486 * 2
def baseEnd_3901486 : Nat := 667779194929142550594133

theorem tailTrace_3901486 : CollatzResearch.WordTrace tailWord_3901486 prefixEnd_3901486 667779194929142550594133 := by
  unfold tailWord_3901486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787360592948752200675539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94865923162393345070269541 17787360592948752200675539)
  ·
    refine ⟨26681040889423128301013309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17787360592948752200675539 26681040889423128301013309)
    ·
      refine ⟨10005390333533673112879991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26681040889423128301013309 10005390333533673112879991)
      ·
        refine ⟨15008085500300509669319987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10005390333533673112879991 15008085500300509669319987)
        ·
          refine ⟨22512128250450764503979981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15008085500300509669319987 22512128250450764503979981)
          ·
            refine ⟨8442048093919036688992493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22512128250450764503979981 8442048093919036688992493)
            ·
              refine ⟨3165768035219638758372185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8442048093919036688992493 3165768035219638758372185)
              ·
                refine ⟨2374326026414729068779139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3165768035219638758372185 2374326026414729068779139)
                ·
                  refine ⟨3561489039622093603168709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374326026414729068779139 3561489039622093603168709)
                  ·
                    refine ⟨667779194929142550594133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561489039622093603168709 667779194929142550594133)
                    ·
                      rfl

theorem cell23_3901486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3901486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901486 prefixEnd_3901486 := by exact prefixLift 3901486
  have htrace : WordTrace (prefixWord ++ tailWord_3901486) baseStart_3901486 baseEnd_3901486 := by
    simpa [prefixWord, tailWord_3901486, baseEnd_3901486] using wordTrace_append hprefix tailTrace_3901486
  have hstable : (prefixWord ++ tailWord_3901486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901486).length < 2 ^ (prefixWord ++ tailWord_3901486).sum := by decide
  have hdescent : baseEnd_3901486 < baseStart_3901486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901498 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3901498 : Nat := 118140960795 + 3901498 * 2 ^ 59
def prefixEnd_3901498 : Nat := 4983230072969 + 3 ^ 40 * 3901498 * 2
def baseEnd_3901498 : Nat := 2003343746555281604832343

theorem tailTrace_3901498 : CollatzResearch.WordTrace tailWord_3901498 prefixEnd_3901498 2003343746555281604832343 := by
  unfold tailWord_3901498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574830604886635913710287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94866214946364362436560765 35574830604886635913710287)
  ·
    refine ⟨53362245907329953870565431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35574830604886635913710287 53362245907329953870565431)
    ·
      refine ⟨80043368860994930805848147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53362245907329953870565431 80043368860994930805848147)
      ·
        refine ⟨120065053291492396208772221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80043368860994930805848147 120065053291492396208772221)
        ·
          refine ⟨45024394984309648578289583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120065053291492396208772221 45024394984309648578289583)
          ·
            refine ⟨67536592476464472867434375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45024394984309648578289583 67536592476464472867434375)
            ·
              refine ⟨101304888714696709301151563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67536592476464472867434375 101304888714696709301151563)
              ·
                refine ⟨151957333072045063951727345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101304888714696709301151563 151957333072045063951727345)
                ·
                  refine ⟨113967999804033797963795509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151957333072045063951727345 113967999804033797963795509)
                  ·
                    refine ⟨10684499981628168559105829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113967999804033797963795509 10684499981628168559105829)
                    ·
                      refine ⟨2003343746555281604832343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10684499981628168559105829 2003343746555281604832343)
                      ·
                        rfl

theorem cell23_3901498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3901498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901498 prefixEnd_3901498 := by exact prefixLift 3901498
  have htrace : WordTrace (prefixWord ++ tailWord_3901498) baseStart_3901498 baseEnd_3901498 := by
    simpa [prefixWord, tailWord_3901498, baseEnd_3901498] using wordTrace_append hprefix tailTrace_3901498
  have hstable : (prefixWord ++ tailWord_3901498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901498).length < 2 ^ (prefixWord ++ tailWord_3901498).sum := by decide
  have hdescent : baseEnd_3901498 < baseStart_3901498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901525 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3901525 : Nat := 118140960795 + 3901525 * 2 ^ 59
def prefixEnd_3901525 : Nat := 4983230072969 + 3 ^ 40 * 3901525 * 2
def baseEnd_3901525 : Nat := 667785870177650999731573

theorem tailTrace_3901525 : CollatzResearch.WordTrace tailWord_3901525 prefixEnd_3901525 667785870177650999731573 := by
  unfold tailWord_3901525
  simp only [CollatzResearch.WordTrace]
  refine ⟨142300307190448727266074029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94866871460299151510716019 142300307190448727266074029)
  ·
    refine ⟨53362615196418272724777761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142300307190448727266074029 53362615196418272724777761)
    ·
      refine ⟨40021961397313704543583321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53362615196418272724777761 40021961397313704543583321)
      ·
        refine ⟨30016471047985278407687491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40021961397313704543583321 30016471047985278407687491)
        ·
          refine ⟨45024706571977917611531237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30016471047985278407687491 45024706571977917611531237)
          ·
            refine ⟨8442132482245859552162107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45024706571977917611531237 8442132482245859552162107)
            ·
              refine ⟨12663198723368789328243161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442132482245859552162107 12663198723368789328243161)
              ·
                refine ⟨9497399042526591996182371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663198723368789328243161 9497399042526591996182371)
                ·
                  refine ⟨14246098563789887994273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497399042526591996182371 14246098563789887994273557)
                  ·
                    refine ⟨667785870177650999731573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14246098563789887994273557 667785870177650999731573)
                    ·
                      rfl

theorem cell23_3901525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3901525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901525 prefixEnd_3901525 := by exact prefixLift 3901525
  have htrace : WordTrace (prefixWord ++ tailWord_3901525) baseStart_3901525 baseEnd_3901525 := by
    simpa [prefixWord, tailWord_3901525, baseEnd_3901525] using wordTrace_append hprefix tailTrace_3901525
  have hstable : (prefixWord ++ tailWord_3901525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901525).length < 2 ^ (prefixWord ++ tailWord_3901525).sum := by decide
  have hdescent : baseEnd_3901525 < baseStart_3901525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901549 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3901549 : Nat := 118140960795 + 3901549 * 2 ^ 59
def prefixEnd_3901549 : Nat := 4983230072969 + 3 ^ 40 * 3901549 * 2
def baseEnd_3901549 : Nat := 2003369934068660905294609

theorem tailTrace_3901549 : CollatzResearch.WordTrace tailWord_3901549 prefixEnd_3901549 2003369934068660905294609 := by
  unfold tailWord_3901549
  simp only [CollatzResearch.WordTrace]
  refine ⟨142301182542361779364947701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94867455028241186243298467 142301182542361779364947701)
  ·
    refine ⟨13340735863346416815463847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142301182542361779364947701 13340735863346416815463847)
    ·
      refine ⟨20011103795019625223195771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340735863346416815463847 20011103795019625223195771)
      ·
        refine ⟨30016655692529437834793657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20011103795019625223195771 30016655692529437834793657)
        ·
          refine ⟨22512491769397078376095243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016655692529437834793657 22512491769397078376095243)
          ·
            refine ⟨33768737654095617564142865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22512491769397078376095243 33768737654095617564142865)
            ·
              refine ⟨25326553240571713173107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33768737654095617564142865 25326553240571713173107149)
              ·
                refine ⟨9497457465214392439915181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25326553240571713173107149 9497457465214392439915181)
                ·
                  refine ⟨3561546549455397164968193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9497457465214392439915181 3561546549455397164968193)
                  ·
                    refine ⟨2671159912091547873726145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3561546549455397164968193 2671159912091547873726145)
                    ·
                      refine ⟨2003369934068660905294609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671159912091547873726145 2003369934068660905294609)
                      ·
                        rfl

theorem cell23_3901549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3901549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901549 prefixEnd_3901549 := by exact prefixLift 3901549
  have htrace : WordTrace (prefixWord ++ tailWord_3901549) baseStart_3901549 baseEnd_3901549 := by
    simpa [prefixWord, tailWord_3901549, baseEnd_3901549] using wordTrace_append hprefix tailTrace_3901549
  have hstable : (prefixWord ++ tailWord_3901549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901549).length < 2 ^ (prefixWord ++ tailWord_3901549).sum := by decide
  have hdescent : baseEnd_3901549 < baseStart_3901549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901568 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_3901568 : Nat := 118140960795 + 3901568 * 2 ^ 59
def prefixEnd_3901568 : Nat := 4983230072969 + 3 ^ 40 * 3901568 * 2
def baseEnd_3901568 : Nat := 667793230067032110319007

theorem tailTrace_3901568 : CollatzResearch.WordTrace tailWord_3901568 prefixEnd_3901568 667793230067032110319007 := by
  unfold tailWord_3901568
  simp only [CollatzResearch.WordTrace]
  refine ⟨71150937764646472804944679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94867917019528630406592905 71150937764646472804944679)
  ·
    refine ⟨106726406646969709207417019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71150937764646472804944679 106726406646969709207417019)
    ·
      refine ⟨160089609970454563811125529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106726406646969709207417019 160089609970454563811125529)
      ·
        refine ⟨120067207477840922858344147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160089609970454563811125529 120067207477840922858344147)
        ·
          refine ⟨180100811216761384287516221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120067207477840922858344147 180100811216761384287516221)
          ·
            refine ⟨67537804206285519107818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180100811216761384287516221 67537804206285519107818583)
            ·
              refine ⟨101306706309428278661727875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67537804206285519107818583 101306706309428278661727875)
              ·
                refine ⟨151960059464142417992591813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101306706309428278661727875 151960059464142417992591813)
                ·
                  refine ⟨28492511149526703373610965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151960059464142417992591813 28492511149526703373610965)
                  ·
                    refine ⟨667793230067032110319007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28492511149526703373610965 667793230067032110319007)
                    ·
                      rfl

theorem cell23_3901568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_3901568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901568 prefixEnd_3901568 := by exact prefixLift 3901568
  have htrace : WordTrace (prefixWord ++ tailWord_3901568) baseStart_3901568 baseEnd_3901568 := by
    simpa [prefixWord, tailWord_3901568, baseEnd_3901568] using wordTrace_append hprefix tailTrace_3901568
  have hstable : (prefixWord ++ tailWord_3901568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901568).length < 2 ^ (prefixWord ++ tailWord_3901568).sum := by decide
  have hdescent : baseEnd_3901568 < baseStart_3901568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901599 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3901599 : Nat := 118140960795 + 3901599 * 2 ^ 59
def prefixEnd_3901599 : Nat := 4983230072969 + 3 ^ 40 * 3901599 * 2
def baseEnd_3901599 : Nat := 2003395608101385709669379

theorem tailTrace_3901599 : CollatzResearch.WordTrace tailWord_3901599 prefixEnd_3901599 2003395608101385709669379 := by
  unfold tailWord_3901599
  simp only [CollatzResearch.WordTrace]
  refine ⟨142303006192180637904267851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94868670794787091936178567 142303006192180637904267851)
  ·
    refine ⟨213454509288270956856401777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142303006192180637904267851 213454509288270956856401777)
    ·
      refine ⟨160090881966203217642301333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213454509288270956856401777 160090881966203217642301333)
      ·
        refine ⟨7504260092165775826982875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160090881966203217642301333 7504260092165775826982875)
        ·
          refine ⟨11256390138248663740474313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504260092165775826982875 11256390138248663740474313)
          ·
            refine ⟨8442292603686497805355735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11256390138248663740474313 8442292603686497805355735)
            ·
              refine ⟨12663438905529746708033603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442292603686497805355735 12663438905529746708033603)
              ·
                refine ⟨18995158358294620062050405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12663438905529746708033603 18995158358294620062050405)
                ·
                  refine ⟨3561592192180241261634451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18995158358294620062050405 3561592192180241261634451)
                  ·
                    refine ⟨5342388288270361892451677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3561592192180241261634451 5342388288270361892451677)
                    ·
                      refine ⟨2003395608101385709669379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342388288270361892451677 2003395608101385709669379)
                      ·
                        rfl

theorem cell23_3901599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3901599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901599 prefixEnd_3901599 := by exact prefixLift 3901599
  have htrace : WordTrace (prefixWord ++ tailWord_3901599) baseStart_3901599 baseEnd_3901599 := by
    simpa [prefixWord, tailWord_3901599, baseEnd_3901599] using wordTrace_append hprefix tailTrace_3901599
  have hstable : (prefixWord ++ tailWord_3901599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901599).length < 2 ^ (prefixWord ++ tailWord_3901599).sum := by decide
  have hdescent : baseEnd_3901599 < baseStart_3901599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901620 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3901620 : Nat := 118140960795 + 3901620 * 2 ^ 59
def prefixEnd_3901620 : Nat := 4983230072969 + 3 ^ 40 * 3901620 * 2
def baseEnd_3901620 : Nat := 2003406391195130127506783

theorem tailTrace_3901620 : CollatzResearch.WordTrace tailWord_3901620 prefixEnd_3901620 2003406391195130127506783 := by
  unfold tailWord_3901620
  simp only [CollatzResearch.WordTrace]
  refine ⟨71151886062552279245391157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94869181416736372327188209 71151886062552279245391157)
  ·
    refine ⟨6670489318364276179255421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71151886062552279245391157 6670489318364276179255421)
    ·
      refine ⟨2501433494386603567220783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6670489318364276179255421 2501433494386603567220783)
      ·
        refine ⟨3752150241579905350831175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501433494386603567220783 3752150241579905350831175)
        ·
          refine ⟨5628225362369858026246763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752150241579905350831175 5628225362369858026246763)
          ·
            refine ⟨8442338043554787039370145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628225362369858026246763 8442338043554787039370145)
            ·
              refine ⟨6331753532666090279527609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8442338043554787039370145 6331753532666090279527609)
              ·
                refine ⟨4748815149499567709645707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6331753532666090279527609 4748815149499567709645707)
                ·
                  refine ⟨7123222724249351564468561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748815149499567709645707 7123222724249351564468561)
                  ·
                    refine ⟨5342417043187013673351421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123222724249351564468561 5342417043187013673351421)
                    ·
                      refine ⟨2003406391195130127506783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342417043187013673351421 2003406391195130127506783)
                      ·
                        rfl

theorem cell23_3901620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3901620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901620 prefixEnd_3901620 := by exact prefixLift 3901620
  have htrace : WordTrace (prefixWord ++ tailWord_3901620) baseStart_3901620 baseEnd_3901620 := by
    simpa [prefixWord, tailWord_3901620, baseEnd_3901620] using wordTrace_append hprefix tailTrace_3901620
  have hstable : (prefixWord ++ tailWord_3901620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901620).length < 2 ^ (prefixWord ++ tailWord_3901620).sum := by decide
  have hdescent : baseEnd_3901620 < baseStart_3901620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901625 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3901625 : Nat := 118140960795 + 3901625 * 2 ^ 59
def prefixEnd_3901625 : Nat := 4983230072969 + 3 ^ 40 * 3901625 * 2
def baseEnd_3901625 : Nat := 2003408958598402607944259

theorem tailTrace_3901625 : CollatzResearch.WordTrace tailWord_3901625 prefixEnd_3901625 2003408958598402607944259 := by
  unfold tailWord_3901625
  simp only [CollatzResearch.WordTrace]
  refine ⟨142303954490086444344714329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94869302993390962896476219 142303954490086444344714329)
  ·
    refine ⟨106727965867564833258535747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142303954490086444344714329 106727965867564833258535747)
    ·
      refine ⟨160091948801347249887803621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106727965867564833258535747 160091948801347249887803621)
      ·
        refine ⟨30017240400252609353963179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160091948801347249887803621 30017240400252609353963179)
        ·
          refine ⟨45025860600378914030944769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30017240400252609353963179 45025860600378914030944769)
          ·
            refine ⟨33769395450284185523208577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45025860600378914030944769 33769395450284185523208577)
            ·
              refine ⟨25327046587713139142406433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33769395450284185523208577 25327046587713139142406433)
              ·
                refine ⟨18995284940784854356804825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25327046587713139142406433 18995284940784854356804825)
                ·
                  refine ⟨14246463705588640767603619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18995284940784854356804825 14246463705588640767603619)
                  ·
                    refine ⟨21369695558382961151405429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14246463705588640767603619 21369695558382961151405429)
                    ·
                      refine ⟨2003408958598402607944259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21369695558382961151405429 2003408958598402607944259)
                      ·
                        rfl

theorem cell23_3901625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3901625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901625 prefixEnd_3901625 := by exact prefixLift 3901625
  have htrace : WordTrace (prefixWord ++ tailWord_3901625) baseStart_3901625 baseEnd_3901625 := by
    simpa [prefixWord, tailWord_3901625, baseEnd_3901625] using wordTrace_append hprefix tailTrace_3901625
  have hstable : (prefixWord ++ tailWord_3901625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901625).length < 2 ^ (prefixWord ++ tailWord_3901625).sum := by decide
  have hdescent : baseEnd_3901625 < baseStart_3901625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901675 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 4, 5]
def baseStart_3901675 : Nat := 118140960795 + 3901675 * 2 ^ 59
def prefixEnd_3901675 : Nat := 4983230072969 + 3 ^ 40 * 3901675 * 2
def baseEnd_3901675 : Nat := 667811544210375804106343

theorem tailTrace_3901675 : CollatzResearch.WordTrace tailWord_3901675 prefixEnd_3901675 667811544210375804106343 := by
  unfold tailWord_3901675
  simp only [CollatzResearch.WordTrace]
  refine ⟨142305778139905302884034479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94870518759936868589356319 142305778139905302884034479)
  ·
    refine ⟨213458667209857954326051719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142305778139905302884034479 213458667209857954326051719)
    ·
      refine ⟨320188000814786931489077579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213458667209857954326051719 320188000814786931489077579)
      ·
        refine ⟨480282001222180397233616369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320188000814786931489077579 480282001222180397233616369)
        ·
          refine ⟨360211500916635297925212277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480282001222180397233616369 360211500916635297925212277)
          ·
            refine ⟨33769828210934559180488651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360211500916635297925212277 33769828210934559180488651)
            ·
              refine ⟨50654742316401838770732977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33769828210934559180488651 50654742316401838770732977)
              ·
                refine ⟨37991056737301379078049733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50654742316401838770732977 37991056737301379078049733)
                ·
                  refine ⟨7123323138244008577134325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37991056737301379078049733 7123323138244008577134325)
                  ·
                    refine ⟨667811544210375804106343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7123323138244008577134325 667811544210375804106343)
                    ·
                      rfl

theorem cell23_3901675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 5].length) (baseStart_3901675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901675 prefixEnd_3901675 := by exact prefixLift 3901675
  have htrace : WordTrace (prefixWord ++ tailWord_3901675) baseStart_3901675 baseEnd_3901675 := by
    simpa [prefixWord, tailWord_3901675, baseEnd_3901675] using wordTrace_append hprefix tailTrace_3901675
  have hstable : (prefixWord ++ tailWord_3901675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901675).length < 2 ^ (prefixWord ++ tailWord_3901675).sum := by decide
  have hdescent : baseEnd_3901675 < baseStart_3901675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901692 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_3901692 : Nat := 118140960795 + 3901692 * 2 ^ 59
def prefixEnd_3901692 : Nat := 4983230072969 + 3 ^ 40 * 3901692 * 2
def baseEnd_3901692 : Nat := 667814453934084615268817

theorem tailTrace_3901692 : CollatzResearch.WordTrace tailWord_3901692 prefixEnd_3901692 667814453934084615268817 := by
  unfold tailWord_3901692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71153199090421857393701665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94870932120562476524935553 71153199090421857393701665)
  ·
    refine ⟨53364899317816393045276249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71153199090421857393701665 53364899317816393045276249)
    ·
      refine ⟨40023674488362294783957187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53364899317816393045276249 40023674488362294783957187)
      ·
        refine ⟨60035511732543442175935781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40023674488362294783957187 60035511732543442175935781)
        ·
          refine ⟨11256658449851895407987959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60035511732543442175935781 11256658449851895407987959)
          ·
            refine ⟨16884987674777843111981939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256658449851895407987959 16884987674777843111981939)
            ·
              refine ⟨25327481512166764667972909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884987674777843111981939 25327481512166764667972909)
              ·
                refine ⟨9497805567062536750489841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25327481512166764667972909 9497805567062536750489841)
                ·
                  refine ⟨7123354175296902562867381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497805567062536750489841 7123354175296902562867381)
                  ·
                    refine ⟨667814453934084615268817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7123354175296902562867381 667814453934084615268817)
                    ·
                      rfl

theorem cell23_3901692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_3901692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901692 prefixEnd_3901692 := by exact prefixLift 3901692
  have htrace : WordTrace (prefixWord ++ tailWord_3901692) baseStart_3901692 baseEnd_3901692 := by
    simpa [prefixWord, tailWord_3901692, baseEnd_3901692] using wordTrace_append hprefix tailTrace_3901692
  have hstable : (prefixWord ++ tailWord_3901692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901692).length < 2 ^ (prefixWord ++ tailWord_3901692).sum := by decide
  have hdescent : baseEnd_3901692 < baseStart_3901692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901746 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3901746 : Nat := 118140960795 + 3901746 * 2 ^ 59
def prefixEnd_3901746 : Nat := 4983230072969 + 3 ^ 40 * 3901746 * 2
def baseEnd_3901746 : Nat := 2003471089757596634531203

theorem tailTrace_3901746 : CollatzResearch.WordTrace tailWord_3901746 prefixEnd_3901746 2003471089757596634531203 := by
  unfold tailWord_3901746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35577091930662020502467273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94872245148432054673246061 35577091930662020502467273)
  ·
    refine ⟨26682818947996515376850455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35577091930662020502467273 26682818947996515376850455)
    ·
      refine ⟨40024228421994773065275683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26682818947996515376850455 40024228421994773065275683)
      ·
        refine ⟨60036342632992159597913525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40024228421994773065275683 60036342632992159597913525)
        ·
          refine ⟨5628407121843014962304393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60036342632992159597913525 5628407121843014962304393)
          ·
            refine ⟨4221305341382261221728295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5628407121843014962304393 4221305341382261221728295)
            ·
              refine ⟨6331958012073391832592443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221305341382261221728295 6331958012073391832592443)
              ·
                refine ⟨9497937018110087748888665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331958012073391832592443 9497937018110087748888665)
                ·
                  refine ⟨7123452763582565811666499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497937018110087748888665 7123452763582565811666499)
                  ·
                    refine ⟨10685179145373848717499749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123452763582565811666499 10685179145373848717499749)
                    ·
                      refine ⟨2003471089757596634531203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10685179145373848717499749 2003471089757596634531203)
                      ·
                        rfl

theorem cell23_3901746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3901746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901746 prefixEnd_3901746 := by exact prefixLift 3901746
  have htrace : WordTrace (prefixWord ++ tailWord_3901746) baseStart_3901746 baseEnd_3901746 := by
    simpa [prefixWord, tailWord_3901746, baseEnd_3901746] using wordTrace_append hprefix tailTrace_3901746
  have hstable : (prefixWord ++ tailWord_3901746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901746).length < 2 ^ (prefixWord ++ tailWord_3901746).sum := by decide
  have hdescent : baseEnd_3901746 < baseStart_3901746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901756 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_3901756 : Nat := 118140960795 + 3901756 * 2 ^ 59
def prefixEnd_3901756 : Nat := 4983230072969 + 3 ^ 40 * 3901756 * 2
def baseEnd_3901756 : Nat := 667825408188047198468719

theorem tailTrace_3901756 : CollatzResearch.WordTrace tailWord_3901756 prefixEnd_3901756 667825408188047198468719 := by
  unfold tailWord_3901756
  simp only [CollatzResearch.WordTrace]
  refine ⟨71154366226305926858866561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94872488301741235811822081 71154366226305926858866561)
  ·
    refine ⟨53365774669729445144149921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71154366226305926858866561 53365774669729445144149921)
    ·
      refine ⟨40024331002297083858112441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53365774669729445144149921 40024331002297083858112441)
      ·
        refine ⟨30018248251722812893584331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40024331002297083858112441 30018248251722812893584331)
        ·
          refine ⟨45027372377584219340376497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30018248251722812893584331 45027372377584219340376497)
          ·
            refine ⟨33770529283188164505282373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45027372377584219340376497 33770529283188164505282373)
            ·
              refine ⟨6331974240597780844740445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33770529283188164505282373 6331974240597780844740445)
              ·
                refine ⟨2374490340224167816777667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6331974240597780844740445 2374490340224167816777667)
                ·
                  refine ⟨3561735510336251725166501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374490340224167816777667 3561735510336251725166501)
                  ·
                    refine ⟨667825408188047198468719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561735510336251725166501 667825408188047198468719)
                    ·
                      rfl

theorem cell23_3901756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_3901756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901756 prefixEnd_3901756 := by exact prefixLift 3901756
  have htrace : WordTrace (prefixWord ++ tailWord_3901756) baseStart_3901756 baseEnd_3901756 := by
    simpa [prefixWord, tailWord_3901756, baseEnd_3901756] using wordTrace_append hprefix tailTrace_3901756
  have hstable : (prefixWord ++ tailWord_3901756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901756).length < 2 ^ (prefixWord ++ tailWord_3901756).sum := by decide
  have hdescent : baseEnd_3901756 < baseStart_3901756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901775 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_3901775 : Nat := 118140960795 + 3901775 * 2 ^ 59
def prefixEnd_3901775 : Nat := 4983230072969 + 3 ^ 40 * 3901775 * 2
def baseEnd_3901775 : Nat := 2003485980696577021068569

theorem tailTrace_3901775 : CollatzResearch.WordTrace tailWord_3901775 prefixEnd_3901775 2003485980696577021068569 := by
  unfold tailWord_3901775
  simp only [CollatzResearch.WordTrace]
  refine ⟨142309425439543019962674779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94872950293028679975116519 142309425439543019962674779)
  ·
    refine ⟨213464138159314529944012169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142309425439543019962674779 213464138159314529944012169)
    ·
      refine ⟨160098103619485897458009127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213464138159314529944012169 160098103619485897458009127)
      ·
        refine ⟨240147155429228846187013691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160098103619485897458009127 240147155429228846187013691)
        ·
          refine ⟨360220733143843269280520537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240147155429228846187013691 360220733143843269280520537)
          ·
            refine ⟨270165549857882451960390403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360220733143843269280520537 270165549857882451960390403)
            ·
              refine ⟨405248324786823677940585605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270165549857882451960390403 405248324786823677940585605)
              ·
                refine ⟨75984060897529439613859801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405248324786823677940585605 75984060897529439613859801)
                ·
                  refine ⟨56988045673147079710394851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75984060897529439613859801 56988045673147079710394851)
                  ·
                    refine ⟨85482068509720619565592277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56988045673147079710394851 85482068509720619565592277)
                    ·
                      refine ⟨2003485980696577021068569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85482068509720619565592277 2003485980696577021068569)
                      ·
                        rfl

theorem cell23_3901775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_3901775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901775 prefixEnd_3901775 := by exact prefixLift 3901775
  have htrace : WordTrace (prefixWord ++ tailWord_3901775) baseStart_3901775 baseEnd_3901775 := by
    simpa [prefixWord, tailWord_3901775, baseEnd_3901775] using wordTrace_append hprefix tailTrace_3901775
  have hstable : (prefixWord ++ tailWord_3901775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901775).length < 2 ^ (prefixWord ++ tailWord_3901775).sum := by decide
  have hdescent : baseEnd_3901775 < baseStart_3901775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901799 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 1, 5]
def baseStart_3901799 : Nat := 118140960795 + 3901799 * 2 ^ 59
def prefixEnd_3901799 : Nat := 4983230072969 + 3 ^ 40 * 3901799 * 2
def baseEnd_3901799 : Nat := 667832768077428309056153

theorem tailTrace_3901799 : CollatzResearch.WordTrace tailWord_3901799 prefixEnd_3901799 667832768077428309056153 := by
  unfold tailWord_3901799
  simp only [CollatzResearch.WordTrace]
  refine ⟨142310300791456072061548451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94873533860970714707698967 142310300791456072061548451)
  ·
    refine ⟨213465451187184108092322677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142310300791456072061548451 213465451187184108092322677)
    ·
      refine ⟨20012386048798510133655251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213465451187184108092322677 20012386048798510133655251)
      ·
        refine ⟨30018579073197765200482877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012386048798510133655251 30018579073197765200482877)
        ·
          refine ⟨11256967152449161950181079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30018579073197765200482877 11256967152449161950181079)
          ·
            refine ⟨16885450728673742925271619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256967152449161950181079 16885450728673742925271619)
            ·
              refine ⟨25328176093010614387907429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16885450728673742925271619 25328176093010614387907429)
              ·
                refine ⟨4749033017439490197732643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25328176093010614387907429 4749033017439490197732643)
                ·
                  refine ⟨7123549526159235296598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749033017439490197732643 7123549526159235296598965)
                  ·
                    refine ⟨667832768077428309056153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7123549526159235296598965 667832768077428309056153)
                    ·
                      rfl

theorem cell23_3901799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_3901799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901799 prefixEnd_3901799 := by exact prefixLift 3901799
  have htrace : WordTrace (prefixWord ++ tailWord_3901799) baseStart_3901799 baseEnd_3901799 := by
    simpa [prefixWord, tailWord_3901799, baseEnd_3901799] using wordTrace_append hprefix tailTrace_3901799
  have hstable : (prefixWord ++ tailWord_3901799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901799).length < 2 ^ (prefixWord ++ tailWord_3901799).sum := by decide
  have hdescent : baseEnd_3901799 < baseStart_3901799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901819 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 4]
def baseStart_3901819 : Nat := 118140960795 + 3901819 * 2 ^ 59
def prefixEnd_3901819 : Nat := 4983230072969 + 3 ^ 40 * 3901819 * 2
def baseEnd_3901819 : Nat := 2003508573845374848918367

theorem tailTrace_3901819 : CollatzResearch.WordTrace tailWord_3901819 prefixEnd_3901819 2003508573845374848918367 := by
  unfold tailWord_3901819
  simp only [CollatzResearch.WordTrace]
  refine ⟨142311030251383615477276511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94874020167589076984851007 142311030251383615477276511)
  ·
    refine ⟨213466545377075423215914767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142311030251383615477276511 213466545377075423215914767)
    ·
      refine ⟨320199818065613134823872151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213466545377075423215914767 320199818065613134823872151)
      ·
        refine ⟨480299727098419702235808227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320199818065613134823872151 480299727098419702235808227)
        ·
          refine ⟨720449590647629553353712341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480299727098419702235808227 720449590647629553353712341)
          ·
            refine ⟨16885537280803817656727633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 720449590647629553353712341 16885537280803817656727633)
            ·
              refine ⟨12664152960602863242545725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16885537280803817656727633 12664152960602863242545725)
              ·
                refine ⟨4749057360226073715954647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12664152960602863242545725 4749057360226073715954647)
                ·
                  refine ⟨7123586040339110573931971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749057360226073715954647 7123586040339110573931971)
                  ·
                    refine ⟨10685379060508665860897957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123586040339110573931971 10685379060508665860897957)
                    ·
                      refine ⟨2003508573845374848918367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10685379060508665860897957 2003508573845374848918367)
                      ·
                        rfl

theorem cell23_3901819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 4].length) (baseStart_3901819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901819 prefixEnd_3901819 := by exact prefixLift 3901819
  have htrace : WordTrace (prefixWord ++ tailWord_3901819) baseStart_3901819 baseEnd_3901819 := by
    simpa [prefixWord, tailWord_3901819, baseEnd_3901819] using wordTrace_append hprefix tailTrace_3901819
  have hstable : (prefixWord ++ tailWord_3901819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901819).length < 2 ^ (prefixWord ++ tailWord_3901819).sum := by decide
  have hdescent : baseEnd_3901819 < baseStart_3901819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
