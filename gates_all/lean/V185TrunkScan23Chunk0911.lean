import V185TrunkScan23Chunk0910

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5392508 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_5392508 : Nat := 118140960795 + 5392508 * 2 ^ 59
def prefixEnd_5392508 : Nat := 4983230072969 + 3 ^ 40 * 5392508 * 2
def baseEnd_5392508 : Nat := 2768948537215493021350313

theorem tailTrace_5392508 : CollatzResearch.WordTrace tailWord_5392508 prefixEnd_5392508 2768948537215493021350313 := by
  unfold tailWord_5392508
  simp only [CollatzResearch.WordTrace]
  refine ⟨98340462373935978944789089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131120616498581305259718785 98340462373935978944789089)
  ·
    refine ⟨73755346780451984208591817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98340462373935978944789089 73755346780451984208591817)
    ·
      refine ⟨55316510085338988156443863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73755346780451984208591817 55316510085338988156443863)
      ·
        refine ⟨82974765128008482234665795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55316510085338988156443863 82974765128008482234665795)
        ·
          refine ⟨124462147692012723351998693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82974765128008482234665795 124462147692012723351998693)
          ·
            refine ⟨23336652692252385628499755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124462147692012723351998693 23336652692252385628499755)
            ·
              refine ⟨35004979038378578442749633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23336652692252385628499755 35004979038378578442749633)
              ·
                refine ⟨26253734278783933832062225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35004979038378578442749633 26253734278783933832062225)
                ·
                  refine ⟨19690300709087950374046669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26253734278783933832062225 19690300709087950374046669)
                  ·
                    refine ⟨7383862765907981390267501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19690300709087950374046669 7383862765907981390267501)
                    ·
                      refine ⟨2768948537215493021350313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7383862765907981390267501 2768948537215493021350313)
                      ·
                        rfl

theorem cell23_5392508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_5392508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392508 prefixEnd_5392508 := by exact prefixLift 5392508
  have htrace : WordTrace (prefixWord ++ tailWord_5392508) baseStart_5392508 baseEnd_5392508 := by
    simpa [prefixWord, tailWord_5392508, baseEnd_5392508] using wordTrace_append hprefix tailTrace_5392508
  have hstable : (prefixWord ++ tailWord_5392508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392508).length < 2 ^ (prefixWord ++ tailWord_5392508).sum := by decide
  have hdescent : baseEnd_5392508 < baseStart_5392508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392509 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_5392509 : Nat := 118140960795 + 5392509 * 2 ^ 59
def prefixEnd_5392509 : Nat := 4983230072969 + 3 ^ 40 * 5392509 * 2
def baseEnd_5392509 : Nat := 2768949050696147517437809

theorem tailTrace_5392509 : CollatzResearch.WordTrace tailWord_5392509 prefixEnd_5392509 2768949050696147517437809 := by
  unfold tailWord_5392509
  simp only [CollatzResearch.WordTrace]
  refine ⟨196680961220868335060364581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131120640813912223373576387 196680961220868335060364581)
  ·
    refine ⟨36877680228912812823818359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196680961220868335060364581 36877680228912812823818359)
    ·
      refine ⟨55316520343369219235727539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36877680228912812823818359 55316520343369219235727539)
      ·
        refine ⟨82974780515053828853591309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55316520343369219235727539 82974780515053828853591309)
        ·
          refine ⟨31115542693145185820096741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82974780515053828853591309 31115542693145185820096741)
          ·
            refine ⟨5834164254964722341268139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31115542693145185820096741 5834164254964722341268139)
            ·
              refine ⟨8751246382447083511902209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834164254964722341268139 8751246382447083511902209)
              ·
                refine ⟨6563434786835312633926657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8751246382447083511902209 6563434786835312633926657)
                ·
                  refine ⟨4922576090126484475444993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563434786835312633926657 4922576090126484475444993)
                  ·
                    refine ⟨3691932067594863356583745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922576090126484475444993 3691932067594863356583745)
                    ·
                      refine ⟨2768949050696147517437809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691932067594863356583745 2768949050696147517437809)
                      ·
                        rfl

theorem cell23_5392509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_5392509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392509 prefixEnd_5392509 := by exact prefixLift 5392509
  have htrace : WordTrace (prefixWord ++ tailWord_5392509) baseStart_5392509 baseEnd_5392509 := by
    simpa [prefixWord, tailWord_5392509, baseEnd_5392509] using wordTrace_append hprefix tailTrace_5392509
  have hstable : (prefixWord ++ tailWord_5392509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392509).length < 2 ^ (prefixWord ++ tailWord_5392509).sum := by decide
  have hdescent : baseEnd_5392509 < baseStart_5392509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392521 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_5392521 : Nat := 118140960795 + 5392521 * 2 ^ 59
def prefixEnd_5392521 : Nat := 4983230072969 + 3 ^ 40 * 5392521 * 2
def baseEnd_5392521 : Nat := 2768955212464001470487753

theorem tailTrace_5392521 : CollatzResearch.WordTrace tailWord_5392521 prefixEnd_5392521 2768955212464001470487753 := by
  unfold tailWord_5392521
  simp only [CollatzResearch.WordTrace]
  refine ⟨196681398896824861109801417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131120932597883240739867611 196681398896824861109801417)
  ·
    refine ⟨147511049172618645832351063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196681398896824861109801417 147511049172618645832351063)
    ·
      refine ⟨221266573758927968748526595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147511049172618645832351063 221266573758927968748526595)
      ·
        refine ⟨331899860638391953122789893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221266573758927968748526595 331899860638391953122789893)
        ·
          refine ⟨62231223869698491210523105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331899860638391953122789893 62231223869698491210523105)
          ·
            refine ⟨46673417902273868407892329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62231223869698491210523105 46673417902273868407892329)
            ·
              refine ⟨35005063426705401305919247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46673417902273868407892329 35005063426705401305919247)
              ·
                refine ⟨52507595140058101958878871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35005063426705401305919247 52507595140058101958878871)
                ·
                  refine ⟨78761392710087152938318307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52507595140058101958878871 78761392710087152938318307)
                  ·
                    refine ⟨118142089065130729407477461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78761392710087152938318307 118142089065130729407477461)
                    ·
                      refine ⟨2768955212464001470487753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118142089065130729407477461 2768955212464001470487753)
                      ·
                        rfl

theorem cell23_5392521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_5392521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392521 prefixEnd_5392521 := by exact prefixLift 5392521
  have htrace : WordTrace (prefixWord ++ tailWord_5392521) baseStart_5392521 baseEnd_5392521 := by
    simpa [prefixWord, tailWord_5392521, baseEnd_5392521] using wordTrace_append hprefix tailTrace_5392521
  have hstable : (prefixWord ++ tailWord_5392521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392521).length < 2 ^ (prefixWord ++ tailWord_5392521).sum := by decide
  have hdescent : baseEnd_5392521 < baseStart_5392521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392526 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5392526 : Nat := 118140960795 + 5392526 * 2 ^ 59
def prefixEnd_5392526 : Nat := 4983230072969 + 3 ^ 40 * 5392526 * 2
def baseEnd_5392526 : Nat := 2768957779867273950925231

theorem tailTrace_5392526 : CollatzResearch.WordTrace tailWord_5392526 prefixEnd_5392526 2768957779867273950925231 := by
  unfold tailWord_5392526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24585197657725843370466679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131121054174537831309155621 24585197657725843370466679)
  ·
    refine ⟨36877796486588765055700019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24585197657725843370466679 36877796486588765055700019)
    ·
      refine ⟨55316694729883147583550029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36877796486588765055700019 55316694729883147583550029)
      ·
        refine ⟨20743760523706180343831261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55316694729883147583550029 20743760523706180343831261)
        ·
          refine ⟨7778910196389817628936723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20743760523706180343831261 7778910196389817628936723)
          ·
            refine ⟨11668365294584726443405085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778910196389817628936723 11668365294584726443405085)
            ·
              refine ⟨4375636985469272416276907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11668365294584726443405085 4375636985469272416276907)
              ·
                refine ⟨6563455478203908624415361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375636985469272416276907 6563455478203908624415361)
                ·
                  refine ⟨4922591608652931468311521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563455478203908624415361 4922591608652931468311521)
                  ·
                    refine ⟨3691943706489698601233641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4922591608652931468311521 3691943706489698601233641)
                    ·
                      refine ⟨2768957779867273950925231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3691943706489698601233641 2768957779867273950925231)
                      ·
                        rfl

theorem cell23_5392526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5392526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392526 prefixEnd_5392526 := by exact prefixLift 5392526
  have htrace : WordTrace (prefixWord ++ tailWord_5392526) baseStart_5392526 baseEnd_5392526 := by
    simpa [prefixWord, tailWord_5392526, baseEnd_5392526] using wordTrace_append hprefix tailTrace_5392526
  have hstable : (prefixWord ++ tailWord_5392526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392526).length < 2 ^ (prefixWord ++ tailWord_5392526).sum := by decide
  have hdescent : baseEnd_5392526 < baseStart_5392526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392571 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 8]
def baseStart_5392571 : Nat := 118140960795 + 5392571 * 2 ^ 59
def prefixEnd_5392571 : Nat := 4983230072969 + 3 ^ 40 * 5392571 * 2
def baseEnd_5392571 : Nat := 307664542944080697206947

theorem tailTrace_5392571 : CollatzResearch.WordTrace tailWord_5392571 prefixEnd_5392571 307664542944080697206947 := by
  unfold tailWord_5392571
  simp only [CollatzResearch.WordTrace]
  refine ⟨196683222546643719649121567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131122148364429146432747711 196683222546643719649121567)
  ·
    refine ⟨295024833819965579473682351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196683222546643719649121567 295024833819965579473682351)
    ·
      refine ⟨442537250729948369210523527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295024833819965579473682351 442537250729948369210523527)
      ·
        refine ⟨663805876094922553815785291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442537250729948369210523527 663805876094922553815785291)
        ·
          refine ⟨995708814142383830723677937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663805876094922553815785291 995708814142383830723677937)
          ·
            refine ⟨746781610606787873042758453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995708814142383830723677937 746781610606787873042758453)
            ·
              refine ⟨70010775994386363097758605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 746781610606787873042758453 70010775994386363097758605)
              ·
                refine ⟨26254040997894886161659477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70010775994386363097758605 26254040997894886161659477)
                ·
                  refine ⟨307664542944080697206947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26254040997894886161659477 307664542944080697206947)
                  ·
                    rfl

theorem cell23_5392571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_5392571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392571 prefixEnd_5392571 := by exact prefixLift 5392571
  have htrace : WordTrace (prefixWord ++ tailWord_5392571) baseStart_5392571 baseEnd_5392571 := by
    simpa [prefixWord, tailWord_5392571, baseEnd_5392571] using wordTrace_append hprefix tailTrace_5392571
  have hstable : (prefixWord ++ tailWord_5392571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392571).length < 2 ^ (prefixWord ++ tailWord_5392571).sum := by decide
  have hdescent : baseEnd_5392571 < baseStart_5392571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392626 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_5392626 : Nat := 118140960795 + 5392626 * 2 ^ 59
def prefixEnd_5392626 : Nat := 4983230072969 + 3 ^ 40 * 5392626 * 2
def baseEnd_5392626 : Nat := 923003042644241186558257

theorem tailTrace_5392626 : CollatzResearch.WordTrace tailWord_5392626 prefixEnd_5392626 923003042644241186558257 := by
  unfold tailWord_5392626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49171307140361116010593433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131123485707629642694915821 49171307140361116010593433)
  ·
    refine ⟨36878480355270837007945075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49171307140361116010593433 36878480355270837007945075)
    ·
      refine ⟨55317720532906255511917613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36878480355270837007945075 55317720532906255511917613)
      ·
        refine ⟨20744145199839845816969105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55317720532906255511917613 20744145199839845816969105)
        ·
          refine ⟨15558108899879884362726829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20744145199839845816969105 15558108899879884362726829)
          ·
            refine ⟨5834290837454956636022561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15558108899879884362726829 5834290837454956636022561)
            ·
              refine ⟨4375718128091217477016921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834290837454956636022561 4375718128091217477016921)
              ·
                refine ⟨3281788596068413107762691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375718128091217477016921 3281788596068413107762691)
                ·
                  refine ⟨4922682894102619661644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281788596068413107762691 4922682894102619661644037)
                  ·
                    refine ⟨923003042644241186558257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922682894102619661644037 923003042644241186558257)
                    ·
                      rfl

theorem cell23_5392626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_5392626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392626 prefixEnd_5392626 := by exact prefixLift 5392626
  have htrace : WordTrace (prefixWord ++ tailWord_5392626) baseStart_5392626 baseEnd_5392626 := by
    simpa [prefixWord, tailWord_5392626, baseEnd_5392626] using wordTrace_append hprefix tailTrace_5392626
  have hstable : (prefixWord ++ tailWord_5392626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392626).length < 2 ^ (prefixWord ++ tailWord_5392626).sum := by decide
  have hdescent : baseEnd_5392626 < baseStart_5392626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392666 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3]
def baseStart_5392666 : Nat := 118140960795 + 5392666 * 2 ^ 59
def prefixEnd_5392666 : Nat := 4983230072969 + 3 ^ 40 * 5392666 * 2
def baseEnd_5392666 : Nat := 2769029667158903403174587

theorem tailTrace_5392666 : CollatzResearch.WordTrace tailWord_5392666 prefixEnd_5392666 2769029667158903403174587 := by
  unfold tailWord_5392666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49171671870324887718457463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131124458320866367249219901 49171671870324887718457463)
  ·
    refine ⟨73757507805487331577686195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49171671870324887718457463 73757507805487331577686195)
    ·
      refine ⟨110636261708230997366529293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73757507805487331577686195 110636261708230997366529293)
      ·
        refine ⟨41488598140586624012448485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110636261708230997366529293 41488598140586624012448485)
        ·
          refine ⟨7779112151359992002334091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41488598140586624012448485 7779112151359992002334091)
          ·
            refine ⟨11668668227039988003501137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779112151359992002334091 11668668227039988003501137)
            ·
              refine ⟨8751501170279991002625853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11668668227039988003501137 8751501170279991002625853)
              ·
                refine ⟨3281812938854996625984695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8751501170279991002625853 3281812938854996625984695)
                ·
                  refine ⟨4922719408282494938977043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281812938854996625984695 4922719408282494938977043)
                  ·
                    refine ⟨7384079112423742408465565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922719408282494938977043 7384079112423742408465565)
                    ·
                      refine ⟨2769029667158903403174587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384079112423742408465565 2769029667158903403174587)
                      ·
                        rfl

theorem cell23_5392666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_5392666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392666 prefixEnd_5392666 := by exact prefixLift 5392666
  have htrace : WordTrace (prefixWord ++ tailWord_5392666) baseStart_5392666 baseEnd_5392666 := by
    simpa [prefixWord, tailWord_5392666, baseEnd_5392666] using wordTrace_append hprefix tailTrace_5392666
  have hstable : (prefixWord ++ tailWord_5392666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392666).length < 2 ^ (prefixWord ++ tailWord_5392666).sum := by decide
  have hdescent : baseEnd_5392666 < baseStart_5392666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392668 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5392668 : Nat := 118140960795 + 5392668 * 2 ^ 59
def prefixEnd_5392668 : Nat := 4983230072969 + 3 ^ 40 * 5392668 * 2
def baseEnd_5392668 : Nat := 2769030694120212395349577

theorem tailTrace_5392668 : CollatzResearch.WordTrace tailWord_5392668 prefixEnd_5392668 2769030694120212395349577 := by
  unfold tailWord_5392668
  simp only [CollatzResearch.WordTrace]
  refine ⟨98343380213646152607701329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131124506951528203476935105 98343380213646152607701329)
  ·
    refine ⟨73757535160234614455775997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98343380213646152607701329 73757535160234614455775997)
    ·
      refine ⟨27659075685087980420915999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73757535160234614455775997 27659075685087980420915999)
      ·
        refine ⟨41488613527631970631373999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27659075685087980420915999 41488613527631970631373999)
        ·
          refine ⟨62232920291447955947060999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41488613527631970631373999 62232920291447955947060999)
          ·
            refine ⟨93349380437171933920591499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62232920291447955947060999 93349380437171933920591499)
            ·
              refine ⟨140024070655757900880887249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93349380437171933920591499 140024070655757900880887249)
              ·
                refine ⟨105018052991818425660665437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140024070655757900880887249 105018052991818425660665437)
                ·
                  refine ⟨39381769871931909622749539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105018052991818425660665437 39381769871931909622749539)
                  ·
                    refine ⟨59072654807897864434124309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39381769871931909622749539 59072654807897864434124309)
                    ·
                      refine ⟨2769030694120212395349577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59072654807897864434124309 2769030694120212395349577)
                      ·
                        rfl

theorem cell23_5392668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5392668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392668 prefixEnd_5392668 := by exact prefixLift 5392668
  have htrace : WordTrace (prefixWord ++ tailWord_5392668) baseStart_5392668 baseEnd_5392668 := by
    simpa [prefixWord, tailWord_5392668, baseEnd_5392668] using wordTrace_append hprefix tailTrace_5392668
  have hstable : (prefixWord ++ tailWord_5392668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392668).length < 2 ^ (prefixWord ++ tailWord_5392668).sum := by decide
  have hdescent : baseEnd_5392668 < baseStart_5392668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392672 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5392672 : Nat := 118140960795 + 5392672 * 2 ^ 59
def prefixEnd_5392672 : Nat := 4983230072969 + 3 ^ 40 * 5392672 * 2
def baseEnd_5392672 : Nat := 2769032748042830379699559

theorem tailTrace_5392672 : CollatzResearch.WordTrace tailWord_5392672 prefixEnd_5392672 2769032748042830379699559 := by
  unfold tailWord_5392672
  simp only [CollatzResearch.WordTrace]
  refine ⟨98343453159638906949274135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131124604212851875932365513 98343453159638906949274135)
  ·
    refine ⟨147515179739458360423911203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98343453159638906949274135 147515179739458360423911203)
    ·
      refine ⟨221272769609187540635866805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147515179739458360423911203 221272769609187540635866805)
      ·
        refine ⟨20744322150861331934612513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221272769609187540635866805 20744322150861331934612513)
        ·
          refine ⟨15558241613145998950959385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20744322150861331934612513 15558241613145998950959385)
          ·
            refine ⟨11668681209859499213219539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15558241613145998950959385 11668681209859499213219539)
            ·
              refine ⟨17503021814789248819829309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11668681209859499213219539 17503021814789248819829309)
              ·
                refine ⟨6563633180545968307435991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17503021814789248819829309 6563633180545968307435991)
                ·
                  refine ⟨9845449770818952461153987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6563633180545968307435991 9845449770818952461153987)
                  ·
                    refine ⟨14768174656228428691730981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9845449770818952461153987 14768174656228428691730981)
                    ·
                      refine ⟨2769032748042830379699559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14768174656228428691730981 2769032748042830379699559)
                      ·
                        rfl

theorem cell23_5392672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5392672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392672 prefixEnd_5392672 := by exact prefixLift 5392672
  have htrace : WordTrace (prefixWord ++ tailWord_5392672) baseStart_5392672 baseEnd_5392672 := by
    simpa [prefixWord, tailWord_5392672, baseEnd_5392672] using wordTrace_append hprefix tailTrace_5392672
  have hstable : (prefixWord ++ tailWord_5392672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392672).length < 2 ^ (prefixWord ++ tailWord_5392672).sum := by decide
  have hdescent : baseEnd_5392672 < baseStart_5392672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392692 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5392692 : Nat := 118140960795 + 5392692 * 2 ^ 59
def prefixEnd_5392692 : Nat := 4983230072969 + 3 ^ 40 * 5392692 * 2
def baseEnd_5392692 : Nat := 2769043017655920301449467

theorem tailTrace_5392692 : CollatzResearch.WordTrace tailWord_5392692 prefixEnd_5392692 2769043017655920301449467 := by
  unfold tailWord_5392692
  simp only [CollatzResearch.WordTrace]
  refine ⟨98343817889602678657138165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131125090519470238209517553 98343817889602678657138165)
  ·
    refine ⟨9219732927150251124106703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98343817889602678657138165 9219732927150251124106703)
    ·
      refine ⟨13829599390725376686160055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219732927150251124106703 13829599390725376686160055)
      ·
        refine ⟨20744399086088065029240083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829599390725376686160055 20744399086088065029240083)
        ·
          refine ⟨31116598629132097543860125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20744399086088065029240083 31116598629132097543860125)
          ·
            refine ⟨11668724485924536578947547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31116598629132097543860125 11668724485924536578947547)
            ·
              refine ⟨17503086728886804868421321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11668724485924536578947547 17503086728886804868421321)
              ·
                refine ⟨13127315046665103651315991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17503086728886804868421321 13127315046665103651315991)
                ·
                  refine ⟨19690972569997655476973987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13127315046665103651315991 19690972569997655476973987)
                  ·
                    refine ⟨29536458854996483215460981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19690972569997655476973987 29536458854996483215460981)
                    ·
                      refine ⟨2769043017655920301449467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29536458854996483215460981 2769043017655920301449467)
                      ·
                        rfl

theorem cell23_5392692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5392692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392692 prefixEnd_5392692 := by exact prefixLift 5392692
  have htrace : WordTrace (prefixWord ++ tailWord_5392692) baseStart_5392692 baseEnd_5392692 := by
    simpa [prefixWord, tailWord_5392692, baseEnd_5392692] using wordTrace_append hprefix tailTrace_5392692
  have hstable : (prefixWord ++ tailWord_5392692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392692).length < 2 ^ (prefixWord ++ tailWord_5392692).sum := by decide
  have hdescent : baseEnd_5392692 < baseStart_5392692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392702 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_5392702 : Nat := 118140960795 + 5392702 * 2 ^ 59
def prefixEnd_5392702 : Nat := 4983230072969 + 3 ^ 40 * 5392702 * 2
def baseEnd_5392702 : Nat := 2769048152462465262324421

theorem tailTrace_5392702 : CollatzResearch.WordTrace tailWord_5392702 prefixEnd_5392702 2769048152462465262324421 := by
  unfold tailWord_5392702
  simp only [CollatzResearch.WordTrace]
  refine ⟨24586000063646141127767545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131125333672779419348093573 24586000063646141127767545)
  ·
    refine ⟨18439500047734605845825659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24586000063646141127767545 18439500047734605845825659)
    ·
      refine ⟨27659250071601908768738489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18439500047734605845825659 27659250071601908768738489)
      ·
        refine ⟨20744437553701431576553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27659250071601908768738489 20744437553701431576553867)
        ·
          refine ⟨31116656330552147364830801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20744437553701431576553867 31116656330552147364830801)
          ·
            refine ⟨23337492247914110523623101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31116656330552147364830801 23337492247914110523623101)
            ·
              refine ⟨8751559592967791446358663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23337492247914110523623101 8751559592967791446358663)
              ·
                refine ⟨13127339389451687169537995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8751559592967791446358663 13127339389451687169537995)
                ·
                  refine ⟨19691009084177530754306993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13127339389451687169537995 19691009084177530754306993)
                  ·
                    refine ⟨14768256813133148065730245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19691009084177530754306993 14768256813133148065730245)
                    ·
                      refine ⟨2769048152462465262324421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14768256813133148065730245 2769048152462465262324421)
                      ·
                        rfl

theorem cell23_5392702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_5392702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392702 prefixEnd_5392702 := by exact prefixLift 5392702
  have htrace : WordTrace (prefixWord ++ tailWord_5392702) baseStart_5392702 baseEnd_5392702 := by
    simpa [prefixWord, tailWord_5392702, baseEnd_5392702] using wordTrace_append hprefix tailTrace_5392702
  have hstable : (prefixWord ++ tailWord_5392702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392702).length < 2 ^ (prefixWord ++ tailWord_5392702).sum := by decide
  have hdescent : baseEnd_5392702 < baseStart_5392702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392722 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_5392722 : Nat := 118140960795 + 5392722 * 2 ^ 59
def prefixEnd_5392722 : Nat := 4983230072969 + 3 ^ 40 * 5392722 * 2
def baseEnd_5392722 : Nat := 2769058422075555184074329

theorem tailTrace_5392722 : CollatzResearch.WordTrace tailWord_5392722 prefixEnd_5392722 2769058422075555184074329 := by
  unfold tailWord_5392722
  simp only [CollatzResearch.WordTrace]
  refine ⟨49172182492274168109467105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131125819979397781625245613 49172182492274168109467105)
  ·
    refine ⟨36879136869205626082100329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49172182492274168109467105 36879136869205626082100329)
    ·
      refine ⟨27659352651904219561575247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36879136869205626082100329 27659352651904219561575247)
      ·
        refine ⟨41489028977856329342362871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27659352651904219561575247 41489028977856329342362871)
        ·
          refine ⟨62233543466784494013544307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41489028977856329342362871 62233543466784494013544307)
          ·
            refine ⟨93350315200176741020316461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62233543466784494013544307 93350315200176741020316461)
            ·
              refine ⟨35006368200066277882618673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93350315200176741020316461 35006368200066277882618673)
              ·
                refine ⟨26254776150049708411964005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35006368200066277882618673 26254776150049708411964005)
                ·
                  refine ⟨4922770528134320327243251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26254776150049708411964005 4922770528134320327243251)
                  ·
                    refine ⟨7384155792201480490864877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922770528134320327243251 7384155792201480490864877)
                    ·
                      refine ⟨2769058422075555184074329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384155792201480490864877 2769058422075555184074329)
                      ·
                        rfl

theorem cell23_5392722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_5392722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392722 prefixEnd_5392722 := by exact prefixLift 5392722
  have htrace : WordTrace (prefixWord ++ tailWord_5392722) baseStart_5392722 baseEnd_5392722 := by
    simpa [prefixWord, tailWord_5392722, baseEnd_5392722] using wordTrace_append hprefix tailTrace_5392722
  have hstable : (prefixWord ++ tailWord_5392722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392722).length < 2 ^ (prefixWord ++ tailWord_5392722).sum := by decide
  have hdescent : baseEnd_5392722 < baseStart_5392722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392734 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5392734 : Nat := 118140960795 + 5392734 * 2 ^ 59
def prefixEnd_5392734 : Nat := 4983230072969 + 3 ^ 40 * 5392734 * 2
def baseEnd_5392734 : Nat := 2769064583843409137124275

theorem tailTrace_5392734 : CollatzResearch.WordTrace tailWord_5392734 prefixEnd_5392734 2769064583843409137124275 := by
  unfold tailWord_5392734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24586145955631649810913157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131126111763368798991536837 24586145955631649810913157)
  ·
    refine ⟨4609902366680934339546217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24586145955631649810913157 4609902366680934339546217)
    ·
      refine ⟨3457426775010700754659663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4609902366680934339546217 3457426775010700754659663)
      ·
        refine ⟨5186140162516051131989495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457426775010700754659663 5186140162516051131989495)
        ·
          refine ⟨7779210243774076697984243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186140162516051131989495 7779210243774076697984243)
          ·
            refine ⟨11668815365661115046976365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779210243774076697984243 11668815365661115046976365)
            ·
              refine ⟨4375805762122918142616137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11668815365661115046976365 4375805762122918142616137)
              ·
                refine ⟨3281854321592188606962103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375805762122918142616137 3281854321592188606962103)
                ·
                  refine ⟨4922781482388282910443155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281854321592188606962103 4922781482388282910443155)
                  ·
                    refine ⟨7384172223582424365664733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922781482388282910443155 7384172223582424365664733)
                    ·
                      refine ⟨2769064583843409137124275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384172223582424365664733 2769064583843409137124275)
                      ·
                        rfl

theorem cell23_5392734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5392734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392734 prefixEnd_5392734 := by exact prefixLift 5392734
  have htrace : WordTrace (prefixWord ++ tailWord_5392734) baseStart_5392734 baseEnd_5392734 := by
    simpa [prefixWord, tailWord_5392734, baseEnd_5392734] using wordTrace_append hprefix tailTrace_5392734
  have hstable : (prefixWord ++ tailWord_5392734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392734).length < 2 ^ (prefixWord ++ tailWord_5392734).sum := by decide
  have hdescent : baseEnd_5392734 < baseStart_5392734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392765 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_5392765 : Nat := 118140960795 + 5392765 * 2 ^ 59
def prefixEnd_5392765 : Nat := 4983230072969 + 3 ^ 40 * 5392765 * 2
def baseEnd_5392765 : Nat := 2769080501743698515836631

theorem tailTrace_5392765 : CollatzResearch.WordTrace tailWord_5392765 prefixEnd_5392765 2769080501743698515836631 := by
  unfold tailWord_5392765
  simp only [CollatzResearch.WordTrace]
  refine ⟨196690298307940890781683749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131126865538627260521122499 196690298307940890781683749)
  ·
    refine ⟨36879430932738917021565703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196690298307940890781683749 36879430932738917021565703)
    ·
      refine ⟨55319146399108375532348555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36879430932738917021565703 55319146399108375532348555)
      ·
        refine ⟨82978719598662563298522833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55319146399108375532348555 82978719598662563298522833)
        ·
          refine ⟨62234039698996922473892125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82978719598662563298522833 62234039698996922473892125)
          ·
            refine ⟨23337764887123845927709547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62234039698996922473892125 23337764887123845927709547)
            ·
              refine ⟨35006647330685768891564321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23337764887123845927709547 35006647330685768891564321)
              ·
                refine ⟨26254985498014326668673241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35006647330685768891564321 26254985498014326668673241)
                ·
                  refine ⟨19691239123510745001504931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26254985498014326668673241 19691239123510745001504931)
                  ·
                    refine ⟨29536858685266117502257397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19691239123510745001504931 29536858685266117502257397)
                    ·
                      refine ⟨2769080501743698515836631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29536858685266117502257397 2769080501743698515836631)
                      ·
                        rfl

theorem cell23_5392765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_5392765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392765 prefixEnd_5392765 := by exact prefixLift 5392765
  have htrace : WordTrace (prefixWord ++ tailWord_5392765) baseStart_5392765 baseEnd_5392765 := by
    simpa [prefixWord, tailWord_5392765, baseEnd_5392765] using wordTrace_append hprefix tailTrace_5392765
  have hstable : (prefixWord ++ tailWord_5392765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392765).length < 2 ^ (prefixWord ++ tailWord_5392765).sum := by decide
  have hdescent : baseEnd_5392765 < baseStart_5392765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392782 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5392782 : Nat := 118140960795 + 5392782 * 2 ^ 59
def prefixEnd_5392782 : Nat := 4983230072969 + 3 ^ 40 * 5392782 * 2
def baseEnd_5392782 : Nat := 2769089230914824949324053

theorem tailTrace_5392782 : CollatzResearch.WordTrace tailWord_5392782 prefixEnd_5392782 2769089230914824949324053 := by
  unfold tailWord_5392782
  simp only [CollatzResearch.WordTrace]
  refine ⟨24586364793609912835631575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131127278899252868456701733 24586364793609912835631575)
  ·
    refine ⟨36879547190414869253447363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24586364793609912835631575 36879547190414869253447363)
    ·
      refine ⟨55319320785622303880171045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36879547190414869253447363 55319320785622303880171045)
      ·
        refine ⟨10372372647304181977532071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55319320785622303880171045 10372372647304181977532071)
        ·
          refine ⟨15558558970956272966298107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372372647304181977532071 15558558970956272966298107)
          ·
            refine ⟨23337838456434409449447161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15558558970956272966298107 23337838456434409449447161)
            ·
              refine ⟨17503378842325807087085371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23337838456434409449447161 17503378842325807087085371)
              ·
                refine ⟨26255068263488710630628057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17503378842325807087085371 26255068263488710630628057)
                ·
                  refine ⟨19691301197616532972971043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26255068263488710630628057 19691301197616532972971043)
                  ·
                    refine ⟨29536951796424799459456565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19691301197616532972971043 29536951796424799459456565)
                    ·
                      refine ⟨2769089230914824949324053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29536951796424799459456565 2769089230914824949324053)
                      ·
                        rfl

theorem cell23_5392782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5392782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392782 prefixEnd_5392782 := by exact prefixLift 5392782
  have htrace : WordTrace (prefixWord ++ tailWord_5392782) baseStart_5392782 baseEnd_5392782 := by
    simpa [prefixWord, tailWord_5392782, baseEnd_5392782] using wordTrace_append hprefix tailTrace_5392782
  have hstable : (prefixWord ++ tailWord_5392782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392782).length < 2 ^ (prefixWord ++ tailWord_5392782).sum := by decide
  have hdescent : baseEnd_5392782 < baseStart_5392782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392836 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 5]
def baseStart_5392836 : Nat := 118140960795 + 5392836 * 2 ^ 59
def prefixEnd_5392836 : Nat := 4983230072969 + 3 ^ 40 * 5392836 * 2
def baseEnd_5392836 : Nat := 307679662096685304227645

theorem tailTrace_5392836 : CollatzResearch.WordTrace tailWord_5392836 prefixEnd_5392836 307679662096685304227645 := by
  unfold tailWord_5392836
  simp only [CollatzResearch.WordTrace]
  refine ⟨98346443945341834953759181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131128591927122446605012241 98346443945341834953759181)
  ·
    refine ⟨36879916479503188107659693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98346443945341834953759181 36879916479503188107659693)
    ·
      refine ⟨13829968679813695540372385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36879916479503188107659693 13829968679813695540372385)
      ·
        refine ⟨10372476509860271655279289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13829968679813695540372385 10372476509860271655279289)
        ·
          refine ⟨7779357382395203741459467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10372476509860271655279289 7779357382395203741459467)
          ·
            refine ⟨11669036073592805612189201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779357382395203741459467 11669036073592805612189201)
            ·
              refine ⟨8751777055194604209141901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11669036073592805612189201 8751777055194604209141901)
              ·
                refine ⟨3281916395697976578428213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8751777055194604209141901 3281916395697976578428213)
                ·
                  refine ⟨307679662096685304227645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3281916395697976578428213 307679662096685304227645)
                  ·
                    rfl

theorem cell23_5392836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_5392836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392836 prefixEnd_5392836 := by exact prefixLift 5392836
  have htrace : WordTrace (prefixWord ++ tailWord_5392836) baseStart_5392836 baseEnd_5392836 := by
    simpa [prefixWord, tailWord_5392836, baseEnd_5392836] using wordTrace_append hprefix tailTrace_5392836
  have hstable : (prefixWord ++ tailWord_5392836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392836).length < 2 ^ (prefixWord ++ tailWord_5392836).sum := by decide
  have hdescent : baseEnd_5392836 < baseStart_5392836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392865 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_5392865 : Nat := 118140960795 + 5392865 * 2 ^ 59
def prefixEnd_5392865 : Nat := 4983230072969 + 3 ^ 40 * 5392865 * 2
def baseEnd_5392865 : Nat := 2769131849809148124586171

theorem tailTrace_5392865 : CollatzResearch.WordTrace tailWord_5392865 prefixEnd_5392865 2769131849809148124586171 := by
  unfold tailWord_5392865
  simp only [CollatzResearch.WordTrace]
  refine ⟨196693945607578607860324049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131129297071719071906882699 196693945607578607860324049)
  ·
    refine ⟨147520459205683955895243037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196693945607578607860324049 147520459205683955895243037)
    ·
      refine ⟨55320172202131483460716139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147520459205683955895243037 55320172202131483460716139)
      ·
        refine ⟨82980258303197225191074209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55320172202131483460716139 82980258303197225191074209)
        ·
          refine ⟨62235193727397918893305657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82980258303197225191074209 62235193727397918893305657)
          ·
            refine ⟨46676395295548439169979243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62235193727397918893305657 46676395295548439169979243)
            ·
              refine ⟨70014592943322658754968865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46676395295548439169979243 70014592943322658754968865)
              ·
                refine ⟨52510944707491994066226649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70014592943322658754968865 52510944707491994066226649)
                ·
                  refine ⟨39383208530618995549669987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52510944707491994066226649 39383208530618995549669987)
                  ·
                    refine ⟨59074812795928493324504981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39383208530618995549669987 59074812795928493324504981)
                    ·
                      refine ⟨2769131849809148124586171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59074812795928493324504981 2769131849809148124586171)
                      ·
                        rfl

theorem cell23_5392865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_5392865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392865 prefixEnd_5392865 := by exact prefixLift 5392865
  have htrace : WordTrace (prefixWord ++ tailWord_5392865) baseStart_5392865 baseEnd_5392865 := by
    simpa [prefixWord, tailWord_5392865, baseEnd_5392865] using wordTrace_append hprefix tailTrace_5392865
  have hstable : (prefixWord ++ tailWord_5392865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392865).length < 2 ^ (prefixWord ++ tailWord_5392865).sum := by decide
  have hdescent : baseEnd_5392865 < baseStart_5392865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392872 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5392872 : Nat := 118140960795 + 5392872 * 2 ^ 59
def prefixEnd_5392872 : Nat := 4983230072969 + 3 ^ 40 * 5392872 * 2
def baseEnd_5392872 : Nat := 2769135444173729597198639

theorem tailTrace_5392872 : CollatzResearch.WordTrace tailWord_5392872 prefixEnd_5392872 2769135444173729597198639 := by
  unfold tailWord_5392872
  simp only [CollatzResearch.WordTrace]
  refine ⟨98347100459276624027914435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131129467279035498703885913 98347100459276624027914435)
  ·
    refine ⟨147520650688914936041871653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98347100459276624027914435 147520650688914936041871653)
    ·
      refine ⟨27660122004171550507850935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147520650688914936041871653 27660122004171550507850935)
      ·
        refine ⟨41490183006257325761776403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27660122004171550507850935 41490183006257325761776403)
        ·
          refine ⟨62235274509385988642664605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41490183006257325761776403 62235274509385988642664605)
          ·
            refine ⟨23338227941019745740999227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62235274509385988642664605 23338227941019745740999227)
            ·
              refine ⟨35007341911529618611498841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23338227941019745740999227 35007341911529618611498841)
              ·
                refine ⟨26255506433647213958624131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35007341911529618611498841 26255506433647213958624131)
                ·
                  refine ⟨39383259650470820937936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26255506433647213958624131 39383259650470820937936197)
                  ·
                    refine ⟨7384361184463278925863037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39383259650470820937936197 7384361184463278925863037)
                    ·
                      refine ⟨2769135444173729597198639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384361184463278925863037 2769135444173729597198639)
                      ·
                        rfl

theorem cell23_5392872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5392872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392872 prefixEnd_5392872 := by exact prefixLift 5392872
  have htrace : WordTrace (prefixWord ++ tailWord_5392872) baseStart_5392872 baseEnd_5392872 := by
    simpa [prefixWord, tailWord_5392872, baseEnd_5392872] using wordTrace_append hprefix tailTrace_5392872
  have hstable : (prefixWord ++ tailWord_5392872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392872).length < 2 ^ (prefixWord ++ tailWord_5392872).sum := by decide
  have hdescent : baseEnd_5392872 < baseStart_5392872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392929 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5392929 : Nat := 118140960795 + 5392929 * 2 ^ 59
def prefixEnd_5392929 : Nat := 4983230072969 + 3 ^ 40 * 5392929 * 2
def baseEnd_5392929 : Nat := 2769164712571035874185877

theorem tailTrace_5392929 : CollatzResearch.WordTrace tailWord_5392929 prefixEnd_5392929 2769164712571035874185877 := by
  unfold tailWord_5392929
  simp only [CollatzResearch.WordTrace]
  refine ⟨196696279879346746790653841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131130853252897831193769227 196696279879346746790653841)
  ·
    refine ⟨147522209909510060092990381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196696279879346746790653841 147522209909510060092990381)
    ·
      refine ⟨55320828716066272534871393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147522209909510060092990381 55320828716066272534871393)
      ·
        refine ⟨41490621537049704401153545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55320828716066272534871393 41490621537049704401153545)
        ·
          refine ⟨31117966152787278300865159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41490621537049704401153545 31117966152787278300865159)
          ·
            refine ⟨46676949229180917451297739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31117966152787278300865159 46676949229180917451297739)
            ·
              refine ⟨70015423843771376176946609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46676949229180917451297739 70015423843771376176946609)
              ·
                refine ⟨52511567882828532132709957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70015423843771376176946609 52511567882828532132709957)
                ·
                  refine ⟨9845918978030349774883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52511567882828532132709957 9845918978030349774883117)
                  ·
                    refine ⟨3692219616761381165581169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9845918978030349774883117 3692219616761381165581169)
                    ·
                      refine ⟨2769164712571035874185877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692219616761381165581169 2769164712571035874185877)
                      ·
                        rfl

theorem cell23_5392929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5392929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392929 prefixEnd_5392929 := by exact prefixLift 5392929
  have htrace : WordTrace (prefixWord ++ tailWord_5392929) baseStart_5392929 baseEnd_5392929 := by
    simpa [prefixWord, tailWord_5392929, baseEnd_5392929] using wordTrace_append hprefix tailTrace_5392929
  have hstable : (prefixWord ++ tailWord_5392929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392929).length < 2 ^ (prefixWord ++ tailWord_5392929).sum := by decide
  have hdescent : baseEnd_5392929 < baseStart_5392929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392952 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_5392952 : Nat := 118140960795 + 5392952 * 2 ^ 59
def prefixEnd_5392952 : Nat := 4983230072969 + 3 ^ 40 * 5392952 * 2
def baseEnd_5392952 : Nat := 923058840875363094732757

theorem tailTrace_5392952 : CollatzResearch.WordTrace tailWord_5392952 prefixEnd_5392952 923058840875363094732757 := by
  unfold tailWord_5392952
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348559379131710859370555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131131412505508947812494073 98348559379131710859370555)
  ·
    refine ⟨147522839068697566289055833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98348559379131710859370555 147522839068697566289055833)
    ·
      refine ⟨110642129301523174716791875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147522839068697566289055833 110642129301523174716791875)
      ·
        refine ⟨165963193952284762075187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110642129301523174716791875 165963193952284762075187813)
        ·
          refine ⟨31118098866053392889097715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165963193952284762075187813 31118098866053392889097715)
          ·
            refine ⟨46677148299080089333646573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31118098866053392889097715 46677148299080089333646573)
            ·
              refine ⟨17503930612155033500117465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46677148299080089333646573 17503930612155033500117465)
              ·
                refine ⟨13127947959116275125088099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17503930612155033500117465 13127947959116275125088099)
                ·
                  refine ⟨19691921938674412687632149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13127947959116275125088099 19691921938674412687632149)
                  ·
                    refine ⟨923058840875363094732757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19691921938674412687632149 923058840875363094732757)
                    ·
                      rfl

theorem cell23_5392952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_5392952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392952 prefixEnd_5392952 := by exact prefixLift 5392952
  have htrace : WordTrace (prefixWord ++ tailWord_5392952) baseStart_5392952 baseEnd_5392952 := by
    simpa [prefixWord, tailWord_5392952, baseEnd_5392952] using wordTrace_append hprefix tailTrace_5392952
  have hstable : (prefixWord ++ tailWord_5392952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392952).length < 2 ^ (prefixWord ++ tailWord_5392952).sum := by decide
  have hdescent : baseEnd_5392952 < baseStart_5392952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392956 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5392956 : Nat := 118140960795 + 5392956 * 2 ^ 59
def prefixEnd_5392956 : Nat := 4983230072969 + 3 ^ 40 * 5392956 * 2
def baseEnd_5392956 : Nat := 923059525516235756182751

theorem tailTrace_5392956 : CollatzResearch.WordTrace tailWord_5392956 prefixEnd_5392956 923059525516235756182751 := by
  unfold tailWord_5392956
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348632325124465200943361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131131509766832620267924481 98348632325124465200943361)
  ·
    refine ⟨73761474243843348900707521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98348632325124465200943361 73761474243843348900707521)
    ·
      refine ⟨55321105682882511675530641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73761474243843348900707521 55321105682882511675530641)
      ·
        refine ⟨41490829262161883756647981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55321105682882511675530641 41490829262161883756647981)
        ·
          refine ⟨15559060973310706408742993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41490829262161883756647981 15559060973310706408742993)
          ·
            refine ⟨11669295729983029806557245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15559060973310706408742993 11669295729983029806557245)
            ·
              refine ⟨4375985898743636177458967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11669295729983029806557245 4375985898743636177458967)
              ·
                refine ⟨6563978848115454266188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4375985898743636177458967 6563978848115454266188451)
                ·
                  refine ⟨9845968272173181399282677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6563978848115454266188451 9845968272173181399282677)
                  ·
                    refine ⟨923059525516235756182751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9845968272173181399282677 923059525516235756182751)
                    ·
                      rfl

theorem cell23_5392956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5392956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392956 prefixEnd_5392956 := by exact prefixLift 5392956
  have htrace : WordTrace (prefixWord ++ tailWord_5392956) baseStart_5392956 baseEnd_5392956 := by
    simpa [prefixWord, tailWord_5392956, baseEnd_5392956] using wordTrace_append hprefix tailTrace_5392956
  have hstable : (prefixWord ++ tailWord_5392956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392956).length < 2 ^ (prefixWord ++ tailWord_5392956).sum := by decide
  have hdescent : baseEnd_5392956 < baseStart_5392956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392964 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5392964 : Nat := 118140960795 + 5392964 * 2 ^ 59
def prefixEnd_5392964 : Nat := 4983230072969 + 3 ^ 40 * 5392964 * 2
def baseEnd_5392964 : Nat := 923060894797981079082739

theorem tailTrace_5392964 : CollatzResearch.WordTrace tailWord_5392964 prefixEnd_5392964 923060894797981079082739 := by
  unfold tailWord_5392964
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348778217109973884088973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131131704289479965178785297 98348778217109973884088973)
  ·
    refine ⟨36880791831416240206533365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98348778217109973884088973 36880791831416240206533365)
    ·
      refine ⟨3457574234195272519362503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36880791831416240206533365 3457574234195272519362503)
      ·
        refine ⟨5186361351292908779043755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457574234195272519362503 5186361351292908779043755)
        ·
          refine ⟨7779542026939363168565633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186361351292908779043755 7779542026939363168565633)
          ·
            refine ⟨5834656520204522376424225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7779542026939363168565633 5834656520204522376424225)
            ·
              refine ⟨4375992390153391782318169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834656520204522376424225 4375992390153391782318169)
              ·
                refine ⟨3281994292615043836738627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375992390153391782318169 3281994292615043836738627)
                ·
                  refine ⟨4922991438922565755107941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281994292615043836738627 4922991438922565755107941)
                  ·
                    refine ⟨923060894797981079082739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4922991438922565755107941 923060894797981079082739)
                    ·
                      rfl

theorem cell23_5392964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5392964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392964 prefixEnd_5392964 := by exact prefixLift 5392964
  have htrace : WordTrace (prefixWord ++ tailWord_5392964) baseStart_5392964 baseEnd_5392964 := by
    simpa [prefixWord, tailWord_5392964, baseEnd_5392964] using wordTrace_append hprefix tailTrace_5392964
  have hstable : (prefixWord ++ tailWord_5392964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392964).length < 2 ^ (prefixWord ++ tailWord_5392964).sum := by decide
  have hdescent : baseEnd_5392964 < baseStart_5392964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392965 : List Nat := [1, 3, 1, 1, 1, 16]
def baseStart_5392965 : Nat := 118140960795 + 5392965 * 2 ^ 59
def prefixEnd_5392965 : Nat := 4983230072969 + 3 ^ 40 * 5392965 * 2
def baseEnd_5392965 : Nat := 11395815629113570919077

theorem tailTrace_5392965 : CollatzResearch.WordTrace tailWord_5392965 prefixEnd_5392965 11395815629113570919077 := by
  unfold tailWord_5392965
  simp only [CollatzResearch.WordTrace]
  refine ⟨196697592907216324938964349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131131728604810883292642899 196697592907216324938964349)
  ·
    refine ⟨73761597340206121852111631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196697592907216324938964349 73761597340206121852111631)
    ·
      refine ⟨110642396010309182778167447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73761597340206121852111631 110642396010309182778167447)
      ·
        refine ⟨165963594015463774167251171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110642396010309182778167447 165963594015463774167251171)
        ·
          refine ⟨248945391023195661250876757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165963594015463774167251171 248945391023195661250876757)
          ·
            refine ⟨11395815629113570919077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 248945391023195661250876757 11395815629113570919077)
            ·
              rfl

theorem cell23_5392965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 16].length) (baseStart_5392965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392965 prefixEnd_5392965 := by exact prefixLift 5392965
  have htrace : WordTrace (prefixWord ++ tailWord_5392965) baseStart_5392965 baseEnd_5392965 := by
    simpa [prefixWord, tailWord_5392965, baseEnd_5392965] using wordTrace_append hprefix tailTrace_5392965
  have hstable : (prefixWord ++ tailWord_5392965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392965).length < 2 ^ (prefixWord ++ tailWord_5392965).sum := by decide
  have hdescent : baseEnd_5392965 < baseStart_5392965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392970 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_5392970 : Nat := 118140960795 + 5392970 * 2 ^ 59
def prefixEnd_5392970 : Nat := 4983230072969 + 3 ^ 40 * 5392970 * 2
def baseEnd_5392970 : Nat := 2769185765277870213773189

theorem tailTrace_5392970 : CollatzResearch.WordTrace tailWord_5392970 prefixEnd_5392970 2769185765277870213773189 := by
  unfold tailWord_5392970
  simp only [CollatzResearch.WordTrace]
  refine ⟨49174443818049552698224091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131131850181465473861930909 49174443818049552698224091)
  ·
    refine ⟨73761665727074329047336137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49174443818049552698224091 73761665727074329047336137)
    ·
      refine ⟨55321249295305746785502103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73761665727074329047336137 55321249295305746785502103)
      ·
        refine ⟨82981873942958620178253155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55321249295305746785502103 82981873942958620178253155)
        ·
          refine ⟨124472810914437930267379733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82981873942958620178253155 124472810914437930267379733)
          ·
            refine ⟨5834663011614277981283425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124472810914437930267379733 5834663011614277981283425)
            ·
              refine ⟨4375997258710708485962569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834663011614277981283425 4375997258710708485962569)
              ·
                refine ⟨3281997944033031364471927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4375997258710708485962569 3281997944033031364471927)
                ·
                  refine ⟨4922996916049547046707891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3281997944033031364471927 4922996916049547046707891)
                  ·
                    refine ⟨7384495374074320570061837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4922996916049547046707891 7384495374074320570061837)
                    ·
                      refine ⟨2769185765277870213773189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384495374074320570061837 2769185765277870213773189)
                      ·
                        rfl

theorem cell23_5392970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_5392970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392970 prefixEnd_5392970 := by exact prefixLift 5392970
  have htrace : WordTrace (prefixWord ++ tailWord_5392970) baseStart_5392970 baseEnd_5392970 := by
    simpa [prefixWord, tailWord_5392970, baseEnd_5392970] using wordTrace_append hprefix tailTrace_5392970
  have hstable : (prefixWord ++ tailWord_5392970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392970).length < 2 ^ (prefixWord ++ tailWord_5392970).sum := by decide
  have hdescent : baseEnd_5392970 < baseStart_5392970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5392972 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5392972 : Nat := 118140960795 + 5392972 * 2 ^ 59
def prefixEnd_5392972 : Nat := 4983230072969 + 3 ^ 40 * 5392972 * 2
def baseEnd_5392972 : Nat := 2769186792239179205948179

theorem tailTrace_5392972 : CollatzResearch.WordTrace tailWord_5392972 prefixEnd_5392972 2769186792239179205948179 := by
  unfold tailWord_5392972
  simp only [CollatzResearch.WordTrace]
  refine ⟨98348924109095482567234585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131131898812127310089646113 98348924109095482567234585)
  ·
    refine ⟨73761693081821611925425939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98348924109095482567234585 73761693081821611925425939)
    ·
      refine ⟨110642539622732417888138909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73761693081821611925425939 110642539622732417888138909)
      ·
        refine ⟨41490952358524656708052091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110642539622732417888138909 41490952358524656708052091)
        ·
          refine ⟨62236428537786985062078137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41490952358524656708052091 62236428537786985062078137)
          ·
            refine ⟨46677321403340238796558603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62236428537786985062078137 46677321403340238796558603)
            ·
              refine ⟨70015982105010358194837905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46677321403340238796558603 70015982105010358194837905)
              ·
                refine ⟨52511986578757768646128429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70015982105010358194837905 52511986578757768646128429)
                ·
                  refine ⟨19691994967034163242298161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52511986578757768646128429 19691994967034163242298161)
                  ·
                    refine ⟨14768996225275622431723621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19691994967034163242298161 14768996225275622431723621)
                    ·
                      refine ⟨2769186792239179205948179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14768996225275622431723621 2769186792239179205948179)
                      ·
                        rfl

theorem cell23_5392972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5392972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5392972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5392972 prefixEnd_5392972 := by exact prefixLift 5392972
  have htrace : WordTrace (prefixWord ++ tailWord_5392972) baseStart_5392972 baseEnd_5392972 := by
    simpa [prefixWord, tailWord_5392972, baseEnd_5392972] using wordTrace_append hprefix tailTrace_5392972
  have hstable : (prefixWord ++ tailWord_5392972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5392972).length < 2 ^ (prefixWord ++ tailWord_5392972).sum := by decide
  have hdescent : baseEnd_5392972 < baseStart_5392972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5392972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393010 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_5393010 : Nat := 118140960795 + 5393010 * 2 ^ 59
def prefixEnd_5393010 : Nat := 4983230072969 + 3 ^ 40 * 5393010 * 2
def baseEnd_5393010 : Nat := 2769206304504050057273005

theorem tailTrace_5393010 : CollatzResearch.WordTrace tailWord_5393010 prefixEnd_5393010 2769206304504050057273005 := by
  unfold tailWord_5393010
  simp only [CollatzResearch.WordTrace]
  refine ⟨49174808548013324406088121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131132822794702198416234989 49174808548013324406088121)
  ·
    refine ⟨36881106411009993304566091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49174808548013324406088121 36881106411009993304566091)
    ·
      refine ⟨55321659616514989956849137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36881106411009993304566091 55321659616514989956849137)
      ·
        refine ⟨41491244712386242467636853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55321659616514989956849137 41491244712386242467636853)
        ·
          refine ⟨3889804191786210231340955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41491244712386242467636853 3889804191786210231340955)
          ·
            refine ⟨5834706287679315347011433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3889804191786210231340955 5834706287679315347011433)
            ·
              refine ⟨4376029715759486510258575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5834706287679315347011433 4376029715759486510258575)
              ·
                refine ⟨6564044573639229765387863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376029715759486510258575 6564044573639229765387863)
                ·
                  refine ⟨9846066860458844648081795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564044573639229765387863 9846066860458844648081795)
                  ·
                    refine ⟨14769100290688266972122693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9846066860458844648081795 14769100290688266972122693)
                    ·
                      refine ⟨2769206304504050057273005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14769100290688266972122693 2769206304504050057273005)
                      ·
                        rfl

theorem cell23_5393010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_5393010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393010 prefixEnd_5393010 := by exact prefixLift 5393010
  have htrace : WordTrace (prefixWord ++ tailWord_5393010) baseStart_5393010 baseEnd_5393010 := by
    simpa [prefixWord, tailWord_5393010, baseEnd_5393010] using wordTrace_append hprefix tailTrace_5393010
  have hstable : (prefixWord ++ tailWord_5393010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393010).length < 2 ^ (prefixWord ++ tailWord_5393010).sum := by decide
  have hdescent : baseEnd_5393010 < baseStart_5393010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393013 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5393013 : Nat := 118140960795 + 5393013 * 2 ^ 59
def prefixEnd_5393013 : Nat := 4983230072969 + 3 ^ 40 * 5393013 * 2
def baseEnd_5393013 : Nat := 2769207844946013545535491

theorem tailTrace_5393013 : CollatzResearch.WordTrace tailWord_5393013 prefixEnd_5393013 2769207844946013545535491 := by
  unfold tailWord_5393013
  simp only [CollatzResearch.WordTrace]
  refine ⟨196699343611042429136711693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131132895740694952757807795 196699343611042429136711693)
  ·
    refine ⟨73762253854140910926266885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196699343611042429136711693 73762253854140910926266885)
    ·
      refine ⟨13830422597651420798675041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73762253854140910926266885 13830422597651420798675041)
      ·
        refine ⟨10372816948238565599006281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13830422597651420798675041 10372816948238565599006281)
        ·
          refine ⟨7779612711178924199254711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10372816948238565599006281 7779612711178924199254711)
          ·
            refine ⟨11669419066768386298882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779612711178924199254711 11669419066768386298882067)
            ·
              refine ⟨17504128600152579448323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11669419066768386298882067 17504128600152579448323101)
              ·
                refine ⟨6564048225057217293121163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17504128600152579448323101 6564048225057217293121163)
                ·
                  refine ⟨9846072337585825939681745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564048225057217293121163 9846072337585825939681745)
                  ·
                    refine ⟨7384554253189369454761309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9846072337585825939681745 7384554253189369454761309)
                    ·
                      refine ⟨2769207844946013545535491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7384554253189369454761309 2769207844946013545535491)
                      ·
                        rfl

theorem cell23_5393013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5393013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393013 prefixEnd_5393013 := by exact prefixLift 5393013
  have htrace : WordTrace (prefixWord ++ tailWord_5393013) baseStart_5393013 baseEnd_5393013 := by
    simpa [prefixWord, tailWord_5393013, baseEnd_5393013] using wordTrace_append hprefix tailTrace_5393013
  have hstable : (prefixWord ++ tailWord_5393013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393013).length < 2 ^ (prefixWord ++ tailWord_5393013).sum := by decide
  have hdescent : baseEnd_5393013 < baseStart_5393013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393019 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 5, 3, 2]
def baseStart_5393019 : Nat := 118140960795 + 5393019 * 2 ^ 59
def prefixEnd_5393019 : Nat := 4983230072969 + 3 ^ 40 * 5393019 * 2
def baseEnd_5393019 : Nat := 2769210925829940522060463

theorem tailTrace_5393019 : CollatzResearch.WordTrace tailWord_5393019 prefixEnd_5393019 2769210925829940522060463 := by
  unfold tailWord_5393019
  simp only [CollatzResearch.WordTrace]
  refine ⟨196699562449020692161430111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131133041632680461440953407 196699562449020692161430111)
  ·
    refine ⟨295049343673531038242145167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196699562449020692161430111 295049343673531038242145167)
    ·
      refine ⟨442574015510296557363217751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295049343673531038242145167 442574015510296557363217751)
      ·
        refine ⟨663861023265444836044826627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442574015510296557363217751 663861023265444836044826627)
        ·
          refine ⟨995791534898167254067239941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663861023265444836044826627 995791534898167254067239941)
          ·
            refine ⟨186710912793406360137607489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 995791534898167254067239941 186710912793406360137607489)
            ·
              refine ⟨140033184595054770103205617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186710912793406360137607489 140033184595054770103205617)
              ·
                refine ⟨105024888446291077577404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140033184595054770103205617 105024888446291077577404213)
                ·
                  refine ⟨9846083291839788522881645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105024888446291077577404213 9846083291839788522881645)
                  ·
                    refine ⟨3692281234439920696080617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9846083291839788522881645 3692281234439920696080617)
                    ·
                      refine ⟨2769210925829940522060463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692281234439920696080617 2769210925829940522060463)
                      ·
                        rfl

theorem cell23_5393019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3, 2].length) (baseStart_5393019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393019 prefixEnd_5393019 := by exact prefixLift 5393019
  have htrace : WordTrace (prefixWord ++ tailWord_5393019) baseStart_5393019 baseEnd_5393019 := by
    simpa [prefixWord, tailWord_5393019, baseEnd_5393019] using wordTrace_append hprefix tailTrace_5393019
  have hstable : (prefixWord ++ tailWord_5393019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393019).length < 2 ^ (prefixWord ++ tailWord_5393019).sum := by decide
  have hdescent : baseEnd_5393019 < baseStart_5393019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393069 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5393069 : Nat := 118140960795 + 5393069 * 2 ^ 59
def prefixEnd_5393069 : Nat := 4983230072969 + 3 ^ 40 * 5393069 * 2
def baseEnd_5393069 : Nat := 2769236599862665326435233

theorem tailTrace_5393069 : CollatzResearch.WordTrace tailWord_5393069 prefixEnd_5393069 2769236599862665326435233 := by
  unfold tailWord_5393069
  simp only [CollatzResearch.WordTrace]
  refine ⟨196701386098839550700750261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131134257399226367133833507 196701386098839550700750261)
  ·
    refine ⟨18440754946766207878195337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196701386098839550700750261 18440754946766207878195337)
    ·
      refine ⟨13830566210074655908646503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18440754946766207878195337 13830566210074655908646503)
      ·
        refine ⟨20745849315111983862969755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13830566210074655908646503 20745849315111983862969755)
        ·
          refine ⟨31118773972667975794454633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20745849315111983862969755 31118773972667975794454633)
          ·
            refine ⟨23339080479500981845840975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31118773972667975794454633 23339080479500981845840975)
            ·
              refine ⟨35008620719251472768761463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23339080479500981845840975 35008620719251472768761463)
              ·
                refine ⟨52512931078877209153142195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35008620719251472768761463 52512931078877209153142195)
                ·
                  refine ⟨78769396618315813729713293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52512931078877209153142195 78769396618315813729713293)
                  ·
                    refine ⟨29538523731868430148642485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78769396618315813729713293 29538523731868430148642485)
                    ·
                      refine ⟨2769236599862665326435233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29538523731868430148642485 2769236599862665326435233)
                      ·
                        rfl

theorem cell23_5393069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5393069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393069 prefixEnd_5393069 := by exact prefixLift 5393069
  have htrace : WordTrace (prefixWord ++ tailWord_5393069) baseStart_5393069 baseEnd_5393069 := by
    simpa [prefixWord, tailWord_5393069, baseEnd_5393069] using wordTrace_append hprefix tailTrace_5393069
  have hstable : (prefixWord ++ tailWord_5393069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393069).length < 2 ^ (prefixWord ++ tailWord_5393069).sum := by decide
  have hdescent : baseEnd_5393069 < baseStart_5393069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393070 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5393070 : Nat := 118140960795 + 5393070 * 2 ^ 59
def prefixEnd_5393070 : Nat := 4983230072969 + 3 ^ 40 * 5393070 * 2
def baseEnd_5393070 : Nat := 2769237113343319822522729

theorem tailTrace_5393070 : CollatzResearch.WordTrace tailWord_5393070 prefixEnd_5393070 2769237113343319822522729 := by
  unfold tailWord_5393070
  simp only [CollatzResearch.WordTrace]
  refine ⟨24587677821479490983942083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131134281714557285247691109 24587677821479490983942083)
  ·
    refine ⟨36881516732219236475913125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24587677821479490983942083 36881516732219236475913125)
    ·
      refine ⟨6915284387291106839233711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36881516732219236475913125 6915284387291106839233711)
      ·
        refine ⟨10372926580936660258850567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915284387291106839233711 10372926580936660258850567)
        ·
          refine ⟨15559389871404990388275851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372926580936660258850567 15559389871404990388275851)
          ·
            refine ⟨23339084807107485582413777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15559389871404990388275851 23339084807107485582413777)
            ·
              refine ⟨17504313605330614186810333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23339084807107485582413777 17504313605330614186810333)
              ·
                refine ⟨6564117601998980320053875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17504313605330614186810333 6564117601998980320053875)
                ·
                  refine ⟨9846176402998470480080813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6564117601998980320053875 9846176402998470480080813)
                  ·
                    refine ⟨3692316151124426430030305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9846176402998470480080813 3692316151124426430030305)
                    ·
                      refine ⟨2769237113343319822522729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692316151124426430030305 2769237113343319822522729)
                      ·
                        rfl

theorem cell23_5393070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5393070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393070 prefixEnd_5393070 := by exact prefixLift 5393070
  have htrace : WordTrace (prefixWord ++ tailWord_5393070) baseStart_5393070 baseEnd_5393070 := by
    simpa [prefixWord, tailWord_5393070, baseEnd_5393070] using wordTrace_append hprefix tailTrace_5393070
  have hstable : (prefixWord ++ tailWord_5393070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393070).length < 2 ^ (prefixWord ++ tailWord_5393070).sum := by decide
  have hdescent : baseEnd_5393070 < baseStart_5393070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393082 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_5393082 : Nat := 118140960795 + 5393082 * 2 ^ 59
def prefixEnd_5393082 : Nat := 4983230072969 + 3 ^ 40 * 5393082 * 2
def baseEnd_5393082 : Nat := 2769243275111173775572673

theorem tailTrace_5393082 : CollatzResearch.WordTrace tailWord_5393082 prefixEnd_5393082 2769243275111173775572673 := by
  unfold tailWord_5393082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49175465061948113480243375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131134573498528302613982333 49175465061948113480243375)
  ·
    refine ⟨73763197592922170220365063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49175465061948113480243375 73763197592922170220365063)
    ·
      refine ⟨110644796389383255330547595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73763197592922170220365063 110644796389383255330547595)
      ·
        refine ⟨165967194584074882995821393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110644796389383255330547595 165967194584074882995821393)
        ·
          refine ⟨124475395938056162246866045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165967194584074882995821393 124475395938056162246866045)
          ·
            refine ⟨46678273476771060842574767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124475395938056162246866045 46678273476771060842574767)
            ·
              refine ⟨70017410215156591263862151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46678273476771060842574767 70017410215156591263862151)
              ·
                refine ⟨105026115322734886895793227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70017410215156591263862151 105026115322734886895793227)
                ·
                  refine ⟨157539172984102330343689841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105026115322734886895793227 157539172984102330343689841)
                  ·
                    refine ⟨118154379738076747757767381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157539172984102330343689841 118154379738076747757767381)
                    ·
                      refine ⟨2769243275111173775572673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118154379738076747757767381 2769243275111173775572673)
                      ·
                        rfl

theorem cell23_5393082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_5393082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393082 prefixEnd_5393082 := by exact prefixLift 5393082
  have htrace : WordTrace (prefixWord ++ tailWord_5393082) baseStart_5393082 baseEnd_5393082 := by
    simpa [prefixWord, tailWord_5393082, baseEnd_5393082] using wordTrace_append hprefix tailTrace_5393082
  have hstable : (prefixWord ++ tailWord_5393082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393082).length < 2 ^ (prefixWord ++ tailWord_5393082).sum := by decide
  have hdescent : baseEnd_5393082 < baseStart_5393082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393100 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5393100 : Nat := 118140960795 + 5393100 * 2 ^ 59
def prefixEnd_5393100 : Nat := 4983230072969 + 3 ^ 40 * 5393100 * 2
def baseEnd_5393100 : Nat := 2769252517762954705147591

theorem tailTrace_5393100 : CollatzResearch.WordTrace tailWord_5393100 prefixEnd_5393100 2769252517762954705147591 := by
  unfold tailWord_5393100
  simp only [CollatzResearch.WordTrace]
  refine ⟨98351258380863621497564377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131135011174484828663419169 98351258380863621497564377)
  ·
    refine ⟨73763443785647716123173283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98351258380863621497564377 73763443785647716123173283)
    ·
      refine ⟨110645165678471574184759925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73763443785647716123173283 110645165678471574184759925)
      ·
        refine ⟨10372984282356710079821243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110645165678471574184759925 10372984282356710079821243)
        ·
          refine ⟨15559476423535065119731865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372984282356710079821243 15559476423535065119731865)
          ·
            refine ⟨11669607317651298839798899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15559476423535065119731865 11669607317651298839798899)
            ·
              refine ⟨17504410976476948259698349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11669607317651298839798899 17504410976476948259698349)
              ·
                refine ⟨6564154116178855597386881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17504410976476948259698349 6564154116178855597386881)
                ·
                  refine ⟨4923115587134141698040161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564154116178855597386881 4923115587134141698040161)
                  ·
                    refine ⟨3692336690350606273530121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923115587134141698040161 3692336690350606273530121)
                    ·
                      refine ⟨2769252517762954705147591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692336690350606273530121 2769252517762954705147591)
                      ·
                        rfl

theorem cell23_5393100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5393100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393100 prefixEnd_5393100 := by exact prefixLift 5393100
  have htrace : WordTrace (prefixWord ++ tailWord_5393100) baseStart_5393100 baseEnd_5393100 := by
    simpa [prefixWord, tailWord_5393100, baseEnd_5393100] using wordTrace_append hprefix tailTrace_5393100
  have hstable : (prefixWord ++ tailWord_5393100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393100).length < 2 ^ (prefixWord ++ tailWord_5393100).sum := by decide
  have hdescent : baseEnd_5393100 < baseStart_5393100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393119 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 2, 5]
def baseStart_5393119 : Nat := 118140960795 + 5393119 * 2 ^ 59
def prefixEnd_5393119 : Nat := 4983230072969 + 3 ^ 40 * 5393119 * 2
def baseEnd_5393119 : Nat := 923087424631796710270001

theorem tailTrace_5393119 : CollatzResearch.WordTrace tailWord_5393119 prefixEnd_5393119 923087424631796710270001 := by
  unfold tailWord_5393119
  simp only [CollatzResearch.WordTrace]
  refine ⟨196703209748658409240070411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131135473165772272826713607 196703209748658409240070411)
  ·
    refine ⟨295054814622987613860105617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196703209748658409240070411 295054814622987613860105617)
    ·
      refine ⟨221291110967240710395079213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295054814622987613860105617 221291110967240710395079213)
      ·
        refine ⟨82984166612715266398154705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221291110967240710395079213 82984166612715266398154705)
        ·
          refine ⟨62238124959536449798616029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82984166612715266398154705 62238124959536449798616029)
          ·
            refine ⟨23339296859826168674481011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62238124959536449798616029 23339296859826168674481011)
            ·
              refine ⟨35008945289739253011721517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23339296859826168674481011 35008945289739253011721517)
              ·
                refine ⟨13128354483652219879395569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35008945289739253011721517 13128354483652219879395569)
                ·
                  refine ⟨9846265862739164909546677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13128354483652219879395569 9846265862739164909546677)
                  ·
                    refine ⟨923087424631796710270001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9846265862739164909546677 923087424631796710270001)
                    ·
                      rfl

theorem cell23_5393119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_5393119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393119 prefixEnd_5393119 := by exact prefixLift 5393119
  have htrace : WordTrace (prefixWord ++ tailWord_5393119) baseStart_5393119 baseEnd_5393119 := by
    simpa [prefixWord, tailWord_5393119, baseEnd_5393119] using wordTrace_append hprefix tailTrace_5393119
  have hstable : (prefixWord ++ tailWord_5393119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393119).length < 2 ^ (prefixWord ++ tailWord_5393119).sum := by decide
  have hdescent : baseEnd_5393119 < baseStart_5393119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393170 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5393170 : Nat := 118140960795 + 5393170 * 2 ^ 59
def prefixEnd_5393170 : Nat := 4983230072969 + 3 ^ 40 * 5393170 * 2
def baseEnd_5393170 : Nat := 923096153802923143757423

theorem tailTrace_5393170 : CollatzResearch.WordTrace tailWord_5393170 prefixEnd_5393170 923096153802923143757423 := by
  unfold tailWord_5393170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49176267467868411237544241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131136713247649096633451309 49176267467868411237544241)
  ·
    refine ⟨36882200600901308428158181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49176267467868411237544241 36882200600901308428158181)
    ·
      refine ⟨6915412612668995330279659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36882200600901308428158181 6915412612668995330279659)
      ·
        refine ⟨10373118919003492995419489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915412612668995330279659 10373118919003492995419489)
        ·
          refine ⟨7779839189252619746564617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10373118919003492995419489 7779839189252619746564617)
          ·
            refine ⟨5834879391939464809923463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7779839189252619746564617 5834879391939464809923463)
            ·
              refine ⟨8752319087909197214885195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834879391939464809923463 8752319087909197214885195)
              ·
                refine ⟨13128478631863795822327793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8752319087909197214885195 13128478631863795822327793)
                ·
                  refine ⟨9846358973897846866745845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13128478631863795822327793 9846358973897846866745845)
                  ·
                    refine ⟨923096153802923143757423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9846358973897846866745845 923096153802923143757423)
                    ·
                      rfl

theorem cell23_5393170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5393170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393170 prefixEnd_5393170 := by exact prefixLift 5393170
  have htrace : WordTrace (prefixWord ++ tailWord_5393170) baseStart_5393170 baseEnd_5393170 := by
    simpa [prefixWord, tailWord_5393170, baseEnd_5393170] using wordTrace_append hprefix tailTrace_5393170
  have hstable : (prefixWord ++ tailWord_5393170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393170).length < 2 ^ (prefixWord ++ tailWord_5393170).sum := by decide
  have hdescent : baseEnd_5393170 < baseStart_5393170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393183 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 1, 4]
def baseStart_5393183 : Nat := 118140960795 + 5393183 * 2 ^ 59
def prefixEnd_5393183 : Nat := 4983230072969 + 3 ^ 40 * 5393183 * 2
def baseEnd_5393183 : Nat := 923098378885759293469903

theorem tailTrace_5393183 : CollatzResearch.WordTrace tailWord_5393183 prefixEnd_5393183 923098378885759293469903 := by
  unfold tailWord_5393183
  simp only [CollatzResearch.WordTrace]
  refine ⟨196705544020426548170400203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131137029346951032113600135 196705544020426548170400203)
  ·
    refine ⟨295058316030639822255600305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196705544020426548170400203 295058316030639822255600305)
    ·
      refine ⟨221293737022979866691700229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295058316030639822255600305 221293737022979866691700229)
      ·
        refine ⟨41492575691808725004693793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221293737022979866691700229 41492575691808725004693793)
        ·
          refine ⟨31119431768856543753520345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41492575691808725004693793 31119431768856543753520345)
          ·
            refine ⟨23339573826642407815140259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31119431768856543753520345 23339573826642407815140259)
            ·
              refine ⟨35009360739963611722710389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23339573826642407815140259 35009360739963611722710389)
              ·
                refine ⟨3282127569371588599004099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35009360739963611722710389 3282127569371588599004099)
                ·
                  refine ⟨4923191354057382898506149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282127569371588599004099 4923191354057382898506149)
                  ·
                    refine ⟨923098378885759293469903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923191354057382898506149 923098378885759293469903)
                    ·
                      rfl

theorem cell23_5393183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_5393183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393183 prefixEnd_5393183 := by exact prefixLift 5393183
  have htrace : WordTrace (prefixWord ++ tailWord_5393183) baseStart_5393183 baseEnd_5393183 := by
    simpa [prefixWord, tailWord_5393183, baseEnd_5393183] using wordTrace_append hprefix tailTrace_5393183
  have hstable : (prefixWord ++ tailWord_5393183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393183).length < 2 ^ (prefixWord ++ tailWord_5393183).sum := by decide
  have hdescent : baseEnd_5393183 < baseStart_5393183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393259 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6]
def baseStart_5393259 : Nat := 118140960795 + 5393259 * 2 ^ 59
def prefixEnd_5393259 : Nat := 4983230072969 + 3 ^ 40 * 5393259 * 2
def baseEnd_5393259 : Nat := 2769334161187019583059359

theorem tailTrace_5393259 : CollatzResearch.WordTrace tailWord_5393259 prefixEnd_5393259 2769334161187019583059359 := by
  unfold tailWord_5393259
  simp only [CollatzResearch.WordTrace]
  refine ⟨196708315968151213150166831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131138877312100808766777887 196708315968151213150166831)
  ·
    refine ⟨295062473952226819725250247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196708315968151213150166831 295062473952226819725250247)
    ·
      refine ⟨442593710928340229587875371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295062473952226819725250247 442593710928340229587875371)
      ·
        refine ⟨663890566392510344381813057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442593710928340229587875371 663890566392510344381813057)
        ·
          refine ⟨497917924794382758286359793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663890566392510344381813057 497917924794382758286359793)
          ·
            refine ⟨373438443595787068714769845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497917924794382758286359793 373438443595787068714769845)
            ·
              refine ⟨35009854087105037692009673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373438443595787068714769845 35009854087105037692009673)
              ·
                refine ⟨26257390565328778269007255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35009854087105037692009673 26257390565328778269007255)
                ·
                  refine ⟨39386085847993167403510883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26257390565328778269007255 39386085847993167403510883)
                  ·
                    refine ⟨59079128771989751105266325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39386085847993167403510883 59079128771989751105266325)
                    ·
                      refine ⟨2769334161187019583059359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59079128771989751105266325 2769334161187019583059359)
                      ·
                        rfl

theorem cell23_5393259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_5393259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393259 prefixEnd_5393259 := by exact prefixLift 5393259
  have htrace : WordTrace (prefixWord ++ tailWord_5393259) baseStart_5393259 baseEnd_5393259 := by
    simpa [prefixWord, tailWord_5393259, baseEnd_5393259] using wordTrace_append hprefix tailTrace_5393259
  have hstable : (prefixWord ++ tailWord_5393259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393259).length < 2 ^ (prefixWord ++ tailWord_5393259).sum := by decide
  have hdescent : baseEnd_5393259 < baseStart_5393259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393266 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5393266 : Nat := 118140960795 + 5393266 * 2 ^ 59
def prefixEnd_5393266 : Nat := 4983230072969 + 3 ^ 40 * 5393266 * 2
def baseEnd_5393266 : Nat := 2769337755551601055671827

theorem tailTrace_5393266 : CollatzResearch.WordTrace tailWord_5393266 prefixEnd_5393266 2769337755551601055671827 := by
  unfold tailWord_5393266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49177142819781463336417913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131139047519417235563781101 49177142819781463336417913)
  ·
    refine ⟨36882857114836097502313435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49177142819781463336417913 36882857114836097502313435)
    ·
      refine ⟨55324285672254146253470153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36882857114836097502313435 55324285672254146253470153)
      ·
        refine ⟨41493214254190609690102615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55324285672254146253470153 41493214254190609690102615)
        ·
          refine ⟨62239821381285914535153923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41493214254190609690102615 62239821381285914535153923)
          ·
            refine ⟨93359732071928871802730885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62239821381285914535153923 93359732071928871802730885)
            ·
              refine ⟨17504949763486663463012041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93359732071928871802730885 17504949763486663463012041)
              ·
                refine ⟨13128712322614997597259031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17504949763486663463012041 13128712322614997597259031)
                ·
                  refine ⟨19693068483922496395888547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13128712322614997597259031 19693068483922496395888547)
                  ·
                    refine ⟨29539602725883744593832821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19693068483922496395888547 29539602725883744593832821)
                    ·
                      refine ⟨2769337755551601055671827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29539602725883744593832821 2769337755551601055671827)
                      ·
                        rfl

theorem cell23_5393266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5393266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393266 prefixEnd_5393266 := by exact prefixLift 5393266
  have htrace : WordTrace (prefixWord ++ tailWord_5393266) baseStart_5393266 baseEnd_5393266 := by
    simpa [prefixWord, tailWord_5393266, baseEnd_5393266] using wordTrace_append hprefix tailTrace_5393266
  have hstable : (prefixWord ++ tailWord_5393266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393266).length < 2 ^ (prefixWord ++ tailWord_5393266).sum := by decide
  have hdescent : baseEnd_5393266 < baseStart_5393266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393273 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_5393273 : Nat := 118140960795 + 5393273 * 2 ^ 59
def prefixEnd_5393273 : Nat := 4983230072969 + 3 ^ 40 * 5393273 * 2
def baseEnd_5393273 : Nat := 923113783305394176094765

theorem tailTrace_5393273 : CollatzResearch.WordTrace tailWord_5393273 prefixEnd_5393273 923113783305394176094765 := by
  unfold tailWord_5393273
  simp only [CollatzResearch.WordTrace]
  refine ⟨196708826590100493541176473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131139217726733662360784315 196708826590100493541176473)
  ·
    refine ⟨147531619942575370155882355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196708826590100493541176473 147531619942575370155882355)
    ·
      refine ⟨221297429913863055233823533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147531619942575370155882355 221297429913863055233823533)
      ·
        refine ⟨82986536217698645712683825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221297429913863055233823533 82986536217698645712683825)
        ·
          refine ⟨62239902163273984284512869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82986536217698645712683825 62239902163273984284512869)
          ·
            refine ⟨11669981655613872053346163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62239902163273984284512869 11669981655613872053346163)
            ·
              refine ⟨17504972483420808080019245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11669981655613872053346163 17504972483420808080019245)
              ·
                refine ⟨6564364681282803030007217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17504972483420808080019245 6564364681282803030007217)
                ·
                  refine ⟨4923273510962102272505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564364681282803030007217 4923273510962102272505413)
                  ·
                    refine ⟨923113783305394176094765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923273510962102272505413 923113783305394176094765)
                    ·
                      rfl

theorem cell23_5393273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_5393273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393273 prefixEnd_5393273 := by exact prefixLift 5393273
  have htrace : WordTrace (prefixWord ++ tailWord_5393273) baseStart_5393273 baseEnd_5393273 := by
    simpa [prefixWord, tailWord_5393273, baseEnd_5393273] using wordTrace_append hprefix tailTrace_5393273
  have hstable : (prefixWord ++ tailWord_5393273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393273).length < 2 ^ (prefixWord ++ tailWord_5393273).sum := by decide
  have hdescent : baseEnd_5393273 < baseStart_5393273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393314 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_5393314 : Nat := 118140960795 + 5393314 * 2 ^ 59
def prefixEnd_5393314 : Nat := 4983230072969 + 3 ^ 40 * 5393314 * 2
def baseEnd_5393314 : Nat := 2769362402623016867871607

theorem tailTrace_5393314 : CollatzResearch.WordTrace tailWord_5393314 prefixEnd_5393314 2769362402623016867871607 := by
  unfold tailWord_5393314
  simp only [CollatzResearch.WordTrace]
  refine ⟨49177580495737989385854749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131140214655301305028945997 49177580495737989385854749)
  ·
    refine ⟨18441592685901746019695531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49177580495737989385854749 18441592685901746019695531)
    ·
      refine ⟨27662389028852619029543297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18441592685901746019695531 27662389028852619029543297)
      ·
        refine ⟨20746791771639464272157473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27662389028852619029543297 20746791771639464272157473)
        ·
          refine ⟨15560093828729598204118105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20746791771639464272157473 15560093828729598204118105)
          ·
            refine ⟨11670070371547198653088579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15560093828729598204118105 11670070371547198653088579)
            ·
              refine ⟨17505105557320797979632869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11670070371547198653088579 17505105557320797979632869)
              ·
                refine ⟨3282207291997649621181163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17505105557320797979632869 3282207291997649621181163)
                ·
                  refine ⟨4923310937996474431771745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282207291997649621181163 4923310937996474431771745)
                  ·
                    refine ⟨3692483203497355823828809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923310937996474431771745 3692483203497355823828809)
                    ·
                      refine ⟨2769362402623016867871607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692483203497355823828809 2769362402623016867871607)
                      ·
                        rfl

theorem cell23_5393314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_5393314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393314 prefixEnd_5393314 := by exact prefixLift 5393314
  have htrace : WordTrace (prefixWord ++ tailWord_5393314) baseStart_5393314 baseEnd_5393314 := by
    simpa [prefixWord, tailWord_5393314, baseEnd_5393314] using wordTrace_append hprefix tailTrace_5393314
  have hstable : (prefixWord ++ tailWord_5393314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393314).length < 2 ^ (prefixWord ++ tailWord_5393314).sum := by decide
  have hdescent : baseEnd_5393314 < baseStart_5393314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393356 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5393356 : Nat := 118140960795 + 5393356 * 2 ^ 59
def prefixEnd_5393356 : Nat := 4983230072969 + 3 ^ 40 * 5393356 * 2
def baseEnd_5393356 : Nat := 2769383968810505703546413

theorem tailTrace_5393356 : CollatzResearch.WordTrace tailWord_5393356 prefixEnd_5393356 2769383968810505703546413 := by
  unfold tailWord_5393356
  simp only [CollatzResearch.WordTrace]
  refine ⟨98355926924399899358223961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131141235899199865810965281 98355926924399899358223961)
  ·
    refine ⟨73766945193299924518667971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98355926924399899358223961 73766945193299924518667971)
    ·
      refine ⟨110650417789949886778001957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73766945193299924518667971 110650417789949886778001957)
      ·
        refine ⟨20746953335615603770875367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110650417789949886778001957 20746953335615603770875367)
        ·
          refine ⟨31120430003423405656313051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20746953335615603770875367 31120430003423405656313051)
          ·
            refine ⟨46680645005135108484469577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31120430003423405656313051 46680645005135108484469577)
            ·
              refine ⟨35010483753851331363352183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46680645005135108484469577 35010483753851331363352183)
              ·
                refine ⟨52515725630776997045028275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35010483753851331363352183 52515725630776997045028275)
                ·
                  refine ⟨78773588446165495567542413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52515725630776997045028275 78773588446165495567542413)
                  ·
                    refine ⟨29540095667312060837828405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78773588446165495567542413 29540095667312060837828405)
                    ·
                      refine ⟨2769383968810505703546413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29540095667312060837828405 2769383968810505703546413)
                      ·
                        rfl

theorem cell23_5393356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5393356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393356 prefixEnd_5393356 := by exact prefixLift 5393356
  have htrace : WordTrace (prefixWord ++ tailWord_5393356) baseStart_5393356 baseEnd_5393356 := by
    simpa [prefixWord, tailWord_5393356, baseEnd_5393356] using wordTrace_append hprefix tailTrace_5393356
  have hstable : (prefixWord ++ tailWord_5393356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393356).length < 2 ^ (prefixWord ++ tailWord_5393356).sum := by decide
  have hdescent : baseEnd_5393356 < baseStart_5393356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393383 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5393383 : Nat := 118140960795 + 5393383 * 2 ^ 59
def prefixEnd_5393383 : Nat := 4983230072969 + 3 ^ 40 * 5393383 * 2
def baseEnd_5393383 : Nat := 2769397832788177097908789

theorem tailTrace_5393383 : CollatzResearch.WordTrace tailWord_5393383 prefixEnd_5393383 2769397832788177097908789 := by
  unfold tailWord_5393383
  simp only [CollatzResearch.WordTrace]
  refine ⟨196712838619701982327680803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131141892413134654885120535 196712838619701982327680803)
  ·
    refine ⟨295069257929552973491521205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196712838619701982327680803 295069257929552973491521205)
    ·
      refine ⟨27662742930895591264830113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295069257929552973491521205 27662742930895591264830113)
      ·
        refine ⟨20747057198171693448622585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27662742930895591264830113 20747057198171693448622585)
        ·
          refine ⟨15560292898628770086466939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20747057198171693448622585 15560292898628770086466939)
          ·
            refine ⟨23340439347943155129700409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560292898628770086466939 23340439347943155129700409)
            ·
              refine ⟨17505329510957366347275307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23340439347943155129700409 17505329510957366347275307)
              ·
                refine ⟨26257994266436049520912961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17505329510957366347275307 26257994266436049520912961)
                ·
                  refine ⟨19693495699827037140684721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26257994266436049520912961 19693495699827037140684721)
                  ·
                    refine ⟨14770121774870277855513541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19693495699827037140684721 14770121774870277855513541)
                    ·
                      refine ⟨2769397832788177097908789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14770121774870277855513541 2769397832788177097908789)
                      ·
                        rfl

theorem cell23_5393383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5393383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393383 prefixEnd_5393383 := by exact prefixLift 5393383
  have htrace : WordTrace (prefixWord ++ tailWord_5393383) baseStart_5393383 baseEnd_5393383 := by
    simpa [prefixWord, tailWord_5393383, baseEnd_5393383] using wordTrace_append hprefix tailTrace_5393383
  have hstable : (prefixWord ++ tailWord_5393383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393383).length < 2 ^ (prefixWord ++ tailWord_5393383).sum := by decide
  have hdescent : baseEnd_5393383 < baseStart_5393383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393466 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_5393466 : Nat := 118140960795 + 5393466 * 2 ^ 59
def prefixEnd_5393466 : Nat := 4983230072969 + 3 ^ 40 * 5393466 * 2
def baseEnd_5393466 : Nat := 307715605742500030352323

theorem tailTrace_5393466 : CollatzResearch.WordTrace tailWord_5393466 prefixEnd_5393466 307715605742500030352323 := by
  unfold tailWord_5393466
  simp only [CollatzResearch.WordTrace]
  refine ⟨49178966469600321875738063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131143910585600858335301501 49178966469600321875738063)
  ·
    refine ⟨73768449704400482813607095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49178966469600321875738063 73768449704400482813607095)
    ·
      refine ⟨110652674556600724220410643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73768449704400482813607095 110652674556600724220410643)
      ·
        refine ⟨165979011834901086330615965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110652674556600724220410643 165979011834901086330615965)
        ·
          refine ⟨62242129438087907373980987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165979011834901086330615965 62242129438087907373980987)
          ·
            refine ⟨93363194157131861060971481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62242129438087907373980987 93363194157131861060971481)
            ·
              refine ⟨70022395617848895795728611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93363194157131861060971481 70022395617848895795728611)
              ·
                refine ⟨105033593426773343693592917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70022395617848895795728611 105033593426773343693592917)
                ·
                  refine ⟨307715605742500030352323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105033593426773343693592917 307715605742500030352323)
                  ·
                    rfl

theorem cell23_5393466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_5393466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393466 prefixEnd_5393466 := by exact prefixLift 5393466
  have htrace : WordTrace (prefixWord ++ tailWord_5393466) baseStart_5393466 baseEnd_5393466 := by
    simpa [prefixWord, tailWord_5393466, baseEnd_5393466] using wordTrace_append hprefix tailTrace_5393466
  have hstable : (prefixWord ++ tailWord_5393466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393466).length < 2 ^ (prefixWord ++ tailWord_5393466).sum := by decide
  have hdescent : baseEnd_5393466 < baseStart_5393466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393513 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_5393513 : Nat := 118140960795 + 5393513 * 2 ^ 59
def prefixEnd_5393513 : Nat := 4983230072969 + 3 ^ 40 * 5393513 * 2
def baseEnd_5393513 : Nat := 923154861757753863094397

theorem tailTrace_5393513 : CollatzResearch.WordTrace tailWord_5393513 prefixEnd_5393513 923154861757753863094397 := by
  unfold tailWord_5393513
  simp only [CollatzResearch.WordTrace]
  refine ⟨196717580109231014529913193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131145053406154009686608795 196717580109231014529913193)
  ·
    refine ⟨147538185081923260897434895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196717580109231014529913193 147538185081923260897434895)
    ·
      refine ⟨221307277622884891346152343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147538185081923260897434895 221307277622884891346152343)
      ·
        refine ⟨331960916434327337019228515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221307277622884891346152343 331960916434327337019228515)
        ·
          refine ⟨497941374651491005528842773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331960916434327337019228515 497941374651491005528842773)
          ·
            refine ⟨23341001936788640884164505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 497941374651491005528842773 23341001936788640884164505)
            ·
              refine ⟨17505751452591480663123379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23341001936788640884164505 17505751452591480663123379)
              ·
                refine ⟨26258627178887220994685069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17505751452591480663123379 26258627178887220994685069)
                ·
                  refine ⟨9846985192082707873006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26258627178887220994685069 9846985192082707873006901)
                  ·
                    refine ⟨923154861757753863094397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9846985192082707873006901 923154861757753863094397)
                    ·
                      rfl

theorem cell23_5393513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_5393513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393513 prefixEnd_5393513 := by exact prefixLift 5393513
  have htrace : WordTrace (prefixWord ++ tailWord_5393513) baseStart_5393513 baseEnd_5393513 := by
    simpa [prefixWord, tailWord_5393513, baseEnd_5393513] using wordTrace_append hprefix tailTrace_5393513
  have hstable : (prefixWord ++ tailWord_5393513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393513).length < 2 ^ (prefixWord ++ tailWord_5393513).sum := by decide
  have hdescent : baseEnd_5393513 < baseStart_5393513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393520 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2]
def baseStart_5393520 : Nat := 118140960795 + 5393520 * 2 ^ 59
def prefixEnd_5393520 : Nat := 4983230072969 + 3 ^ 40 * 5393520 * 2
def baseEnd_5393520 : Nat := 2769468179637843061895659

theorem tailTrace_5393520 : CollatzResearch.WordTrace tailWord_5393520 prefixEnd_5393520 2769468179637843061895659 := by
  unfold tailWord_5393520
  simp only [CollatzResearch.WordTrace]
  refine ⟨98358917710102827362709007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131145223613470436483612009 98358917710102827362709007)
  ·
    refine ⟨147538376565154241044063511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98358917710102827362709007 147538376565154241044063511)
    ·
      refine ⟨221307564847731361566095267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147538376565154241044063511 221307564847731361566095267)
      ·
        refine ⟨331961347271597042349142901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221307564847731361566095267 331961347271597042349142901)
        ·
          refine ⟨31121376306712222720232147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 331961347271597042349142901 31121376306712222720232147)
          ·
            refine ⟨46682064460068334080348221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31121376306712222720232147 46682064460068334080348221)
            ·
              refine ⟨17505774172525625280130583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46682064460068334080348221 17505774172525625280130583)
              ·
                refine ⟨26258661258788437920195875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17505774172525625280130583 26258661258788437920195875)
                ·
                  refine ⟨39387991888182656880293813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26258661258788437920195875 39387991888182656880293813)
                  ·
                    refine ⟨3692624239517124082527545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39387991888182656880293813 3692624239517124082527545)
                    ·
                      refine ⟨2769468179637843061895659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692624239517124082527545 2769468179637843061895659)
                      ·
                        rfl

theorem cell23_5393520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 5, 2].length) (baseStart_5393520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393520 prefixEnd_5393520 := by exact prefixLift 5393520
  have htrace : WordTrace (prefixWord ++ tailWord_5393520) baseStart_5393520 baseEnd_5393520 := by
    simpa [prefixWord, tailWord_5393520, baseEnd_5393520] using wordTrace_append hprefix tailTrace_5393520
  have hstable : (prefixWord ++ tailWord_5393520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393520).length < 2 ^ (prefixWord ++ tailWord_5393520).sum := by decide
  have hdescent : baseEnd_5393520 < baseStart_5393520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393534 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_5393534 : Nat := 118140960795 + 5393534 * 2 ^ 59
def prefixEnd_5393534 : Nat := 4983230072969 + 3 ^ 40 * 5393534 * 2
def baseEnd_5393534 : Nat := 307719485374111778568955

theorem tailTrace_5393534 : CollatzResearch.WordTrace tailWord_5393534 prefixEnd_5393534 307719485374111778568955 := by
  unfold tailWord_5393534
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589793255269366889553457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131145564028103290077618437 24589793255269366889553457)
  ·
    refine ⟨18442344941452025167165093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24589793255269366889553457 18442344941452025167165093)
    ·
      refine ⟨3457939676522254718843455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18442344941452025167165093 3457939676522254718843455)
      ·
        refine ⟨5186909514783382078265183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457939676522254718843455 5186909514783382078265183)
        ·
          refine ⟨7780364272175073117397775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5186909514783382078265183 7780364272175073117397775)
          ·
            refine ⟨11670546408262609676096663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780364272175073117397775 11670546408262609676096663)
            ·
              refine ⟨17505819612393914514144995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11670546408262609676096663 17505819612393914514144995)
              ·
                refine ⟨26258729418590871771217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17505819612393914514144995 26258729418590871771217493)
                ·
                  refine ⟨307719485374111778568955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26258729418590871771217493 307719485374111778568955)
                  ·
                    rfl

theorem cell23_5393534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_5393534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393534 prefixEnd_5393534 := by exact prefixLift 5393534
  have htrace : WordTrace (prefixWord ++ tailWord_5393534) baseStart_5393534 baseEnd_5393534 := by
    simpa [prefixWord, tailWord_5393534, baseEnd_5393534] using wordTrace_append hprefix tailTrace_5393534
  have hstable : (prefixWord ++ tailWord_5393534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393534).length < 2 ^ (prefixWord ++ tailWord_5393534).sum := by decide
  have hdescent : baseEnd_5393534 < baseStart_5393534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393544 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5393544 : Nat := 118140960795 + 5393544 * 2 ^ 59
def prefixEnd_5393544 : Nat := 4983230072969 + 3 ^ 40 * 5393544 * 2
def baseEnd_5393544 : Nat := 2769480503173550967995549

theorem tailTrace_5393544 : CollatzResearch.WordTrace tailWord_5393544 prefixEnd_5393544 2769480503173550967995549 := by
  unfold tailWord_5393544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98359355386059353412145843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131145807181412471216194457 98359355386059353412145843)
  ·
    refine ⟨147539033079089030118218765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98359355386059353412145843 147539033079089030118218765)
    ·
      refine ⟨55327137404658386294332037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147539033079089030118218765 55327137404658386294332037)
      ·
        refine ⟨10373838263373447430187257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55327137404658386294332037 10373838263373447430187257)
        ·
          refine ⟨7780378697530085572640443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10373838263373447430187257 7780378697530085572640443)
          ·
            refine ⟨11670568046295128358960665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780378697530085572640443 11670568046295128358960665)
            ·
              refine ⟨8752926034721346269220499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11670568046295128358960665 8752926034721346269220499)
              ·
                refine ⟨13129389052082019403830749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8752926034721346269220499 13129389052082019403830749)
                ·
                  refine ⟨4923520894530757276436531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13129389052082019403830749 4923520894530757276436531)
                  ·
                    refine ⟨7385281341796135914654797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4923520894530757276436531 7385281341796135914654797)
                    ·
                      refine ⟨2769480503173550967995549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7385281341796135914654797 2769480503173550967995549)
                      ·
                        rfl

theorem cell23_5393544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5393544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393544 prefixEnd_5393544 := by exact prefixLift 5393544
  have htrace : WordTrace (prefixWord ++ tailWord_5393544) baseStart_5393544 baseEnd_5393544 := by
    simpa [prefixWord, tailWord_5393544, baseEnd_5393544] using wordTrace_append hprefix tailTrace_5393544
  have hstable : (prefixWord ++ tailWord_5393544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393544).length < 2 ^ (prefixWord ++ tailWord_5393544).sum := by decide
  have hdescent : baseEnd_5393544 < baseStart_5393544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393560 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_5393560 : Nat := 118140960795 + 5393560 * 2 ^ 59
def prefixEnd_5393560 : Nat := 4983230072969 + 3 ^ 40 * 5393560 * 2
def baseEnd_5393560 : Nat := 923162906288007635131825

theorem tailTrace_5393560 : CollatzResearch.WordTrace tailWord_5393560 prefixEnd_5393560 923162906288007635131825 := by
  unfold tailWord_5393560
  simp only [CollatzResearch.WordTrace]
  refine ⟨98359647170030370778437067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131146196226707161037916089 98359647170030370778437067)
  ·
    refine ⟨147539470755045556167655601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98359647170030370778437067 147539470755045556167655601)
    ·
      refine ⟨110654603066284167125741701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147539470755045556167655601 110654603066284167125741701)
      ·
        refine ⟨20747738074928281336076569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110654603066284167125741701 20747738074928281336076569)
        ·
          refine ⟨15560803556196211002057427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20747738074928281336076569 15560803556196211002057427)
          ·
            refine ⟨23341205334294316503086141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560803556196211002057427 23341205334294316503086141)
            ·
              refine ⟨8752952000360368688657303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23341205334294316503086141 8752952000360368688657303)
              ·
                refine ⟨13129428000540553032985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8752952000360368688657303 13129428000540553032985955)
                ·
                  refine ⟨19694142000810829549478933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13129428000540553032985955 19694142000810829549478933)
                  ·
                    refine ⟨923162906288007635131825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19694142000810829549478933 923162906288007635131825)
                    ·
                      rfl

theorem cell23_5393560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_5393560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393560 prefixEnd_5393560 := by exact prefixLift 5393560
  have htrace : WordTrace (prefixWord ++ tailWord_5393560) baseStart_5393560 baseEnd_5393560 := by
    simpa [prefixWord, tailWord_5393560, baseEnd_5393560] using wordTrace_append hprefix tailTrace_5393560
  have hstable : (prefixWord ++ tailWord_5393560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393560).length < 2 ^ (prefixWord ++ tailWord_5393560).sum := by decide
  have hdescent : baseEnd_5393560 < baseStart_5393560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393573 : List Nat := [1, 3, 1, 2, 1, 5, 1, 9]
def baseStart_5393573 : Nat := 118140960795 + 5393573 * 2 ^ 59
def prefixEnd_5393573 : Nat := 4983230072969 + 3 ^ 40 * 5393573 * 2
def baseEnd_5393573 : Nat := 102573903485649309427145

theorem tailTrace_5393573 : CollatzResearch.WordTrace tailWord_5393573 prefixEnd_5393573 102573903485649309427145 := by
  unfold tailWord_5393573
  simp only [CollatzResearch.WordTrace]
  refine ⟨196719768489013644777097373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131146512326009096518064915 196719768489013644777097373)
  ·
    refine ⟨73769913183380116791411515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196719768489013644777097373 73769913183380116791411515)
    ·
      refine ⟨110654869775070175187117273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73769913183380116791411515 110654869775070175187117273)
      ·
        refine ⟨82991152331302631390337955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110654869775070175187117273 82991152331302631390337955)
        ·
          refine ⟨124486728496953947085506933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82991152331302631390337955 124486728496953947085506933)
          ·
            refine ⟨11670630796589432539266275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124486728496953947085506933 11670630796589432539266275)
            ·
              refine ⟨17505946194884148808899413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11670630796589432539266275 17505946194884148808899413)
              ·
                refine ⟨102573903485649309427145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17505946194884148808899413 102573903485649309427145)
                ·
                  rfl

theorem cell23_5393573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 9].length) (baseStart_5393573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393573 prefixEnd_5393573 := by exact prefixLift 5393573
  have htrace : WordTrace (prefixWord ++ tailWord_5393573) baseStart_5393573 baseEnd_5393573 := by
    simpa [prefixWord, tailWord_5393573, baseEnd_5393573] using wordTrace_append hprefix tailTrace_5393573
  have hstable : (prefixWord ++ tailWord_5393573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393573).length < 2 ^ (prefixWord ++ tailWord_5393573).sum := by decide
  have hdescent : baseEnd_5393573 < baseStart_5393573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393578 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5393578 : Nat := 118140960795 + 5393578 * 2 ^ 59
def prefixEnd_5393578 : Nat := 4983230072969 + 3 ^ 40 * 5393578 * 2
def baseEnd_5393578 : Nat := 2769497961515803834970393

theorem tailTrace_5393578 : CollatzResearch.WordTrace tailWord_5393578 prefixEnd_5393578 2769497961515803834970393 := by
  unfold tailWord_5393578
  simp only [CollatzResearch.WordTrace]
  refine ⟨49179987713498882657757347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131146633902663687087352925 49179987713498882657757347)
  ·
    refine ⟨73769981570248323986636021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49179987713498882657757347 73769981570248323986636021)
    ·
      refine ⟨6915935772210780373747127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73769981570248323986636021 6915935772210780373747127)
      ·
        refine ⟨10373903658316170560620691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915935772210780373747127 10373903658316170560620691)
        ·
          refine ⟨15560855487474255840931037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373903658316170560620691 15560855487474255840931037)
          ·
            refine ⟨5835320807802845940349139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15560855487474255840931037 5835320807802845940349139)
            ·
              refine ⟨8752981211704268910523709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835320807802845940349139 8752981211704268910523709)
              ·
                refine ⟨3282367954389100841446391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8752981211704268910523709 3282367954389100841446391)
                ·
                  refine ⟨4923551931583651262169587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282367954389100841446391 4923551931583651262169587)
                  ·
                    refine ⟨7385327897375476893254381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4923551931583651262169587 7385327897375476893254381)
                    ·
                      refine ⟨2769497961515803834970393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7385327897375476893254381 2769497961515803834970393)
                      ·
                        rfl

theorem cell23_5393578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5393578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393578 prefixEnd_5393578 := by exact prefixLift 5393578
  have htrace : WordTrace (prefixWord ++ tailWord_5393578) baseStart_5393578 baseEnd_5393578 := by
    simpa [prefixWord, tailWord_5393578, baseEnd_5393578] using wordTrace_append hprefix tailTrace_5393578
  have hstable : (prefixWord ++ tailWord_5393578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393578).length < 2 ^ (prefixWord ++ tailWord_5393578).sum := by decide
  have hdescent : baseEnd_5393578 < baseStart_5393578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393601 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5393601 : Nat := 118140960795 + 5393601 * 2 ^ 59
def prefixEnd_5393601 : Nat := 4983230072969 + 3 ^ 40 * 5393601 * 2
def baseEnd_5393601 : Nat := 2769509771570857244982787

theorem tailTrace_5393601 : CollatzResearch.WordTrace tailWord_5393601 prefixEnd_5393601 2769509771570857244982787 := by
  unfold tailWord_5393601
  simp only [CollatzResearch.WordTrace]
  refine ⟨196720789732912205559116657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131147193155274803706077771 196720789732912205559116657)
  ·
    refine ⟨147540592299684154169337493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196720789732912205559116657 147540592299684154169337493)
    ·
      refine ⟨6915965264047694726687695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147540592299684154169337493 6915965264047694726687695)
      ·
        refine ⟨10373947896071542090031543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915965264047694726687695 10373947896071542090031543)
        ·
          refine ⟨15560921844107313135047315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10373947896071542090031543 15560921844107313135047315)
          ·
            refine ⟨23341382766160969702570973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15560921844107313135047315 23341382766160969702570973)
            ·
              refine ⟨8753018537310363638464115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23341382766160969702570973 8753018537310363638464115)
              ·
                refine ⟨13129527805965545457696173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753018537310363638464115 13129527805965545457696173)
                ·
                  refine ⟨4923572927237079546636065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13129527805965545457696173 4923572927237079546636065)
                  ·
                    refine ⟨3692679695427809659977049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923572927237079546636065 3692679695427809659977049)
                    ·
                      refine ⟨2769509771570857244982787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692679695427809659977049 2769509771570857244982787)
                      ·
                        rfl

theorem cell23_5393601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5393601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393601 prefixEnd_5393601 := by exact prefixLift 5393601
  have htrace : WordTrace (prefixWord ++ tailWord_5393601) baseStart_5393601 baseEnd_5393601 := by
    simpa [prefixWord, tailWord_5393601, baseEnd_5393601] using wordTrace_append hprefix tailTrace_5393601
  have hstable : (prefixWord ++ tailWord_5393601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393601).length < 2 ^ (prefixWord ++ tailWord_5393601).sum := by decide
  have hdescent : baseEnd_5393601 < baseStart_5393601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393652 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5393652 : Nat := 118140960795 + 5393652 * 2 ^ 59
def prefixEnd_5393652 : Nat := 4983230072969 + 3 ^ 40 * 5393652 * 2
def baseEnd_5393652 : Nat := 2769535959084236545445053

theorem tailTrace_5393652 : CollatzResearch.WordTrace tailWord_5393652 prefixEnd_5393652 2769535959084236545445053 := by
  unfold tailWord_5393652
  simp only [CollatzResearch.WordTrace]
  refine ⟨98361324927863720634611605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131148433237151627512815473 98361324927863720634611605)
  ·
    refine ⟨4610687105993611904747419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98361324927863720634611605 4610687105993611904747419)
    ·
      refine ⟨6916030658990417857121129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610687105993611904747419 6916030658990417857121129)
      ·
        refine ⟨5187022994242813392840847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6916030658990417857121129 5187022994242813392840847)
        ·
          refine ⟨7780534491364220089261271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187022994242813392840847 7780534491364220089261271)
          ·
            refine ⟨11670801737046330133891907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780534491364220089261271 11670801737046330133891907)
            ·
              refine ⟨17506202605569495200837861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11670801737046330133891907 17506202605569495200837861)
              ·
                refine ⟨3282412988544280350157099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17506202605569495200837861 3282412988544280350157099)
                ·
                  refine ⟨4923619482816420525235649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282412988544280350157099 4923619482816420525235649)
                  ·
                    refine ⟨3692714612112315393926737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923619482816420525235649 3692714612112315393926737)
                    ·
                      refine ⟨2769535959084236545445053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692714612112315393926737 2769535959084236545445053)
                      ·
                        rfl

theorem cell23_5393652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5393652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393652 prefixEnd_5393652 := by exact prefixLift 5393652
  have htrace : WordTrace (prefixWord ++ tailWord_5393652) baseStart_5393652 baseEnd_5393652 := by
    simpa [prefixWord, tailWord_5393652, baseEnd_5393652] using wordTrace_append hprefix tailTrace_5393652
  have hstable : (prefixWord ++ tailWord_5393652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393652).length < 2 ^ (prefixWord ++ tailWord_5393652).sum := by decide
  have hdescent : baseEnd_5393652 < baseStart_5393652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393725 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5393725 : Nat := 118140960795 + 5393725 * 2 ^ 59
def prefixEnd_5393725 : Nat := 4983230072969 + 3 ^ 40 * 5393725 * 2
def baseEnd_5393725 : Nat := 2769573443172014759832217

theorem tailTrace_5393725 : CollatzResearch.WordTrace tailWord_5393725 prefixEnd_5393725 2769573443172014759832217 := by
  unfold tailWord_5393725
  simp only [CollatzResearch.WordTrace]
  refine ⟨196725312384462974736630629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131150208256308649824420419 196725312384462974736630629)
  ·
    refine ⟨36885996072086807763118243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196725312384462974736630629 36885996072086807763118243)
    ·
      refine ⟨55328994108130211644677365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36885996072086807763118243 55328994108130211644677365)
      ·
        refine ⟨5187093197637207341688503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55328994108130211644677365 5187093197637207341688503)
        ·
          refine ⟨7780639796455811012532755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187093197637207341688503 7780639796455811012532755)
          ·
            refine ⟨11670959694683716518799133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780639796455811012532755 11670959694683716518799133)
            ·
              refine ⟨4376609885506393694549675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11670959694683716518799133 4376609885506393694549675)
              ·
                refine ⟨6564914828259590541824513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376609885506393694549675 6564914828259590541824513)
                ·
                  refine ⟨4923686121194692906368385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6564914828259590541824513 4923686121194692906368385)
                  ·
                    refine ⟨3692764590896019679776289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923686121194692906368385 3692764590896019679776289)
                    ·
                      refine ⟨2769573443172014759832217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692764590896019679776289 2769573443172014759832217)
                      ·
                        rfl

theorem cell23_5393725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5393725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393725 prefixEnd_5393725 := by exact prefixLift 5393725
  have htrace : WordTrace (prefixWord ++ tailWord_5393725) baseStart_5393725 baseEnd_5393725 := by
    simpa [prefixWord, tailWord_5393725, baseEnd_5393725] using wordTrace_append hprefix tailTrace_5393725
  have hstable : (prefixWord ++ tailWord_5393725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393725).length < 2 ^ (prefixWord ++ tailWord_5393725).sum := by decide
  have hdescent : baseEnd_5393725 < baseStart_5393725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393824 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2]
def baseStart_5393824 : Nat := 118140960795 + 5393824 * 2 ^ 59
def prefixEnd_5393824 : Nat := 4983230072969 + 3 ^ 40 * 5393824 * 2
def baseEnd_5393824 : Nat := 2769624277756809872494261

theorem tailTrace_5393824 : CollatzResearch.WordTrace tailWord_5393824 prefixEnd_5393824 2769624277756809872494261 := by
  unfold tailWord_5393824
  simp only [CollatzResearch.WordTrace]
  refine ⟨98364461605552157322242263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131152615474069543096323017 98364461605552157322242263)
  ·
    refine ⟨147546692408328235983363395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98364461605552157322242263 147546692408328235983363395)
    ·
      refine ⟨221320038612492353975045093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147546692408328235983363395 221320038612492353975045093)
      ·
        refine ⟨41497507239842316370320955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221320038612492353975045093 41497507239842316370320955)
        ·
          refine ⟨62246260859763474555481433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41497507239842316370320955 62246260859763474555481433)
          ·
            refine ⟨46684695644822605916611075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62246260859763474555481433 46684695644822605916611075)
            ·
              refine ⟨70027043467233908874916613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46684695644822605916611075 70027043467233908874916613)
              ·
                refine ⟨13130070650106357914046865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70027043467233908874916613 13130070650106357914046865)
                ·
                  refine ⟨9847552987579768435535149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13130070650106357914046865 9847552987579768435535149)
                  ·
                    refine ⟨3692832370342413163325681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9847552987579768435535149 3692832370342413163325681)
                    ·
                      refine ⟨2769624277756809872494261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692832370342413163325681 2769624277756809872494261)
                      ·
                        rfl

theorem cell23_5393824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_5393824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393824 prefixEnd_5393824 := by exact prefixLift 5393824
  have htrace : WordTrace (prefixWord ++ tailWord_5393824) baseStart_5393824 baseEnd_5393824 := by
    simpa [prefixWord, tailWord_5393824, baseEnd_5393824] using wordTrace_append hprefix tailTrace_5393824
  have hstable : (prefixWord ++ tailWord_5393824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393824).length < 2 ^ (prefixWord ++ tailWord_5393824).sum := by decide
  have hdescent : baseEnd_5393824 < baseStart_5393824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393847 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 6]
def baseStart_5393847 : Nat := 118140960795 + 5393847 * 2 ^ 59
def prefixEnd_5393847 : Nat := 4983230072969 + 3 ^ 40 * 5393847 * 2
def baseEnd_5393847 : Nat := 923212029270621094168885

theorem tailTrace_5393847 : CollatzResearch.WordTrace tailWord_5393847 prefixEnd_5393847 923212029270621094168885 := by
  unfold tailWord_5393847
  simp only [CollatzResearch.WordTrace]
  refine ⟨196729762090020989572571795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131153174726680659715047863 196729762090020989572571795)
  ·
    refine ⟨295094643135031484358857693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196729762090020989572571795 295094643135031484358857693)
    ·
      refine ⟨110660491175636806634571635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295094643135031484358857693 110660491175636806634571635)
      ·
        refine ⟨165990736763455209951857453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110660491175636806634571635 165990736763455209951857453)
        ·
          refine ⟨62246526286295703731946545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165990736763455209951857453 62246526286295703731946545)
          ·
            refine ⟨46684894714721777798959909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62246526286295703731946545 46684894714721777798959909)
            ·
              refine ⟨8753417759010333337304983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46684894714721777798959909 8753417759010333337304983)
              ·
                refine ⟨13130126638515500005957475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753417759010333337304983 13130126638515500005957475)
                ·
                  refine ⟨19695189957773250008936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130126638515500005957475 19695189957773250008936213)
                  ·
                    refine ⟨923212029270621094168885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19695189957773250008936213 923212029270621094168885)
                    ·
                      rfl

theorem cell23_5393847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_5393847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393847 prefixEnd_5393847 := by exact prefixLift 5393847
  have htrace : WordTrace (prefixWord ++ tailWord_5393847) baseStart_5393847 baseEnd_5393847 := by
    simpa [prefixWord, tailWord_5393847, baseEnd_5393847] using wordTrace_append hprefix tailTrace_5393847
  have hstable : (prefixWord ++ tailWord_5393847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393847).length < 2 ^ (prefixWord ++ tailWord_5393847).sum := by decide
  have hdescent : baseEnd_5393847 < baseStart_5393847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393854 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_5393854 : Nat := 118140960795 + 5393854 * 2 ^ 59
def prefixEnd_5393854 : Nat := 4983230072969 + 3 ^ 40 * 5393854 * 2
def baseEnd_5393854 : Nat := 2769639682176444755119123

theorem tailTrace_5393854 : CollatzResearch.WordTrace tailWord_5393854 prefixEnd_5393854 2769639682176444755119123 := by
  unfold tailWord_5393854
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591252175124453721009577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131153344933997086512051077 24591252175124453721009577)
  ·
    refine ⟨18443439131343340290757183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24591252175124453721009577 18443439131343340290757183)
    ·
      refine ⟨27665158697015010436135775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18443439131343340290757183 27665158697015010436135775)
      ·
        refine ⟨41497738045522515654203663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27665158697015010436135775 41497738045522515654203663)
        ·
          refine ⟨62246607068283773481305495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41497738045522515654203663 62246607068283773481305495)
          ·
            refine ⟨93369910602425660221958243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62246607068283773481305495 93369910602425660221958243)
            ·
              refine ⟨140054865903638490332937365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93369910602425660221958243 140054865903638490332937365)
              ·
                refine ⟨6565071839233054234356439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140054865903638490332937365 6565071839233054234356439)
                ·
                  refine ⟨9847607758849581351534659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565071839233054234356439 9847607758849581351534659)
                  ·
                    refine ⟨14771411638274372027301989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9847607758849581351534659 14771411638274372027301989)
                    ·
                      refine ⟨2769639682176444755119123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14771411638274372027301989 2769639682176444755119123)
                      ·
                        rfl

theorem cell23_5393854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_5393854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393854 prefixEnd_5393854 := by exact prefixLift 5393854
  have htrace : WordTrace (prefixWord ++ tailWord_5393854) baseStart_5393854 baseEnd_5393854 := by
    simpa [prefixWord, tailWord_5393854, baseEnd_5393854] using wordTrace_append hprefix tailTrace_5393854
  have hstable : (prefixWord ++ tailWord_5393854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393854).length < 2 ^ (prefixWord ++ tailWord_5393854).sum := by decide
  have hdescent : baseEnd_5393854 < baseStart_5393854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393867 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4]
def baseStart_5393867 : Nat := 118140960795 + 5393867 * 2 ^ 59
def prefixEnd_5393867 : Nat := 4983230072969 + 3 ^ 40 * 5393867 * 2
def baseEnd_5393867 : Nat := 2769646357424953204256563

theorem tailTrace_5393867 : CollatzResearch.WordTrace tailWord_5393867 prefixEnd_5393867 2769646357424953204256563 := by
  unfold tailWord_5393867
  simp only [CollatzResearch.WordTrace]
  refine ⟨196730491549948532988299855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131153661033299021992199903 196730491549948532988299855)
  ·
    refine ⟨295095737324922799482449783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196730491549948532988299855 295095737324922799482449783)
    ·
      refine ⟨442643605987384199223674675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295095737324922799482449783 442643605987384199223674675)
      ·
        refine ⟨663965408981076298835512013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442643605987384199223674675 663965408981076298835512013)
        ·
          refine ⟨248987028367903612063317005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 663965408981076298835512013 248987028367903612063317005)
          ·
            refine ⟨93370135637963854523743877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248987028367903612063317005 93370135637963854523743877)
            ·
              refine ⟨17506900432118222723201977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93370135637963854523743877 17506900432118222723201977)
              ·
                refine ⟨13130175324088667042401483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17506900432118222723201977 13130175324088667042401483)
                ·
                  refine ⟨19695262986133000563602225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130175324088667042401483 19695262986133000563602225)
                  ·
                    refine ⟨14771447239599750422701669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19695262986133000563602225 14771447239599750422701669)
                    ·
                      refine ⟨2769646357424953204256563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14771447239599750422701669 2769646357424953204256563)
                      ·
                        rfl

theorem cell23_5393867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 4].length) (baseStart_5393867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393867 prefixEnd_5393867 := by exact prefixLift 5393867
  have htrace : WordTrace (prefixWord ++ tailWord_5393867) baseStart_5393867 baseEnd_5393867 := by
    simpa [prefixWord, tailWord_5393867, baseEnd_5393867] using wordTrace_append hprefix tailTrace_5393867
  have hstable : (prefixWord ++ tailWord_5393867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393867).length < 2 ^ (prefixWord ++ tailWord_5393867).sum := by decide
  have hdescent : baseEnd_5393867 < baseStart_5393867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393881 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_5393881 : Nat := 118140960795 + 5393881 * 2 ^ 59
def prefixEnd_5393881 : Nat := 4983230072969 + 3 ^ 40 * 5393881 * 2
def baseEnd_5393881 : Nat := 923217848718038716493833

theorem tailTrace_5393881 : CollatzResearch.WordTrace tailWord_5393881 prefixEnd_5393881 923217848718038716493833 := by
  unfold tailWord_5393881
  simp only [CollatzResearch.WordTrace]
  refine ⟨196731002171897813379309497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131154001447931875586206331 196731002171897813379309497)
  ·
    refine ⟨147548251628923360034482123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196731002171897813379309497 147548251628923360034482123)
    ·
      refine ⟨221322377443385040051723185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147548251628923360034482123 221322377443385040051723185)
      ·
        refine ⟨165991783082538780038792389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221322377443385040051723185 165991783082538780038792389)
        ·
          refine ⟨31123459327976021257273573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165991783082538780038792389 31123459327976021257273573)
          ·
            refine ⟨5835648623995503985738795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31123459327976021257273573 5835648623995503985738795)
            ·
              refine ⟨8753472935993255978608193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835648623995503985738795 8753472935993255978608193)
              ·
                refine ⟨6565104701994941983956145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8753472935993255978608193 6565104701994941983956145)
                ·
                  refine ⟨4923828526496206487967109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565104701994941983956145 4923828526496206487967109)
                  ·
                    refine ⟨923217848718038716493833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923828526496206487967109 923217848718038716493833)
                    ·
                      rfl

theorem cell23_5393881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_5393881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393881 prefixEnd_5393881 := by exact prefixLift 5393881
  have htrace : WordTrace (prefixWord ++ tailWord_5393881) baseStart_5393881 baseEnd_5393881 := by
    simpa [prefixWord, tailWord_5393881, baseEnd_5393881] using wordTrace_append hprefix tailTrace_5393881
  have hstable : (prefixWord ++ tailWord_5393881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393881).length < 2 ^ (prefixWord ++ tailWord_5393881).sum := by decide
  have hdescent : baseEnd_5393881 < baseStart_5393881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393898 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_5393898 : Nat := 118140960795 + 5393898 * 2 ^ 59
def prefixEnd_5393898 : Nat := 4983230072969 + 3 ^ 40 * 5393898 * 2
def baseEnd_5393898 : Nat := 923220758441747527656307

theorem tailTrace_5393898 : CollatzResearch.WordTrace tailWord_5393898 prefixEnd_5393898 923220758441747527656307 := by
  unfold tailWord_5393898
  simp only [CollatzResearch.WordTrace]
  refine ⟨49182905553209056320669587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131154414808557483521785565 49182905553209056320669587)
  ·
    refine ⟨73774358329813584481004381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49182905553209056320669587 73774358329813584481004381)
    ·
      refine ⟨27665384373680094180376643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73774358329813584481004381 27665384373680094180376643)
      ·
        refine ⟨41498076560520141270564965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27665384373680094180376643 41498076560520141270564965)
        ·
          refine ⟨7780889355097526488230931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41498076560520141270564965 7780889355097526488230931)
          ·
            refine ⟨11671334032646289732346397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7780889355097526488230931 11671334032646289732346397)
            ·
              refine ⟨4376750262242358649629899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11671334032646289732346397 4376750262242358649629899)
              ·
                refine ⟨6565125393363537974444849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376750262242358649629899 6565125393363537974444849)
                ·
                  refine ⟨4923844045022653480833637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565125393363537974444849 4923844045022653480833637)
                  ·
                    refine ⟨923220758441747527656307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923844045022653480833637 923220758441747527656307)
                    ·
                      rfl

theorem cell23_5393898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_5393898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393898 prefixEnd_5393898 := by exact prefixLift 5393898
  have htrace : WordTrace (prefixWord ++ tailWord_5393898) baseStart_5393898 baseEnd_5393898 := by
    simpa [prefixWord, tailWord_5393898, baseEnd_5393898] using wordTrace_append hprefix tailTrace_5393898
  have hstable : (prefixWord ++ tailWord_5393898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393898).length < 2 ^ (prefixWord ++ tailWord_5393898).sum := by decide
  have hdescent : baseEnd_5393898 < baseStart_5393898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393904 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_5393904 : Nat := 118140960795 + 5393904 * 2 ^ 59
def prefixEnd_5393904 : Nat := 4983230072969 + 3 ^ 40 * 5393904 * 2
def baseEnd_5393904 : Nat := 2769665356209169559493893

theorem tailTrace_5393904 : CollatzResearch.WordTrace tailWord_5393904 prefixEnd_5393904 2769665356209169559493893 := by
  unfold tailWord_5393904
  simp only [CollatzResearch.WordTrace]
  refine ⟨98365920525407244153698383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131154560700542992204931177 98365920525407244153698383)
  ·
    refine ⟨147548880788110866230547575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98365920525407244153698383 147548880788110866230547575)
    ·
      refine ⟨221323321182166299345821363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147548880788110866230547575 221323321182166299345821363)
      ·
        refine ⟨331984981773249449018732045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221323321182166299345821363 331984981773249449018732045)
        ·
          refine ⟨124494368164968543382024517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331984981773249449018732045 124494368164968543382024517)
          ·
            refine ⟨23342694030931601884129597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124494368164968543382024517 23342694030931601884129597)
            ·
              refine ⟨8753510261599350706548599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23342694030931601884129597 8753510261599350706548599)
              ·
                refine ⟨13130265392399026059822899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753510261599350706548599 13130265392399026059822899)
                ·
                  refine ⟨19695398088598539089734349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130265392399026059822899 19695398088598539089734349)
                  ·
                    refine ⟨7385774283224452158650381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19695398088598539089734349 7385774283224452158650381)
                    ·
                      refine ⟨2769665356209169559493893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7385774283224452158650381 2769665356209169559493893)
                      ·
                        rfl

theorem cell23_5393904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_5393904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393904 prefixEnd_5393904 := by exact prefixLift 5393904
  have htrace : WordTrace (prefixWord ++ tailWord_5393904) baseStart_5393904 baseEnd_5393904 := by
    simpa [prefixWord, tailWord_5393904, baseEnd_5393904] using wordTrace_append hprefix tailTrace_5393904
  have hstable : (prefixWord ++ tailWord_5393904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393904).length < 2 ^ (prefixWord ++ tailWord_5393904).sum := by decide
  have hdescent : baseEnd_5393904 < baseStart_5393904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393917 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_5393917 : Nat := 118140960795 + 5393917 * 2 ^ 59
def prefixEnd_5393917 : Nat := 4983230072969 + 3 ^ 40 * 5393917 * 2
def baseEnd_5393917 : Nat := 2769672031457678008631333

theorem tailTrace_5393917 : CollatzResearch.WordTrace tailWord_5393917 prefixEnd_5393917 2769672031457678008631333 := by
  unfold tailWord_5393917
  simp only [CollatzResearch.WordTrace]
  refine ⟨196732315199767391527620005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131154876799844927685080003 196732315199767391527620005)
  ·
    refine ⟨36887309099956385911428751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196732315199767391527620005 36887309099956385911428751)
    ·
      refine ⟨55330963649934578867143127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36887309099956385911428751 55330963649934578867143127)
      ·
        refine ⟨82996445474901868300714691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55330963649934578867143127 82996445474901868300714691)
        ·
          refine ⟨124494668212352802451072037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82996445474901868300714691 124494668212352802451072037)
          ·
            refine ⟨23342750289816150459576007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124494668212352802451072037 23342750289816150459576007)
            ·
              refine ⟨35014125434724225689364011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23342750289816150459576007 35014125434724225689364011)
              ·
                refine ⟨52521188152086338534046017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35014125434724225689364011 52521188152086338534046017)
                ·
                  refine ⟨39390891114064753900534513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52521188152086338534046017 39390891114064753900534513)
                  ·
                    refine ⟨29543168335548565425400885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39390891114064753900534513 29543168335548565425400885)
                    ·
                      refine ⟨2769672031457678008631333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29543168335548565425400885 2769672031457678008631333)
                      ·
                        rfl

theorem cell23_5393917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_5393917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393917 prefixEnd_5393917 := by exact prefixLift 5393917
  have htrace : WordTrace (prefixWord ++ tailWord_5393917) baseStart_5393917 baseEnd_5393917 := by
    simpa [prefixWord, tailWord_5393917, baseEnd_5393917] using wordTrace_append hprefix tailTrace_5393917
  have hstable : (prefixWord ++ tailWord_5393917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393917).length < 2 ^ (prefixWord ++ tailWord_5393917).sum := by decide
  have hdescent : baseEnd_5393917 < baseStart_5393917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393922 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5393922 : Nat := 118140960795 + 5393922 * 2 ^ 59
def prefixEnd_5393922 : Nat := 4983230072969 + 3 ^ 40 * 5393922 * 2
def baseEnd_5393922 : Nat := 2769674598860950489068811

theorem tailTrace_5393922 : CollatzResearch.WordTrace tailWord_5393922 prefixEnd_5393922 2769674598860950489068811 := by
  unfold tailWord_5393922
  simp only [CollatzResearch.WordTrace]
  refine ⟨49183124391187319345388005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131154998376499518254368013 49183124391187319345388005)
  ·
    refine ⟨9221835823347622377260251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49183124391187319345388005 9221835823347622377260251)
    ·
      refine ⟨13832753735021433565890377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9221835823347622377260251 13832753735021433565890377)
      ·
        refine ⟨10374565301266075174417783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13832753735021433565890377 10374565301266075174417783)
        ·
          refine ⟨15561847951899112761626675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374565301266075174417783 15561847951899112761626675)
          ·
            refine ⟨23342771927848669142440013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561847951899112761626675 23342771927848669142440013)
            ·
              refine ⟨8753539472943250928415005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23342771927848669142440013 8753539472943250928415005)
              ·
                refine ⟨3282577302353719098155627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8753539472943250928415005 3282577302353719098155627)
                ·
                  refine ⟨4923865953530578647233441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282577302353719098155627 4923865953530578647233441)
                  ·
                    refine ⟨3692899465147933985425081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4923865953530578647233441 3692899465147933985425081)
                    ·
                      refine ⟨2769674598860950489068811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3692899465147933985425081 2769674598860950489068811)
                      ·
                        rfl

theorem cell23_5393922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5393922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393922 prefixEnd_5393922 := by exact prefixLift 5393922
  have htrace : WordTrace (prefixWord ++ tailWord_5393922) baseStart_5393922 baseEnd_5393922 := by
    simpa [prefixWord, tailWord_5393922, baseEnd_5393922] using wordTrace_append hprefix tailTrace_5393922
  have hstable : (prefixWord ++ tailWord_5393922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393922).length < 2 ^ (prefixWord ++ tailWord_5393922).sum := by decide
  have hdescent : baseEnd_5393922 < baseStart_5393922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393955 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 2, 1, 3]
def baseStart_5393955 : Nat := 118140960795 + 5393955 * 2 ^ 59
def prefixEnd_5393955 : Nat := 4983230072969 + 3 ^ 40 * 5393955 * 2
def baseEnd_5393955 : Nat := 2769691543722548859956159

theorem tailTrace_5393955 : CollatzResearch.WordTrace tailWord_5393955 prefixEnd_5393955 2769691543722548859956159 := by
  unfold tailWord_5393955
  simp only [CollatzResearch.WordTrace]
  refine ⟨196733701173629724017503319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131155800782419816011668879 196733701173629724017503319)
  ·
    refine ⟨295100551760444586026254979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196733701173629724017503319 295100551760444586026254979)
    ·
      refine ⟨442650827640666879039382469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295100551760444586026254979 442650827640666879039382469)
      ·
        refine ⟨82997030182625039819884213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442650827640666879039382469 82997030182625039819884213)
        ·
          refine ⟨7780971579621097483114145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82997030182625039819884213 7780971579621097483114145)
          ·
            refine ⟨5835728684715823112335609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780971579621097483114145 5835728684715823112335609)
            ·
              refine ⟨4376796513536867334251707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5835728684715823112335609 4376796513536867334251707)
              ·
                refine ⟨6565194770305301001377561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376796513536867334251707 6565194770305301001377561)
                ·
                  refine ⟨4923896077728975751033171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565194770305301001377561 4923896077728975751033171)
                  ·
                    refine ⟨7385844116593463626549757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4923896077728975751033171 7385844116593463626549757)
                    ·
                      refine ⟨2769691543722548859956159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7385844116593463626549757 2769691543722548859956159)
                      ·
                        rfl

theorem cell23_5393955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_5393955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393955 prefixEnd_5393955 := by exact prefixLift 5393955
  have htrace : WordTrace (prefixWord ++ tailWord_5393955) baseStart_5393955 baseEnd_5393955 := by
    simpa [prefixWord, tailWord_5393955, baseEnd_5393955] using wordTrace_append hprefix tailTrace_5393955
  have hstable : (prefixWord ++ tailWord_5393955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393955).length < 2 ^ (prefixWord ++ tailWord_5393955).sum := by decide
  have hdescent : baseEnd_5393955 < baseStart_5393955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393957 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_5393957 : Nat := 118140960795 + 5393957 * 2 ^ 59
def prefixEnd_5393957 : Nat := 4983230072969 + 3 ^ 40 * 5393957 * 2
def baseEnd_5393957 : Nat := 2769692570683857852131149

theorem tailTrace_5393957 : CollatzResearch.WordTrace tailWord_5393957 prefixEnd_5393957 2769692570683857852131149 := by
  unfold tailWord_5393957
  simp only [CollatzResearch.WordTrace]
  refine ⟨196733774119622478359076125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131155849413081652239384083 196733774119622478359076125)
  ·
    refine ⟨73775165294858429384653547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196733774119622478359076125 73775165294858429384653547)
    ·
      refine ⟨110662747942287644076980321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73775165294858429384653547 110662747942287644076980321)
      ·
        refine ⟨82997060956715733057735241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110662747942287644076980321 82997060956715733057735241)
        ·
          refine ⟨62247795717536799793301431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82997060956715733057735241 62247795717536799793301431)
          ·
            refine ⟨93371693576305199689952147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62247795717536799793301431 93371693576305199689952147)
            ·
              refine ⟨140057540364457799534928221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93371693576305199689952147 140057540364457799534928221)
              ·
                refine ⟨52521577636671674825598083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140057540364457799534928221 52521577636671674825598083)
                ·
                  refine ⟨78782366455007512238397125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52521577636671674825598083 78782366455007512238397125)
                  ·
                    refine ⟨14771693710313908544699461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78782366455007512238397125 14771693710313908544699461)
                    ·
                      refine ⟨2769692570683857852131149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14771693710313908544699461 2769692570683857852131149)
                      ·
                        rfl

theorem cell23_5393957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_5393957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393957 prefixEnd_5393957 := by exact prefixLift 5393957
  have htrace : WordTrace (prefixWord ++ tailWord_5393957) baseStart_5393957 baseEnd_5393957 := by
    simpa [prefixWord, tailWord_5393957, baseEnd_5393957] using wordTrace_append hprefix tailTrace_5393957
  have hstable : (prefixWord ++ tailWord_5393957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393957).length < 2 ^ (prefixWord ++ tailWord_5393957).sum := by decide
  have hdescent : baseEnd_5393957 < baseStart_5393957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393984 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 5]
def baseStart_5393984 : Nat := 118140960795 + 5393984 * 2 ^ 59
def prefixEnd_5393984 : Nat := 4983230072969 + 3 ^ 40 * 5393984 * 2
def baseEnd_5393984 : Nat := 307745159406836582943725

theorem tailTrace_5393984 : CollatzResearch.WordTrace tailWord_5393984 prefixEnd_5393984 307745159406836582943725 := by
  unfold tailWord_5393984
  simp only [CollatzResearch.WordTrace]
  refine ⟨98367379445262330985154503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131156505927016441313539337 98367379445262330985154503)
  ·
    refine ⟨147551069167893496477731755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98367379445262330985154503 147551069167893496477731755)
    ·
      refine ⟨221326603751840244716597633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147551069167893496477731755 221326603751840244716597633)
      ·
        refine ⟨165994952813880183537448225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221326603751840244716597633 165994952813880183537448225)
        ·
          refine ⟨124496214610410137653086169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165994952813880183537448225 124496214610410137653086169)
          ·
            refine ⟨93372160957807603239814627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124496214610410137653086169 93372160957807603239814627)
            ·
              refine ⟨140058241436711404859721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93372160957807603239814627 140058241436711404859721941)
              ·
                refine ⟨3282615033672923551399733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140058241436711404859721941 3282615033672923551399733)
                ·
                  refine ⟨307745159406836582943725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3282615033672923551399733 307745159406836582943725)
                  ·
                    rfl

theorem cell23_5393984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 5].length) (baseStart_5393984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393984 prefixEnd_5393984 := by exact prefixLift 5393984
  have htrace : WordTrace (prefixWord ++ tailWord_5393984) baseStart_5393984 baseEnd_5393984 := by
    simpa [prefixWord, tailWord_5393984, baseEnd_5393984] using wordTrace_append hprefix tailTrace_5393984
  have hstable : (prefixWord ++ tailWord_5393984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393984).length < 2 ^ (prefixWord ++ tailWord_5393984).sum := by decide
  have hdescent : baseEnd_5393984 < baseStart_5393984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5393994 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_5393994 : Nat := 118140960795 + 5393994 * 2 ^ 59
def prefixEnd_5393994 : Nat := 4983230072969 + 3 ^ 40 * 5393994 * 2
def baseEnd_5393994 : Nat := 2769711569468074207368479

theorem tailTrace_5393994 : CollatzResearch.WordTrace tailWord_5393994 prefixEnd_5393994 2769711569468074207368479 := by
  unfold tailWord_5393994
  simp only [CollatzResearch.WordTrace]
  refine ⟨49183780905122108419543259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131156749080325622452115357 49183780905122108419543259)
  ·
    refine ⟨73775671357683162629314889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49183780905122108419543259 73775671357683162629314889)
    ·
      refine ⟨55331753518262371971986167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73775671357683162629314889 55331753518262371971986167)
      ·
        refine ⟨82997630277393557957979251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55331753518262371971986167 82997630277393557957979251)
        ·
          refine ⟨124496445416090336936968877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82997630277393557957979251 124496445416090336936968877)
          ·
            refine ⟨46686167031033876351363329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124496445416090336936968877 46686167031033876351363329)
            ·
              refine ⟨35014625273275407263522497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46686167031033876351363329 35014625273275407263522497)
              ·
                refine ⟨26260968954956555447641873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35014625273275407263522497 26260968954956555447641873)
                ·
                  refine ⟨19695726716217416585731405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26260968954956555447641873 19695726716217416585731405)
                  ·
                    refine ⟨7385897518581531219649277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19695726716217416585731405 7385897518581531219649277)
                    ·
                      refine ⟨2769711569468074207368479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7385897518581531219649277 2769711569468074207368479)
                      ·
                        rfl

theorem cell23_5393994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_5393994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5393994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5393994 prefixEnd_5393994 := by exact prefixLift 5393994
  have htrace : WordTrace (prefixWord ++ tailWord_5393994) baseStart_5393994 baseEnd_5393994 := by
    simpa [prefixWord, tailWord_5393994, baseEnd_5393994] using wordTrace_append hprefix tailTrace_5393994
  have hstable : (prefixWord ++ tailWord_5393994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5393994).length < 2 ^ (prefixWord ++ tailWord_5393994).sum := by decide
  have hdescent : baseEnd_5393994 < baseStart_5393994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5393994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394044 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_5394044 : Nat := 118140960795 + 5394044 * 2 ^ 59
def prefixEnd_5394044 : Nat := 4983230072969 + 3 ^ 40 * 5394044 * 2
def baseEnd_5394044 : Nat := 923245747833599670581083

theorem tailTrace_5394044 : CollatzResearch.WordTrace tailWord_5394044 prefixEnd_5394044 923245747833599670581083 := by
  unfold tailWord_5394044
  simp only [CollatzResearch.WordTrace]
  refine ⟨98368473635153646108746593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131157964846871528144995457 98368473635153646108746593)
  ·
    refine ⟨73776355226365234581559945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98368473635153646108746593 73776355226365234581559945)
    ·
      refine ⟨55332266419773925936169959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73776355226365234581559945 55332266419773925936169959)
      ·
        refine ⟨82998399629660888904254939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55332266419773925936169959 82998399629660888904254939)
        ·
          refine ⟨124497599444491333356382409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82998399629660888904254939 124497599444491333356382409)
          ·
            refine ⟨93373199583368500017286807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124497599444491333356382409 93373199583368500017286807)
            ·
              refine ⟨140059799375052750025930211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93373199583368500017286807 140059799375052750025930211)
              ·
                refine ⟨210089699062579125038895317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140059799375052750025930211 210089699062579125038895317)
                ·
                  refine ⟨4923977321779198243099109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 210089699062579125038895317 4923977321779198243099109)
                  ·
                    refine ⟨923245747833599670581083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4923977321779198243099109 923245747833599670581083)
                    ·
                      rfl

theorem cell23_5394044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_5394044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394044 prefixEnd_5394044 := by exact prefixLift 5394044
  have htrace : WordTrace (prefixWord ++ tailWord_5394044) baseStart_5394044 baseEnd_5394044 := by
    simpa [prefixWord, tailWord_5394044, baseEnd_5394044] using wordTrace_append hprefix tailTrace_5394044
  have hstable : (prefixWord ++ tailWord_5394044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394044).length < 2 ^ (prefixWord ++ tailWord_5394044).sum := by decide
  have hdescent : baseEnd_5394044 < baseStart_5394044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394078 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5394078 : Nat := 118140960795 + 5394078 * 2 ^ 59
def prefixEnd_5394078 : Nat := 4983230072969 + 3 ^ 40 * 5394078 * 2
def baseEnd_5394078 : Nat := 923251567281017292906031

theorem tailTrace_5394078 : CollatzResearch.WordTrace tailWord_5394078 prefixEnd_5394078 923251567281017292906031 := by
  unfold tailWord_5394078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592273419023014503028861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131158791568122744016153925 24592273419023014503028861)
  ·
    refine ⟨9222102532133630438635823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24592273419023014503028861 9222102532133630438635823)
    ·
      refine ⟨13833153798200445657953735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222102532133630438635823 13833153798200445657953735)
      ·
        refine ⟨20749730697300668486930603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13833153798200445657953735 20749730697300668486930603)
        ·
          refine ⟨31124596045951002730395905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20749730697300668486930603 31124596045951002730395905)
          ·
            refine ⟨23343447034463252047796929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31124596045951002730395905 23343447034463252047796929)
            ·
              refine ⟨17507585275847439035847697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23343447034463252047796929 17507585275847439035847697)
              ·
                refine ⟨13130688956885579276885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17507585275847439035847697 13130688956885579276885773)
                ·
                  refine ⟨4924008358832092228832165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13130688956885579276885773 4924008358832092228832165)
                  ·
                    refine ⟨923251567281017292906031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924008358832092228832165 923251567281017292906031)
                    ·
                      rfl

theorem cell23_5394078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5394078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394078 prefixEnd_5394078 := by exact prefixLift 5394078
  have htrace : WordTrace (prefixWord ++ tailWord_5394078) baseStart_5394078 baseEnd_5394078 := by
    simpa [prefixWord, tailWord_5394078, baseEnd_5394078] using wordTrace_append hprefix tailTrace_5394078
  have hstable : (prefixWord ++ tailWord_5394078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394078).length < 2 ^ (prefixWord ++ tailWord_5394078).sum := by decide
  have hdescent : baseEnd_5394078 < baseStart_5394078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394125 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 6]
def baseStart_5394125 : Nat := 118140960795 + 5394125 * 2 ^ 59
def prefixEnd_5394125 : Nat := 4983230072969 + 3 ^ 40 * 5394125 * 2
def baseEnd_5394125 : Nat := 307753203937090354981153

theorem tailTrace_5394125 : CollatzResearch.WordTrace tailWord_5394125 prefixEnd_5394125 307753203937090354981153 := by
  unfold tailWord_5394125
  simp only [CollatzResearch.WordTrace]
  refine ⟨196739901583013843051191829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131159934388675895367461219 196739901583013843051191829)
  ·
    refine ⟨9222182886703773893024617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196739901583013843051191829 9222182886703773893024617)
    ·
      refine ⟨6916637165027830419768463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9222182886703773893024617 6916637165027830419768463)
      ·
        refine ⟨10374955747541745629652695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916637165027830419768463 10374955747541745629652695)
        ·
          refine ⟨15562433621312618444479043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374955747541745629652695 15562433621312618444479043)
          ·
            refine ⟨23343650431968927666718565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15562433621312618444479043 23343650431968927666718565)
            ·
              refine ⟨4376934455994173937509731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23343650431968927666718565 4376934455994173937509731)
              ·
                refine ⟨6565401683991260906264597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4376934455994173937509731 6565401683991260906264597)
                ·
                  refine ⟨307753203937090354981153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6565401683991260906264597 307753203937090354981153)
                  ·
                    rfl

theorem cell23_5394125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_5394125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394125 prefixEnd_5394125 := by exact prefixLift 5394125
  have htrace : WordTrace (prefixWord ++ tailWord_5394125) baseStart_5394125 baseEnd_5394125 := by
    simpa [prefixWord, tailWord_5394125, baseEnd_5394125] using wordTrace_append hprefix tailTrace_5394125
  have hstable : (prefixWord ++ tailWord_5394125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394125).length < 2 ^ (prefixWord ++ tailWord_5394125).sum := by decide
  have hdescent : baseEnd_5394125 < baseStart_5394125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394138 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_5394138 : Nat := 118140960795 + 5394138 * 2 ^ 59
def prefixEnd_5394138 : Nat := 4983230072969 + 3 ^ 40 * 5394138 * 2
def baseEnd_5394138 : Nat := 923261836894107214655939

theorem tailTrace_5394138 : CollatzResearch.WordTrace tailWord_5394138 prefixEnd_5394138 923261836894107214655939 := by
  unfold tailWord_5394138
  simp only [CollatzResearch.WordTrace]
  refine ⟨49185093932991686567853767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131160250487977830847610045 49185093932991686567853767)
  ·
    refine ⟨73777640899487529851780651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49185093932991686567853767 73777640899487529851780651)
    ·
      refine ⟨110666461349231294777670977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73777640899487529851780651 110666461349231294777670977)
      ·
        refine ⟨82999846011923471083253233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110666461349231294777670977 82999846011923471083253233)
        ·
          refine ⟨62249884508942603312439925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82999846011923471083253233 62249884508942603312439925)
          ·
            refine ⟨5835926672713369060541243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62249884508942603312439925 5835926672713369060541243)
            ·
              refine ⟨8753890009070053590811865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835926672713369060541243 8753890009070053590811865)
              ·
                refine ⟨6565417506802540193108899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8753890009070053590811865 6565417506802540193108899)
                ·
                  refine ⟨9848126260203810289663349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565417506802540193108899 9848126260203810289663349)
                  ·
                    refine ⟨923261836894107214655939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9848126260203810289663349 923261836894107214655939)
                    ·
                      rfl

theorem cell23_5394138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_5394138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394138 prefixEnd_5394138 := by exact prefixLift 5394138
  have htrace : WordTrace (prefixWord ++ tailWord_5394138) baseStart_5394138 baseEnd_5394138 := by
    simpa [prefixWord, tailWord_5394138, baseEnd_5394138] using wordTrace_append hprefix tailTrace_5394138
  have hstable : (prefixWord ++ tailWord_5394138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394138).length < 2 ^ (prefixWord ++ tailWord_5394138).sum := by decide
  have hdescent : baseEnd_5394138 < baseStart_5394138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394144 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_5394144 : Nat := 118140960795 + 5394144 * 2 ^ 59
def prefixEnd_5394144 : Nat := 4983230072969 + 3 ^ 40 * 5394144 * 2
def baseEnd_5394144 : Nat := 2769788591566248620492789

theorem tailTrace_5394144 : CollatzResearch.WordTrace tailWord_5394144 prefixEnd_5394144 2769788591566248620492789 := by
  unfold tailWord_5394144
  simp only [CollatzResearch.WordTrace]
  refine ⟨98370297284972504648066743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131160396379963339530755657 98370297284972504648066743)
  ·
    refine ⟨147555445927458756972100115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98370297284972504648066743 147555445927458756972100115)
    ·
      refine ⟨221333168891188135458150173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147555445927458756972100115 221333168891188135458150173)
      ·
        refine ⟨82999938334195550796806315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221333168891188135458150173 82999938334195550796806315)
        ·
          refine ⟨124499907501293326195209473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82999938334195550796806315 124499907501293326195209473)
          ·
            refine ⟨93374930625969994646407105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124499907501293326195209473 93374930625969994646407105)
            ·
              refine ⟨70031197969477495984805329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93374930625969994646407105 70031197969477495984805329)
              ·
                refine ⟨52523398477108121988603997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70031197969477495984805329 52523398477108121988603997)
                ·
                  refine ⟨19696274428915545745726499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52523398477108121988603997 19696274428915545745726499)
                  ·
                    refine ⟨29544411643373318618589749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19696274428915545745726499 29544411643373318618589749)
                    ·
                      refine ⟨2769788591566248620492789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29544411643373318618589749 2769788591566248620492789)
                      ·
                        rfl

theorem cell23_5394144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_5394144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394144 prefixEnd_5394144 := by exact prefixLift 5394144
  have htrace : WordTrace (prefixWord ++ tailWord_5394144) baseStart_5394144 baseEnd_5394144 := by
    simpa [prefixWord, tailWord_5394144, baseEnd_5394144] using wordTrace_append hprefix tailTrace_5394144
  have hstable : (prefixWord ++ tailWord_5394144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394144).length < 2 ^ (prefixWord ++ tailWord_5394144).sum := by decide
  have hdescent : baseEnd_5394144 < baseStart_5394144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394145 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_5394145 : Nat := 118140960795 + 5394145 * 2 ^ 59
def prefixEnd_5394145 : Nat := 4983230072969 + 3 ^ 40 * 5394145 * 2
def baseEnd_5394145 : Nat := 2769789105046903116580285

theorem tailTrace_5394145 : CollatzResearch.WordTrace tailWord_5394145 prefixEnd_5394145 2769789105046903116580285 := by
  unfold tailWord_5394145
  simp only [CollatzResearch.WordTrace]
  refine ⟨196740631042941386466919889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131160420695294257644613259 196740631042941386466919889)
  ·
    refine ⟨147555473282206039850189917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196740631042941386466919889 147555473282206039850189917)
    ·
      refine ⟨55333302480827264943821219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147555473282206039850189917 55333302480827264943821219)
      ·
        refine ⟨82999953721240897415731829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55333302480827264943821219 82999953721240897415731829)
        ·
          refine ⟨7781245661366334132724859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82999953721240897415731829 7781245661366334132724859)
          ·
            refine ⟨11671868492049501199087289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781245661366334132724859 11671868492049501199087289)
            ·
              refine ⟨8753901369037125899315467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11671868492049501199087289 8753901369037125899315467)
              ·
                refine ⟨13130852053555688848973201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753901369037125899315467 13130852053555688848973201)
                ·
                  refine ⟨9848139040166766636729901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13130852053555688848973201 9848139040166766636729901)
                  ·
                    refine ⟨3693052140062537488773713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9848139040166766636729901 3693052140062537488773713)
                    ·
                      refine ⟨2769789105046903116580285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693052140062537488773713 2769789105046903116580285)
                      ·
                        rfl

theorem cell23_5394145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_5394145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394145 prefixEnd_5394145 := by exact prefixLift 5394145
  have htrace : WordTrace (prefixWord ++ tailWord_5394145) baseStart_5394145 baseEnd_5394145 := by
    simpa [prefixWord, tailWord_5394145, baseEnd_5394145] using wordTrace_append hprefix tailTrace_5394145
  have hstable : (prefixWord ++ tailWord_5394145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394145).length < 2 ^ (prefixWord ++ tailWord_5394145).sum := by decide
  have hdescent : baseEnd_5394145 < baseStart_5394145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394161 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_5394161 : Nat := 118140960795 + 5394161 * 2 ^ 59
def prefixEnd_5394161 : Nat := 4983230072969 + 3 ^ 40 * 5394161 * 2
def baseEnd_5394161 : Nat := 2769797320737375053980211

theorem tailTrace_5394161 : CollatzResearch.WordTrace tailWord_5394161 prefixEnd_5394161 2769797320737375053980211 := by
  unfold tailWord_5394161
  simp only [CollatzResearch.WordTrace]
  refine ⟨196741214610883421199502337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131160809740588947466334891 196741214610883421199502337)
  ·
    refine ⟨147555910958162565899626753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196741214610883421199502337 147555910958162565899626753)
    ·
      refine ⟨110666933218621924424720065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147555910958162565899626753 110666933218621924424720065)
      ·
        refine ⟨83000199913966443318540049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110666933218621924424720065 83000199913966443318540049)
        ·
          refine ⟨62250149935474832488905037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83000199913966443318540049 62250149935474832488905037)
          ·
            refine ⟨23343806225803062183339389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62250149935474832488905037 23343806225803062183339389)
            ·
              refine ⟨8753927334676148318752271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23343806225803062183339389 8753927334676148318752271)
              ·
                refine ⟨13130891002014222478128407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753927334676148318752271 13130891002014222478128407)
                ·
                  refine ⟨19696336503021333717192611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13130891002014222478128407 19696336503021333717192611)
                  ·
                    refine ⟨29544504754532000575788917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19696336503021333717192611 29544504754532000575788917)
                    ·
                      refine ⟨2769797320737375053980211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29544504754532000575788917 2769797320737375053980211)
                      ·
                        rfl

theorem cell23_5394161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_5394161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394161 prefixEnd_5394161 := by exact prefixLift 5394161
  have htrace : WordTrace (prefixWord ++ tailWord_5394161) baseStart_5394161 baseEnd_5394161 := by
    simpa [prefixWord, tailWord_5394161, baseEnd_5394161] using wordTrace_append hprefix tailTrace_5394161
  have hstable : (prefixWord ++ tailWord_5394161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394161).length < 2 ^ (prefixWord ++ tailWord_5394161).sum := by decide
  have hdescent : baseEnd_5394161 < baseStart_5394161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394178 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_5394178 : Nat := 118140960795 + 5394178 * 2 ^ 59
def prefixEnd_5394178 : Nat := 4983230072969 + 3 ^ 40 * 5394178 * 2
def baseEnd_5394178 : Nat := 2769806049908501487467633

theorem tailTrace_5394178 : CollatzResearch.WordTrace tailWord_5394178 prefixEnd_5394178 2769806049908501487467633 := by
  unfold tailWord_5394178
  simp only [CollatzResearch.WordTrace]
  refine ⟨49185458662955458275717797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131161223101214555401914125 49185458662955458275717797)
  ·
    refine ⟨9222273499304148426697087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49185458662955458275717797 9222273499304148426697087)
    ·
      refine ⟨13833410248956222640045631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222273499304148426697087 13833410248956222640045631)
      ·
        refine ⟨20750115373434333960068447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13833410248956222640045631 20750115373434333960068447)
        ·
          refine ⟨31125173060151500940102671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20750115373434333960068447 31125173060151500940102671)
          ·
            refine ⟨46687759590227251410154007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31125173060151500940102671 46687759590227251410154007)
            ·
              refine ⟨70031639385340877115231011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46687759590227251410154007 70031639385340877115231011)
              ·
                refine ⟨105047459078011315672846517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70031639385340877115231011 105047459078011315672846517)
                ·
                  refine ⟨9848199288563560844329361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105047459078011315672846517 9848199288563560844329361)
                  ·
                    refine ⟨7386149466422670633247021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9848199288563560844329361 7386149466422670633247021)
                    ·
                      refine ⟨2769806049908501487467633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386149466422670633247021 2769806049908501487467633)
                      ·
                        rfl

theorem cell23_5394178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_5394178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394178 prefixEnd_5394178 := by exact prefixLift 5394178
  have htrace : WordTrace (prefixWord ++ tailWord_5394178) baseStart_5394178 baseEnd_5394178 := by
    simpa [prefixWord, tailWord_5394178, baseEnd_5394178] using wordTrace_append hprefix tailTrace_5394178
  have hstable : (prefixWord ++ tailWord_5394178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394178).length < 2 ^ (prefixWord ++ tailWord_5394178).sum := by decide
  have hdescent : baseEnd_5394178 < baseStart_5394178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394196 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5394196 : Nat := 118140960795 + 5394196 * 2 ^ 59
def prefixEnd_5394196 : Nat := 4983230072969 + 3 ^ 40 * 5394196 * 2
def baseEnd_5394196 : Nat := 2769815292560282417042551

theorem tailTrace_5394196 : CollatzResearch.WordTrace tailWord_5394196 prefixEnd_5394196 2769815292560282417042551 := by
  unfold tailWord_5394196
  simp only [CollatzResearch.WordTrace]
  refine ⟨98371245582878311088513221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131161660777171081451350961 98371245582878311088513221)
  ·
    refine ⟨18444608546789683329096229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98371245582878311088513221 18444608546789683329096229)
    ·
      refine ⟨3458364102523065624205543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18444608546789683329096229 3458364102523065624205543)
      ·
        refine ⟨5187546153784598436308315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458364102523065624205543 5187546153784598436308315)
        ·
          refine ⟨7781319230676897654462473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187546153784598436308315 7781319230676897654462473)
          ·
            refine ⟨5835989423007673240846855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7781319230676897654462473 5835989423007673240846855)
            ·
              refine ⟨8753984134511509861270283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835989423007673240846855 8753984134511509861270283)
              ·
                refine ⟨13130976201767264791905425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8753984134511509861270283 13130976201767264791905425)
                ·
                  refine ⟨9848232151325448593929069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13130976201767264791905425 9848232151325448593929069)
                  ·
                    refine ⟨3693087056747043222723401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9848232151325448593929069 3693087056747043222723401)
                    ·
                      refine ⟨2769815292560282417042551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693087056747043222723401 2769815292560282417042551)
                      ·
                        rfl

theorem cell23_5394196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5394196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394196 prefixEnd_5394196 := by exact prefixLift 5394196
  have htrace : WordTrace (prefixWord ++ tailWord_5394196) baseStart_5394196 baseEnd_5394196 := by
    simpa [prefixWord, tailWord_5394196, baseEnd_5394196] using wordTrace_append hprefix tailTrace_5394196
  have hstable : (prefixWord ++ tailWord_5394196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394196).length < 2 ^ (prefixWord ++ tailWord_5394196).sum := by decide
  have hdescent : baseEnd_5394196 < baseStart_5394196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394206 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5394206 : Nat := 118140960795 + 5394206 * 2 ^ 59
def prefixEnd_5394206 : Nat := 4983230072969 + 3 ^ 40 * 5394206 * 2
def baseEnd_5394206 : Nat := 923273475788942459305835

theorem tailTrace_5394206 : CollatzResearch.WordTrace tailWord_5394206 prefixEnd_5394206 923273475788942459305835 := by
  unfold tailWord_5394206
  simp only [CollatzResearch.WordTrace]
  refine ⟨24592856986965049235611309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131161903930480262589926981 24592856986965049235611309)
  ·
    refine ⟨9222321370111893463354241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24592856986965049235611309 9222321370111893463354241)
    ·
      refine ⟨6916741027583920097515681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9222321370111893463354241 6916741027583920097515681)
      ·
        refine ⟨5187555770687940073136761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6916741027583920097515681 5187555770687940073136761)
        ·
          refine ⟨3890666828015955054852571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5187555770687940073136761 3890666828015955054852571)
          ·
            refine ⟨5836000242023932582278857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890666828015955054852571 5836000242023932582278857)
            ·
              refine ⟨4377000181517949436709143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836000242023932582278857 4377000181517949436709143)
              ·
                refine ⟨6565500272276924155063715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377000181517949436709143 6565500272276924155063715)
                ·
                  refine ⟨9848250408415386232595573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565500272276924155063715 9848250408415386232595573)
                  ·
                    refine ⟨923273475788942459305835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9848250408415386232595573 923273475788942459305835)
                    ·
                      rfl

theorem cell23_5394206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5394206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394206 prefixEnd_5394206 := by exact prefixLift 5394206
  have htrace : WordTrace (prefixWord ++ tailWord_5394206) baseStart_5394206 baseEnd_5394206 := by
    simpa [prefixWord, tailWord_5394206, baseEnd_5394206] using wordTrace_append hprefix tailTrace_5394206
  have hstable : (prefixWord ++ tailWord_5394206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394206).length < 2 ^ (prefixWord ++ tailWord_5394206).sum := by decide
  have hdescent : baseEnd_5394206 < baseStart_5394206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394208 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5394208 : Nat := 118140960795 + 5394208 * 2 ^ 59
def prefixEnd_5394208 : Nat := 4983230072969 + 3 ^ 40 * 5394208 * 2
def baseEnd_5394208 : Nat := 2769821454328136370092495

theorem tailTrace_5394208 : CollatzResearch.WordTrace tailWord_5394208 prefixEnd_5394208 2769821454328136370092495 := by
  unfold tailWord_5394208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98371464420856574113231639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131161952561142098817642185 98371464420856574113231639)
  ·
    refine ⟨147557196631284861169847459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98371464420856574113231639 147557196631284861169847459)
    ·
      refine ⟨221335794946927291754771189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147557196631284861169847459 221335794946927291754771189)
      ·
        refine ⟨20750230776274433602009799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221335794946927291754771189 20750230776274433602009799)
        ·
          refine ⟨31125346164411650403014699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20750230776274433602009799 31125346164411650403014699)
          ·
            refine ⟨46688019246617475604522049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31125346164411650403014699 46688019246617475604522049)
            ·
              refine ⟨35016014434963106703391537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46688019246617475604522049 35016014434963106703391537)
              ·
                refine ⟨26262010826222330027543653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35016014434963106703391537 26262010826222330027543653)
                ·
                  refine ⟨4924127029916686880164435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26262010826222330027543653 4924127029916686880164435)
                  ·
                    refine ⟨7386190544875030320246653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924127029916686880164435 7386190544875030320246653)
                    ·
                      refine ⟨2769821454328136370092495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386190544875030320246653 2769821454328136370092495)
                      ·
                        rfl

theorem cell23_5394208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5394208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394208 prefixEnd_5394208 := by exact prefixLift 5394208
  have htrace : WordTrace (prefixWord ++ tailWord_5394208) baseStart_5394208 baseEnd_5394208 := by
    simpa [prefixWord, tailWord_5394208, baseEnd_5394208] using wordTrace_append hprefix tailTrace_5394208
  have hstable : (prefixWord ++ tailWord_5394208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394208).length < 2 ^ (prefixWord ++ tailWord_5394208).sum := by decide
  have hdescent : baseEnd_5394208 < baseStart_5394208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394212 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_5394212 : Nat := 118140960795 + 5394212 * 2 ^ 59
def prefixEnd_5394212 : Nat := 4983230072969 + 3 ^ 40 * 5394212 * 2
def baseEnd_5394212 : Nat := 2769823508250754354442477

theorem tailTrace_5394212 : CollatzResearch.WordTrace tailWord_5394212 prefixEnd_5394212 2769823508250754354442477 := by
  unfold tailWord_5394212
  simp only [CollatzResearch.WordTrace]
  refine ⟨98371537366849328454804445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131162049822465771273072593 98371537366849328454804445)
  ·
    refine ⟨36889326512568498170551667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98371537366849328454804445 36889326512568498170551667)
    ·
      refine ⟨55333989768852747255827501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36889326512568498170551667 55333989768852747255827501)
      ·
        refine ⟨20750246163319780220935313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55333989768852747255827501 20750246163319780220935313)
        ·
          refine ⟨15562684622489835165701485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20750246163319780220935313 15562684622489835165701485)
          ·
            refine ⟨5836006733433688187138057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15562684622489835165701485 5836006733433688187138057)
            ·
              refine ⟨4377005050075266140353543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836006733433688187138057 4377005050075266140353543)
              ·
                refine ⟨6565507575112899210530315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377005050075266140353543 6565507575112899210530315)
                ·
                  refine ⟨9848261362669348815795473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565507575112899210530315 9848261362669348815795473)
                  ·
                    refine ⟨7386196022002011611846605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9848261362669348815795473 7386196022002011611846605)
                    ·
                      refine ⟨2769823508250754354442477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386196022002011611846605 2769823508250754354442477)
                      ·
                        rfl

theorem cell23_5394212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_5394212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394212 prefixEnd_5394212 := by exact prefixLift 5394212
  have htrace : WordTrace (prefixWord ++ tailWord_5394212) baseStart_5394212 baseEnd_5394212 := by
    simpa [prefixWord, tailWord_5394212, baseEnd_5394212] using wordTrace_append hprefix tailTrace_5394212
  have hstable : (prefixWord ++ tailWord_5394212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394212).length < 2 ^ (prefixWord ++ tailWord_5394212).sum := by decide
  have hdescent : baseEnd_5394212 < baseStart_5394212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394225 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_5394225 : Nat := 118140960795 + 5394225 * 2 ^ 59
def prefixEnd_5394225 : Nat := 4983230072969 + 3 ^ 40 * 5394225 * 2
def baseEnd_5394225 : Nat := 2769830183499262803579917

theorem tailTrace_5394225 : CollatzResearch.WordTrace tailWord_5394225 prefixEnd_5394225 2769830183499262803579917 := by
  unfold tailWord_5394225
  simp only [CollatzResearch.WordTrace]
  refine ⟨196743548882651560129832129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131162365921767706753221419 196743548882651560129832129)
  ·
    refine ⟨147557661661988670097374097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196743548882651560129832129 147557661661988670097374097)
    ·
      refine ⟨110668246246491502573030573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147557661661988670097374097 110668246246491502573030573)
      ·
        refine ⟨41500592342434313464886465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110668246246491502573030573 41500592342434313464886465)
        ·
          refine ⟨31125444256825735098664849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41500592342434313464886465 31125444256825735098664849)
          ·
            refine ⟨23344083192619301323998637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31125444256825735098664849 23344083192619301323998637)
            ·
              refine ⟨8754031197232237996499489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23344083192619301323998637 8754031197232237996499489)
              ·
                refine ⟨6565523397924178497374617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754031197232237996499489 6565523397924178497374617)
                ·
                  refine ⟨4924142548443133873030963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6565523397924178497374617 4924142548443133873030963)
                  ·
                    refine ⟨7386213822664700809546445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924142548443133873030963 7386213822664700809546445)
                    ·
                      refine ⟨2769830183499262803579917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386213822664700809546445 2769830183499262803579917)
                      ·
                        rfl

theorem cell23_5394225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_5394225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394225 prefixEnd_5394225 := by exact prefixLift 5394225
  have htrace : WordTrace (prefixWord ++ tailWord_5394225) baseStart_5394225 baseEnd_5394225 := by
    simpa [prefixWord, tailWord_5394225, baseEnd_5394225] using wordTrace_append hprefix tailTrace_5394225
  have hstable : (prefixWord ++ tailWord_5394225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394225).length < 2 ^ (prefixWord ++ tailWord_5394225).sum := by decide
  have hdescent : baseEnd_5394225 < baseStart_5394225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394252 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5394252 : Nat := 118140960795 + 5394252 * 2 ^ 59
def prefixEnd_5394252 : Nat := 4983230072969 + 3 ^ 40 * 5394252 * 2
def baseEnd_5394252 : Nat := 2769844047476934197942293

theorem tailTrace_5394252 : CollatzResearch.WordTrace tailWord_5394252 prefixEnd_5394252 2769844047476934197942293 := by
  unfold tailWord_5394252
  simp only [CollatzResearch.WordTrace]
  refine ⟨98372266826776871870532505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131163022435702495827376673 98372266826776871870532505)
  ·
    refine ⟨73779200120082653902899379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98372266826776871870532505 73779200120082653902899379)
    ·
      refine ⟨110668800180123980854349069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73779200120082653902899379 110668800180123980854349069)
      ·
        refine ⟨41500800067546492820380901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110668800180123980854349069 41500800067546492820380901)
        ·
          refine ⟨7781400012664967403821419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41500800067546492820380901 7781400012664967403821419)
          ·
            refine ⟨11672100018997451105732129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781400012664967403821419 11672100018997451105732129)
            ·
              refine ⟨8754075014248088329299097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11672100018997451105732129 8754075014248088329299097)
              ·
                refine ⟨6565556260686066246974323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754075014248088329299097 6565556260686066246974323)
                ·
                  refine ⟨9848334391029099370461485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565556260686066246974323 9848334391029099370461485)
                  ·
                    refine ⟨3693125396635912263923057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9848334391029099370461485 3693125396635912263923057)
                    ·
                      refine ⟨2769844047476934197942293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693125396635912263923057 2769844047476934197942293)
                      ·
                        rfl

theorem cell23_5394252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5394252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394252 prefixEnd_5394252 := by exact prefixLift 5394252
  have htrace : WordTrace (prefixWord ++ tailWord_5394252) baseStart_5394252 baseEnd_5394252 := by
    simpa [prefixWord, tailWord_5394252, baseEnd_5394252] using wordTrace_append hprefix tailTrace_5394252
  have hstable : (prefixWord ++ tailWord_5394252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394252).length < 2 ^ (prefixWord ++ tailWord_5394252).sum := by decide
  have hdescent : baseEnd_5394252 < baseStart_5394252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_5394281 : Nat := 118140960795 + 5394281 * 2 ^ 59
def prefixEnd_5394281 : Nat := 4983230072969 + 3 ^ 40 * 5394281 * 2
def baseEnd_5394281 : Nat := 2769858938415914584479659

theorem tailTrace_5394281 : CollatzResearch.WordTrace tailWord_5394281 prefixEnd_5394281 2769858938415914584479659 := by
  unfold tailWord_5394281
  simp only [CollatzResearch.WordTrace]
  refine ⟨196745591370448681693870697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131163727580299121129247131 196745591370448681693870697)
  ·
    refine ⟨147559193527836511270403023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196745591370448681693870697 147559193527836511270403023)
    ·
      refine ⟨221338790291754766905604535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147559193527836511270403023 221338790291754766905604535)
      ·
        refine ⟨332008185437632150358406803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221338790291754766905604535 332008185437632150358406803)
        ·
          refine ⟨498012278156448225537610205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332008185437632150358406803 498012278156448225537610205)
          ·
            refine ⟨186754604308668084576603827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498012278156448225537610205 186754604308668084576603827)
            ·
              refine ⟨280131906463002126864905741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186754604308668084576603827 280131906463002126864905741)
              ·
                refine ⟨105049464923625797574339653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280131906463002126864905741 105049464923625797574339653)
                ·
                  refine ⟨19696774673179837045188685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105049464923625797574339653 19696774673179837045188685)
                  ·
                    refine ⟨7386290502442438891945757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19696774673179837045188685 7386290502442438891945757)
                    ·
                      refine ⟨2769858938415914584479659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386290502442438891945757 2769858938415914584479659)
                      ·
                        rfl

theorem cell23_5394281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_5394281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394281 prefixEnd_5394281 := by exact prefixLift 5394281
  have htrace : WordTrace (prefixWord ++ tailWord_5394281) baseStart_5394281 baseEnd_5394281 := by
    simpa [prefixWord, tailWord_5394281, baseEnd_5394281] using wordTrace_append hprefix tailTrace_5394281
  have hstable : (prefixWord ++ tailWord_5394281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394281).length < 2 ^ (prefixWord ++ tailWord_5394281).sum := by decide
  have hdescent : baseEnd_5394281 < baseStart_5394281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394301 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_5394301 : Nat := 118140960795 + 5394301 * 2 ^ 59
def prefixEnd_5394301 : Nat := 4983230072969 + 3 ^ 40 * 5394301 * 2
def baseEnd_5394301 : Nat := 923289736009668168743189

theorem tailTrace_5394301 : CollatzResearch.WordTrace tailWord_5394301 prefixEnd_5394301 923289736009668168743189 := by
  unfold tailWord_5394301
  simp only [CollatzResearch.WordTrace]
  refine ⟨196746320830376225109598757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131164213886917483406399171 196746320830376225109598757)
  ·
    refine ⟨36889935155695542208049767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196746320830376225109598757 36889935155695542208049767)
    ·
      refine ⟨55334902733543313312074651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36889935155695542208049767 55334902733543313312074651)
      ·
        refine ⟨83002354100314969968111977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55334902733543313312074651 83002354100314969968111977)
        ·
          refine ⟨62251765575236227476083983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83002354100314969968111977 62251765575236227476083983)
          ·
            refine ⟨93377648362854341214125975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62251765575236227476083983 93377648362854341214125975)
            ·
              refine ⟨140066472544281511821188963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93377648362854341214125975 140066472544281511821188963)
              ·
                refine ⟨210099708816422267731783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140066472544281511821188963 210099708816422267731783445)
                ·
                  refine ⟨9848423850769793799927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210099708816422267731783445 9848423850769793799927349)
                  ·
                    refine ⟨923289736009668168743189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9848423850769793799927349 923289736009668168743189)
                    ·
                      rfl

theorem cell23_5394301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_5394301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394301 prefixEnd_5394301 := by exact prefixLift 5394301
  have htrace : WordTrace (prefixWord ++ tailWord_5394301) baseStart_5394301 baseEnd_5394301 := by
    simpa [prefixWord, tailWord_5394301, baseEnd_5394301] using wordTrace_append hprefix tailTrace_5394301
  have hstable : (prefixWord ++ tailWord_5394301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394301).length < 2 ^ (prefixWord ++ tailWord_5394301).sum := by decide
  have hdescent : baseEnd_5394301 < baseStart_5394301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394321 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_5394321 : Nat := 118140960795 + 5394321 * 2 ^ 59
def prefixEnd_5394321 : Nat := 4983230072969 + 3 ^ 40 * 5394321 * 2
def baseEnd_5394321 : Nat := 2769879477642094427979475

theorem tailTrace_5394321 : CollatzResearch.WordTrace tailWord_5394321 prefixEnd_5394321 2769879477642094427979475 := by
  unfold tailWord_5394321
  simp only [CollatzResearch.WordTrace]
  refine ⟨196747050290303768525326817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131164700193535845683551211 196747050290303768525326817)
  ·
    refine ⟨147560287717727826393995113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196747050290303768525326817 147560287717727826393995113)
    ·
      refine ⟨110670215788295869795496335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147560287717727826393995113 110670215788295869795496335)
      ·
        refine ⟨166005323682443804693244503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110670215788295869795496335 166005323682443804693244503)
        ·
          refine ⟨249007985523665707039866755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166005323682443804693244503 249007985523665707039866755)
          ·
            refine ⟨373511978285498560559800133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249007985523665707039866755 373511978285498560559800133)
            ·
              refine ⟨70033495928530980104962525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 373511978285498560559800133 70033495928530980104962525)
              ·
                refine ⟨26262560973199117539360947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70033495928530980104962525 26262560973199117539360947)
                ·
                  refine ⟨39393841459798676309041421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26262560973199117539360947 39393841459798676309041421)
                  ·
                    refine ⟨14772690547424503615890533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39393841459798676309041421 14772690547424503615890533)
                    ·
                      refine ⟨2769879477642094427979475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14772690547424503615890533 2769879477642094427979475)
                      ·
                        rfl

theorem cell23_5394321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_5394321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394321 prefixEnd_5394321 := by exact prefixLift 5394321
  have htrace : WordTrace (prefixWord ++ tailWord_5394321) baseStart_5394321 baseEnd_5394321 := by
    simpa [prefixWord, tailWord_5394321, baseEnd_5394321] using wordTrace_append hprefix tailTrace_5394321
  have hstable : (prefixWord ++ tailWord_5394321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394321).length < 2 ^ (prefixWord ++ tailWord_5394321).sum := by decide
  have hdescent : baseEnd_5394321 < baseStart_5394321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394365 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_5394365 : Nat := 118140960795 + 5394365 * 2 ^ 59
def prefixEnd_5394365 : Nat := 4983230072969 + 3 ^ 40 * 5394365 * 2
def baseEnd_5394365 : Nat := 923300690263630751943091

theorem tailTrace_5394365 : CollatzResearch.WordTrace tailWord_5394365 prefixEnd_5394365 923300690263630751943091 := by
  unfold tailWord_5394365
  simp only [CollatzResearch.WordTrace]
  refine ⟨196748655102144364039928549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131165770068096242693285699 196748655102144364039928549)
  ·
    refine ⟨36890372831652068257486603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196748655102144364039928549 36890372831652068257486603)
    ·
      refine ⟨55335559247478102386229905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36890372831652068257486603 55335559247478102386229905)
      ·
        refine ⟨41501669435608576789672429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55335559247478102386229905 41501669435608576789672429)
        ·
          refine ⟨15563126038353216296127161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41501669435608576789672429 15563126038353216296127161)
          ·
            refine ⟨11672344528764912222095371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15563126038353216296127161 11672344528764912222095371)
            ·
              refine ⟨17508516793147368333143057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11672344528764912222095371 17508516793147368333143057)
              ·
                refine ⟨13131387594860526249857293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17508516793147368333143057 13131387594860526249857293)
                ·
                  refine ⟨4924270348072697343696485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13131387594860526249857293 4924270348072697343696485)
                  ·
                    refine ⟨923300690263630751943091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924270348072697343696485 923300690263630751943091)
                    ·
                      rfl

theorem cell23_5394365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_5394365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394365 prefixEnd_5394365 := by exact prefixLift 5394365
  have htrace : WordTrace (prefixWord ++ tailWord_5394365) baseStart_5394365 baseEnd_5394365 := by
    simpa [prefixWord, tailWord_5394365, baseEnd_5394365] using wordTrace_append hprefix tailTrace_5394365
  have hstable : (prefixWord ++ tailWord_5394365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394365).length < 2 ^ (prefixWord ++ tailWord_5394365).sum := by decide
  have hdescent : baseEnd_5394365 < baseStart_5394365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394382 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_5394382 : Nat := 118140960795 + 5394382 * 2 ^ 59
def prefixEnd_5394382 : Nat := 4983230072969 + 3 ^ 40 * 5394382 * 2
def baseEnd_5394382 : Nat := 923303599987339563105565

theorem tailTrace_5394382 : CollatzResearch.WordTrace tailWord_5394382 prefixEnd_5394382 923303599987339563105565 := by
  unfold tailWord_5394382
  simp only [CollatzResearch.WordTrace]
  refine ⟨24593659392885346992912175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131166183428721850628864933 24593659392885346992912175)
  ·
    refine ⟨36890489089328020489368263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24593659392885346992912175 36890489089328020489368263)
    ·
      refine ⟨55335733633992030734052395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36890489089328020489368263 55335733633992030734052395)
      ·
        refine ⟨83003600450988046101078593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55335733633992030734052395 83003600450988046101078593)
        ·
          refine ⟨62252700338241034575808945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83003600450988046101078593 62252700338241034575808945)
          ·
            refine ⟨46689525253680775931856709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62252700338241034575808945 46689525253680775931856709)
            ·
              refine ⟨8754285985065145487223133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46689525253680775931856709 8754285985065145487223133)
              ·
                refine ⟨3282857244399429557708675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8754285985065145487223133 3282857244399429557708675)
                ·
                  refine ⟨4924285866599144336563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282857244399429557708675 4924285866599144336563013)
                  ·
                    refine ⟨923303599987339563105565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924285866599144336563013 923303599987339563105565)
                    ·
                      rfl

theorem cell23_5394382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_5394382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394382 prefixEnd_5394382 := by exact prefixLift 5394382
  have htrace : WordTrace (prefixWord ++ tailWord_5394382) baseStart_5394382 baseEnd_5394382 := by
    simpa [prefixWord, tailWord_5394382, baseEnd_5394382] using wordTrace_append hprefix tailTrace_5394382
  have hstable : (prefixWord ++ tailWord_5394382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394382).length < 2 ^ (prefixWord ++ tailWord_5394382).sum := by decide
  have hdescent : baseEnd_5394382 < baseStart_5394382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394425 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_5394425 : Nat := 118140960795 + 5394425 * 2 ^ 59
def prefixEnd_5394425 : Nat := 4983230072969 + 3 ^ 40 * 5394425 * 2
def baseEnd_5394425 : Nat := 923310959876720673692999

theorem tailTrace_5394425 : CollatzResearch.WordTrace tailWord_5394425 prefixEnd_5394425 923310959876720673692999 := by
  unfold tailWord_5394425
  simp only [CollatzResearch.WordTrace]
  refine ⟨196750843481926994287112729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131167228987951329524741819 196750843481926994287112729)
  ·
    refine ⟨147563132611445245715334547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196750843481926994287112729 147563132611445245715334547)
    ·
      refine ⟨221344698917167868573001821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147563132611445245715334547 221344698917167868573001821)
      ·
        refine ⟨83004262093937950714875683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221344698917167868573001821 83004262093937950714875683)
        ·
          refine ⟨124506393140906926072313525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83004262093937950714875683 124506393140906926072313525)
          ·
            refine ⟨11672474356960024319279393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124506393140906926072313525 11672474356960024319279393)
            ·
              refine ⟨8754355767720018239459545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11672474356960024319279393 8754355767720018239459545)
              ·
                refine ⟨6565766825790013679594659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754355767720018239459545 6565766825790013679594659)
                ·
                  refine ⟨9848650238685020519391989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565766825790013679594659 9848650238685020519391989)
                  ·
                    refine ⟨923310959876720673692999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9848650238685020519391989 923310959876720673692999)
                    ·
                      rfl

theorem cell23_5394425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_5394425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394425 prefixEnd_5394425 := by exact prefixLift 5394425
  have htrace : WordTrace (prefixWord ++ tailWord_5394425) baseStart_5394425 baseEnd_5394425 := by
    simpa [prefixWord, tailWord_5394425, baseEnd_5394425] using wordTrace_append hprefix tailTrace_5394425
  have hstable : (prefixWord ++ tailWord_5394425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394425).length < 2 ^ (prefixWord ++ tailWord_5394425).sum := by decide
  have hdescent : baseEnd_5394425 < baseStart_5394425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394439 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5394439 : Nat := 118140960795 + 5394439 * 2 ^ 59
def prefixEnd_5394439 : Nat := 4983230072969 + 3 ^ 40 * 5394439 * 2
def baseEnd_5394439 : Nat := 2769940068359324966303933

theorem tailTrace_5394439 : CollatzResearch.WordTrace tailWord_5394439 prefixEnd_5394439 2769940068359324966303933 := by
  unfold tailWord_5394439
  simp only [CollatzResearch.WordTrace]
  refine ⟨196751354103876274678122371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131167569402584183118748247 196751354103876274678122371)
  ·
    refine ⟨295127031155814412017183557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196751354103876274678122371 295127031155814412017183557)
    ·
      refine ⟨55336318341715202253221917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295127031155814412017183557 55336318341715202253221917)
      ·
        refine ⟨20751119378143200844958219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55336318341715202253221917 20751119378143200844958219)
        ·
          refine ⟨31126679067214801267437329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20751119378143200844958219 31126679067214801267437329)
          ·
            refine ⟨23345009300411100950577997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31126679067214801267437329 23345009300411100950577997)
            ·
              refine ⟨8754378487654162856466749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23345009300411100950577997 8754378487654162856466749)
              ·
                refine ⟨3282891932870311071175031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8754378487654162856466749 3282891932870311071175031)
                ·
                  refine ⟨4924337899305466606762547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3282891932870311071175031 4924337899305466606762547)
                  ·
                    refine ⟨7386506848958199910143821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924337899305466606762547 7386506848958199910143821)
                    ·
                      refine ⟨2769940068359324966303933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386506848958199910143821 2769940068359324966303933)
                      ·
                        rfl

theorem cell23_5394439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5394439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394439 prefixEnd_5394439 := by exact prefixLift 5394439
  have htrace : WordTrace (prefixWord ++ tailWord_5394439) baseStart_5394439 baseEnd_5394439 := by
    simpa [prefixWord, tailWord_5394439, baseEnd_5394439] using wordTrace_append hprefix tailTrace_5394439
  have hstable : (prefixWord ++ tailWord_5394439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394439).length < 2 ^ (prefixWord ++ tailWord_5394439).sum := by decide
  have hdescent : baseEnd_5394439 < baseStart_5394439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394451 : List Nat := [1, 1, 1, 2, 1, 4, 13]
def baseStart_5394451 : Nat := 118140960795 + 5394451 * 2 ^ 59
def prefixEnd_5394451 : Nat := 4983230072969 + 3 ^ 40 * 5394451 * 2
def baseEnd_5394451 : Nat := 34196867038607147152517

theorem tailTrace_5394451 : CollatzResearch.WordTrace tailWord_5394451 prefixEnd_5394451 34196867038607147152517 := by
  unfold tailWord_5394451
  simp only [CollatzResearch.WordTrace]
  refine ⟨196751791779832800727559207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131167861186555200485039471 196751791779832800727559207)
  ·
    refine ⟨295127687669749201091338811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196751791779832800727559207 295127687669749201091338811)
    ·
      refine ⟨442691531504623801637008217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295127687669749201091338811 442691531504623801637008217)
      ·
        refine ⟨332018648628467851227756163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442691531504623801637008217 332018648628467851227756163)
        ·
          refine ⟨498027972942701776841634245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332018648628467851227756163 498027972942701776841634245)
          ·
            refine ⟨93380244926756583157806421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 498027972942701776841634245 93380244926756583157806421)
            ·
              refine ⟨34196867038607147152517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 93380244926756583157806421 34196867038607147152517)
              ·
                rfl

theorem cell23_5394451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 13].length) (baseStart_5394451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394451 prefixEnd_5394451 := by exact prefixLift 5394451
  have htrace : WordTrace (prefixWord ++ tailWord_5394451) baseStart_5394451 baseEnd_5394451 := by
    simpa [prefixWord, tailWord_5394451, baseEnd_5394451] using wordTrace_append hprefix tailTrace_5394451
  have hstable : (prefixWord ++ tailWord_5394451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394451).length < 2 ^ (prefixWord ++ tailWord_5394451).sum := by decide
  have hdescent : baseEnd_5394451 < baseStart_5394451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394458 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_5394458 : Nat := 118140960795 + 5394458 * 2 ^ 59
def prefixEnd_5394458 : Nat := 4983230072969 + 3 ^ 40 * 5394458 * 2
def baseEnd_5394458 : Nat := 2769949824491760391966345

theorem tailTrace_5394458 : CollatzResearch.WordTrace tailWord_5394458 prefixEnd_5394458 2769949824491760391966345 := by
  unfold tailWord_5394458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188011772701860230766007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131168031393871627282042685 49188011772701860230766007)
  ·
    refine ⟨73782017659052790346149011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49188011772701860230766007 73782017659052790346149011)
    ·
      refine ⟨110673026488579185519223517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73782017659052790346149011 110673026488579185519223517)
      ·
        refine ⟨41502384933217194569708819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110673026488579185519223517 41502384933217194569708819)
        ·
          refine ⟨62253577399825791854563229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41502384933217194569708819 62253577399825791854563229)
          ·
            refine ⟨23345091524934671945461211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62253577399825791854563229 23345091524934671945461211)
            ·
              refine ⟨35017637287402007918191817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23345091524934671945461211 35017637287402007918191817)
              ·
                refine ⟨26263227965551505938643863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35017637287402007918191817 26263227965551505938643863)
                ·
                  refine ⟨39394841948327258907965795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26263227965551505938643863 39394841948327258907965795)
                  ·
                    refine ⟨59092262922490888361948693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39394841948327258907965795 59092262922490888361948693)
                    ·
                      refine ⟨2769949824491760391966345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59092262922490888361948693 2769949824491760391966345)
                      ·
                        rfl

theorem cell23_5394458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_5394458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394458 prefixEnd_5394458 := by exact prefixLift 5394458
  have htrace : WordTrace (prefixWord ++ tailWord_5394458) baseStart_5394458 baseEnd_5394458 := by
    simpa [prefixWord, tailWord_5394458, baseEnd_5394458] using wordTrace_append hprefix tailTrace_5394458
  have hstable : (prefixWord ++ tailWord_5394458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394458).length < 2 ^ (prefixWord ++ tailWord_5394458).sum := by decide
  have hdescent : baseEnd_5394458 < baseStart_5394458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394482 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_5394482 : Nat := 118140960795 + 5394482 * 2 ^ 59
def prefixEnd_5394482 : Nat := 4983230072969 + 3 ^ 40 * 5394482 * 2
def baseEnd_5394482 : Nat := 2769962148027468298066235

theorem tailTrace_5394482 : CollatzResearch.WordTrace tailWord_5394482 prefixEnd_5394482 2769962148027468298066235 := by
  unfold tailWord_5394482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188230610680123255484425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131168614961813662014625133 49188230610680123255484425)
  ·
    refine ⟨36891172958010092441613319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49188230610680123255484425 36891172958010092441613319)
    ·
      refine ⟨55336759437015138662419979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36891172958010092441613319 55336759437015138662419979)
      ·
        refine ⟨83005139155522707993629969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55336759437015138662419979 83005139155522707993629969)
        ·
          refine ⟨62253854366642030995222477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83005139155522707993629969 62253854366642030995222477)
          ·
            refine ⟨23345195387490761623208429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62253854366642030995222477 23345195387490761623208429)
            ·
              refine ⟨8754448270309035608703161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23345195387490761623208429 8754448270309035608703161)
              ·
                refine ⟨6565836202731776706527371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754448270309035608703161 6565836202731776706527371)
                ·
                  refine ⟨9848754304097665059791057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565836202731776706527371 9848754304097665059791057)
                  ·
                    refine ⟨7386565728073248794843293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9848754304097665059791057 7386565728073248794843293)
                    ·
                      refine ⟨2769962148027468298066235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386565728073248794843293 2769962148027468298066235)
                      ·
                        rfl

theorem cell23_5394482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_5394482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394482 prefixEnd_5394482 := by exact prefixLift 5394482
  have htrace : WordTrace (prefixWord ++ tailWord_5394482) baseStart_5394482 baseEnd_5394482 := by
    simpa [prefixWord, tailWord_5394482, baseEnd_5394482] using wordTrace_append hprefix tailTrace_5394482
  have hstable : (prefixWord ++ tailWord_5394482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394482).length < 2 ^ (prefixWord ++ tailWord_5394482).sum := by decide
  have hdescent : baseEnd_5394482 < baseStart_5394482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394495 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_5394495 : Nat := 118140960795 + 5394495 * 2 ^ 59
def prefixEnd_5394495 : Nat := 4983230072969 + 3 ^ 40 * 5394495 * 2
def baseEnd_5394495 : Nat := 2769968823275976747203675

theorem tailTrace_5394495 : CollatzResearch.WordTrace tailWord_5394495 prefixEnd_5394495 2769968823275976747203675 := by
  unfold tailWord_5394495
  simp only [CollatzResearch.WordTrace]
  refine ⟨196753396591673396242160939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131168931061115597494773959 196753396591673396242160939)
  ·
    refine ⟨295130094887510094363241409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196753396591673396242160939 295130094887510094363241409)
    ·
      refine ⟨221347571165632570772431057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295130094887510094363241409 221347571165632570772431057)
      ·
        refine ⟨166010678374224428079323293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221347571165632570772431057 166010678374224428079323293)
        ·
          refine ⟨62254004390334160529746235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166010678374224428079323293 62254004390334160529746235)
          ·
            refine ⟨93381006585501240794619353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62254004390334160529746235 93381006585501240794619353)
            ·
              refine ⟨70035754939125930595964515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93381006585501240794619353 70035754939125930595964515)
              ·
                refine ⟨105053632408688895893946773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70035754939125930595964515 105053632408688895893946773)
                ·
                  refine ⟨4924389019157291995028755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105053632408688895893946773 4924389019157291995028755)
                  ·
                    refine ⟨7386583528735937992543133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924389019157291995028755 7386583528735937992543133)
                    ·
                      refine ⟨2769968823275976747203675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386583528735937992543133 2769968823275976747203675)
                      ·
                        rfl

theorem cell23_5394495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_5394495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394495 prefixEnd_5394495 := by exact prefixLift 5394495
  have htrace : WordTrace (prefixWord ++ tailWord_5394495) baseStart_5394495 baseEnd_5394495 := by
    simpa [prefixWord, tailWord_5394495, baseEnd_5394495] using wordTrace_append hprefix tailTrace_5394495
  have hstable : (prefixWord ++ tailWord_5394495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394495).length < 2 ^ (prefixWord ++ tailWord_5394495).sum := by decide
  have hdescent : baseEnd_5394495 < baseStart_5394495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394508 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5394508 : Nat := 118140960795 + 5394508 * 2 ^ 59
def prefixEnd_5394508 : Nat := 4983230072969 + 3 ^ 40 * 5394508 * 2
def baseEnd_5394508 : Nat := 2769975498524485196341115

theorem tailTrace_5394508 : CollatzResearch.WordTrace tailWord_5394508 prefixEnd_5394508 2769975498524485196341115 := by
  unfold tailWord_5394508
  simp only [CollatzResearch.WordTrace]
  refine ⟨98376935370313149731192089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131169247160417532974922785 98376935370313149731192089)
  ·
    refine ⟨73782701527734862298394067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98376935370313149731192089 73782701527734862298394067)
    ·
      refine ⟨110674052291602293447591101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73782701527734862298394067 110674052291602293447591101)
      ·
        refine ⟨41502769609350860042846663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110674052291602293447591101 41502769609350860042846663)
        ·
          refine ⟨62254154414026290064269995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41502769609350860042846663 62254154414026290064269995)
          ·
            refine ⟨93381231621039435096404993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62254154414026290064269995 93381231621039435096404993)
            ·
              refine ⟨70035923715779576322303745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93381231621039435096404993 70035923715779576322303745)
              ·
                refine ⟨52526942786834682241727809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70035923715779576322303745 52526942786834682241727809)
                ·
                  refine ⟨39395207090126011681295857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52526942786834682241727809 39395207090126011681295857)
                  ·
                    refine ⟨29546405317594508760971893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39395207090126011681295857 29546405317594508760971893)
                    ·
                      refine ⟨2769975498524485196341115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29546405317594508760971893 2769975498524485196341115)
                      ·
                        rfl

theorem cell23_5394508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5394508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394508 prefixEnd_5394508 := by exact prefixLift 5394508
  have htrace : WordTrace (prefixWord ++ tailWord_5394508) baseStart_5394508 baseEnd_5394508 := by
    simpa [prefixWord, tailWord_5394508, baseEnd_5394508] using wordTrace_append hprefix tailTrace_5394508
  have hstable : (prefixWord ++ tailWord_5394508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394508).length < 2 ^ (prefixWord ++ tailWord_5394508).sum := by decide
  have hdescent : baseEnd_5394508 < baseStart_5394508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394526 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5394526 : Nat := 118140960795 + 5394526 * 2 ^ 59
def prefixEnd_5394526 : Nat := 4983230072969 + 3 ^ 40 * 5394526 * 2
def baseEnd_5394526 : Nat := 2769984741176266125916033

theorem tailTrace_5394526 : CollatzResearch.WordTrace tailWord_5394526 prefixEnd_5394526 2769984741176266125916033 := by
  unfold tailWord_5394526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24594315906820136067067429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131169684836374059024359621 24594315906820136067067429)
  ·
    refine ⟨4611434232528775512575143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24594315906820136067067429 4611434232528775512575143)
    ·
      refine ⟨6917151348793163268862715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611434232528775512575143 6917151348793163268862715)
      ·
        refine ⟨10375727023189744903294073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917151348793163268862715 10375727023189744903294073)
        ·
          refine ⟨7781795267392308677470555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10375727023189744903294073 7781795267392308677470555)
          ·
            refine ⟨11672692901088463016205833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781795267392308677470555 11672692901088463016205833)
            ·
              refine ⟨8754519675816347262154375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11672692901088463016205833 8754519675816347262154375)
              ·
                refine ⟨13131779513724520893231563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754519675816347262154375 13131779513724520893231563)
                ·
                  refine ⟨19697669270586781339847345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13131779513724520893231563 19697669270586781339847345)
                  ·
                    refine ⟨14773251952940086004885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19697669270586781339847345 14773251952940086004885509)
                    ·
                      refine ⟨2769984741176266125916033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14773251952940086004885509 2769984741176266125916033)
                      ·
                        rfl

theorem cell23_5394526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5394526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394526 prefixEnd_5394526 := by exact prefixLift 5394526
  have htrace : WordTrace (prefixWord ++ tailWord_5394526) baseStart_5394526 baseEnd_5394526 := by
    simpa [prefixWord, tailWord_5394526, baseEnd_5394526] using wordTrace_append hprefix tailTrace_5394526
  have hstable : (prefixWord ++ tailWord_5394526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394526).length < 2 ^ (prefixWord ++ tailWord_5394526).sum := by decide
  have hdescent : baseEnd_5394526 < baseStart_5394526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394528 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_5394528 : Nat := 118140960795 + 5394528 * 2 ^ 59
def prefixEnd_5394528 : Nat := 4983230072969 + 3 ^ 40 * 5394528 * 2
def baseEnd_5394528 : Nat := 923328589379191706030341

theorem tailTrace_5394528 : CollatzResearch.WordTrace tailWord_5394528 prefixEnd_5394528 923328589379191706030341 := by
  unfold tailWord_5394528
  simp only [CollatzResearch.WordTrace]
  refine ⟨98377300100276921439056119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131169733467035895252074825 98377300100276921439056119)
  ·
    refine ⟨147565950150415382158584179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98377300100276921439056119 147565950150415382158584179)
    ·
      refine ⟨221348925225623073237876269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147565950150415382158584179 221348925225623073237876269)
      ·
        refine ⟨83005846959608652464203601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221348925225623073237876269 83005846959608652464203601)
        ·
          refine ⟨62254385219706489348152701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83005846959608652464203601 62254385219706489348152701)
          ·
            refine ⟨23345394457389933505557263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62254385219706489348152701 23345394457389933505557263)
            ·
              refine ⟨35018091686084900258335895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23345394457389933505557263 35018091686084900258335895)
              ·
                refine ⟨52527137529127350387503843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35018091686084900258335895 52527137529127350387503843)
                ·
                  refine ⟨78790706293691025581255765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52527137529127350387503843 78790706293691025581255765)
                  ·
                    refine ⟨923328589379191706030341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78790706293691025581255765 923328589379191706030341)
                    ·
                      rfl

theorem cell23_5394528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_5394528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394528 prefixEnd_5394528 := by exact prefixLift 5394528
  have htrace : WordTrace (prefixWord ++ tailWord_5394528) baseStart_5394528 baseEnd_5394528 := by
    simpa [prefixWord, tailWord_5394528, baseEnd_5394528] using wordTrace_append hprefix tailTrace_5394528
  have hstable : (prefixWord ++ tailWord_5394528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394528).length < 2 ^ (prefixWord ++ tailWord_5394528).sum := by decide
  have hdescent : baseEnd_5394528 < baseStart_5394528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394552 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_5394552 : Nat := 118140960795 + 5394552 * 2 ^ 59
def prefixEnd_5394552 : Nat := 4983230072969 + 3 ^ 40 * 5394552 * 2
def baseEnd_5394552 : Nat := 2769998091673283024190913

theorem tailTrace_5394552 : CollatzResearch.WordTrace tailWord_5394552 prefixEnd_5394552 2769998091673283024190913 := by
  unfold tailWord_5394552
  simp only [CollatzResearch.WordTrace]
  refine ⟨98377737776233447488492955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131170317034977929984657273 98377737776233447488492955)
  ·
    refine ⟨147566606664350171232739433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98377737776233447488492955 147566606664350171232739433)
    ·
      refine ⟨110674954998262628424554575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147566606664350171232739433 110674954998262628424554575)
      ·
        refine ⟨166012432497393942636831863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110674954998262628424554575 166012432497393942636831863)
        ·
          refine ⟨249018648746090913955247795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166012432497393942636831863 249018648746090913955247795)
          ·
            refine ⟨373527973119136370932871693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249018648746090913955247795 373527973119136370932871693)
            ·
              refine ⟨140072989919676139099826885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373527973119136370932871693 140072989919676139099826885)
              ·
                refine ⟨26263685609939276081217541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140072989919676139099826885 26263685609939276081217541)
                ·
                  refine ⟨4924441051863614265228289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26263685609939276081217541 4924441051863614265228289)
                  ·
                    refine ⟨3693330788897710698921217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924441051863614265228289 3693330788897710698921217)
                    ·
                      refine ⟨2769998091673283024190913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693330788897710698921217 2769998091673283024190913)
                      ·
                        rfl

theorem cell23_5394552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_5394552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394552 prefixEnd_5394552 := by exact prefixLift 5394552
  have htrace : WordTrace (prefixWord ++ tailWord_5394552) baseStart_5394552 baseEnd_5394552 := by
    simpa [prefixWord, tailWord_5394552, baseEnd_5394552] using wordTrace_append hprefix tailTrace_5394552
  have hstable : (prefixWord ++ tailWord_5394552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394552).length < 2 ^ (prefixWord ++ tailWord_5394552).sum := by decide
  have hdescent : baseEnd_5394552 < baseStart_5394552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394556 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_5394556 : Nat := 118140960795 + 5394556 * 2 ^ 59
def prefixEnd_5394556 : Nat := 4983230072969 + 3 ^ 40 * 5394556 * 2
def baseEnd_5394556 : Nat := 2770000145595901008540895

theorem tailTrace_5394556 : CollatzResearch.WordTrace tailWord_5394556 prefixEnd_5394556 2770000145595901008540895 := by
  unfold tailWord_5394556
  simp only [CollatzResearch.WordTrace]
  refine ⟨98377810722226201830065761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131170414296301602440087681 98377810722226201830065761)
  ·
    refine ⟨73783358041669651372549321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98377810722226201830065761 73783358041669651372549321)
    ·
      refine ⟨55337518531252238529411991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73783358041669651372549321 55337518531252238529411991)
      ·
        refine ⟨83006277796878357794117987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55337518531252238529411991 83006277796878357794117987)
        ·
          refine ⟨124509416695317536691176981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83006277796878357794117987 124509416695317536691176981)
          ·
            refine ⟨5836378907593009532398921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124509416695317536691176981 5836378907593009532398921)
            ·
              refine ⟨4377284180694757149299191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5836378907593009532398921 4377284180694757149299191)
              ·
                refine ⟨6565926271042135723948787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377284180694757149299191 6565926271042135723948787)
                ·
                  refine ⟨9848889406563203585923181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6565926271042135723948787 9848889406563203585923181)
                  ·
                    refine ⟨3693333527461201344721193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9848889406563203585923181 3693333527461201344721193)
                    ·
                      refine ⟨2770000145595901008540895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693333527461201344721193 2770000145595901008540895)
                      ·
                        rfl

theorem cell23_5394556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_5394556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394556 prefixEnd_5394556 := by exact prefixLift 5394556
  have htrace : WordTrace (prefixWord ++ tailWord_5394556) baseStart_5394556 baseEnd_5394556 := by
    simpa [prefixWord, tailWord_5394556, baseEnd_5394556] using wordTrace_append hprefix tailTrace_5394556
  have hstable : (prefixWord ++ tailWord_5394556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394556).length < 2 ^ (prefixWord ++ tailWord_5394556).sum := by decide
  have hdescent : baseEnd_5394556 < baseStart_5394556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394565 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_5394565 : Nat := 118140960795 + 5394565 * 2 ^ 59
def prefixEnd_5394565 : Nat := 4983230072969 + 3 ^ 40 * 5394565 * 2
def baseEnd_5394565 : Nat := 2770004766921791473328353

theorem tailTrace_5394565 : CollatzResearch.WordTrace tailWord_5394565 prefixEnd_5394565 2770004766921791473328353 := by
  unfold tailWord_5394565
  simp only [CollatzResearch.WordTrace]
  refine ⟨196755949701419798197209149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131170633134279865464806099 196755949701419798197209149)
  ·
    refine ⟨73783481138032424323953431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196755949701419798197209149 73783481138032424323953431)
    ·
      refine ⟨110675221707048636485930147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73783481138032424323953431 110675221707048636485930147)
      ·
        refine ⟨166012832560572954728895221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110675221707048636485930147 166012832560572954728895221)
        ·
          refine ⟨15563703052553714505833927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166012832560572954728895221 15563703052553714505833927)
          ·
            refine ⟨23345554578830571758750891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15563703052553714505833927 23345554578830571758750891)
            ·
              refine ⟨35018331868245857638126337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23345554578830571758750891 35018331868245857638126337)
              ·
                refine ⟨26263748901184393228594753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35018331868245857638126337 26263748901184393228594753)
                ·
                  refine ⟨19697811675888294921446065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26263748901184393228594753 19697811675888294921446065)
                  ·
                    refine ⟨14773358756916221191084549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19697811675888294921446065 14773358756916221191084549)
                    ·
                      refine ⟨2770004766921791473328353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14773358756916221191084549 2770004766921791473328353)
                      ·
                        rfl

theorem cell23_5394565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_5394565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394565 prefixEnd_5394565 := by exact prefixLift 5394565
  have htrace : WordTrace (prefixWord ++ tailWord_5394565) baseStart_5394565 baseEnd_5394565 := by
    simpa [prefixWord, tailWord_5394565, baseEnd_5394565] using wordTrace_append hprefix tailTrace_5394565
  have hstable : (prefixWord ++ tailWord_5394565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394565).length < 2 ^ (prefixWord ++ tailWord_5394565).sum := by decide
  have hdescent : baseEnd_5394565 < baseStart_5394565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394586 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5394586 : Nat := 118140960795 + 5394586 * 2 ^ 59
def prefixEnd_5394586 : Nat := 4983230072969 + 3 ^ 40 * 5394586 * 2
def baseEnd_5394586 : Nat := 2770015550015535891165757

theorem tailTrace_5394586 : CollatzResearch.WordTrace tailWord_5394586 prefixEnd_5394586 2770015550015535891165757 := by
  unfold tailWord_5394586
  simp only [CollatzResearch.WordTrace]
  refine ⟨49189178908585929695930903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131171143756229145855815741 49189178908585929695930903)
  ·
    refine ⟨73783768362878894543896355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49189178908585929695930903 73783768362878894543896355)
    ·
      refine ⟨110675652544318341815844533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73783768362878894543896355 110675652544318341815844533)
      ·
        refine ⟨10375842426029844545235425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110675652544318341815844533 10375842426029844545235425)
        ·
          refine ⟨7781881819522383408926569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10375842426029844545235425 7781881819522383408926569)
          ·
            refine ⟨5836411364641787556694927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7781881819522383408926569 5836411364641787556694927)
            ·
              refine ⟨8754617046962681335042391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836411364641787556694927 8754617046962681335042391)
              ·
                refine ⟨13131925570444022002563587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754617046962681335042391 13131925570444022002563587)
                ·
                  refine ⟨19697888355666033003845381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13131925570444022002563587 19697888355666033003845381)
                  ·
                    refine ⟨3693354066687381188221009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19697888355666033003845381 3693354066687381188221009)
                    ·
                      refine ⟨2770015550015535891165757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693354066687381188221009 2770015550015535891165757)
                      ·
                        rfl

theorem cell23_5394586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5394586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394586 prefixEnd_5394586 := by exact prefixLift 5394586
  have htrace : WordTrace (prefixWord ++ tailWord_5394586) baseStart_5394586 baseEnd_5394586 := by
    simpa [prefixWord, tailWord_5394586, baseEnd_5394586] using wordTrace_append hprefix tailTrace_5394586
  have hstable : (prefixWord ++ tailWord_5394586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394586).length < 2 ^ (prefixWord ++ tailWord_5394586).sum := by decide
  have hdescent : baseEnd_5394586 < baseStart_5394586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394626 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_5394626 : Nat := 118140960795 + 5394626 * 2 ^ 59
def prefixEnd_5394626 : Nat := 4983230072969 + 3 ^ 40 * 5394626 * 2
def baseEnd_5394626 : Nat := 307781787693523970518397

theorem tailTrace_5394626 : CollatzResearch.WordTrace tailWord_5394626 prefixEnd_5394626 307781787693523970518397 := by
  unfold tailWord_5394626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49189543638549701403794933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131172116369465870410119821 49189543638549701403794933)
  ·
    refine ⟨4611519716114034506605775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49189543638549701403794933 4611519716114034506605775)
    ·
      refine ⟨6917279574171051759908663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611519716114034506605775 6917279574171051759908663)
      ·
        refine ⟨10375919361256577639862995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917279574171051759908663 10375919361256577639862995)
        ·
          refine ⟨15563879041884866459794493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10375919361256577639862995 15563879041884866459794493)
          ·
            refine ⟨5836454640706824922422935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15563879041884866459794493 5836454640706824922422935)
            ·
              refine ⟨8754681961060237383634403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836454640706824922422935 8754681961060237383634403)
              ·
                refine ⟨13132022941590356075451605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754681961060237383634403 13132022941590356075451605)
                ·
                  refine ⟨307781787693523970518397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13132022941590356075451605 307781787693523970518397)
                  ·
                    rfl

theorem cell23_5394626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_5394626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394626 prefixEnd_5394626 := by exact prefixLift 5394626
  have htrace : WordTrace (prefixWord ++ tailWord_5394626) baseStart_5394626 baseEnd_5394626 := by
    simpa [prefixWord, tailWord_5394626, baseEnd_5394626] using wordTrace_append hprefix tailTrace_5394626
  have hstable : (prefixWord ++ tailWord_5394626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394626).length < 2 ^ (prefixWord ++ tailWord_5394626).sum := by decide
  have hdescent : baseEnd_5394626 < baseStart_5394626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394682 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_5394682 : Nat := 118140960795 + 5394682 * 2 ^ 59
def prefixEnd_5394682 : Nat := 4983230072969 + 3 ^ 40 * 5394682 * 2
def baseEnd_5394682 : Nat := 307784982684263057285035

theorem tailTrace_5394682 : CollatzResearch.WordTrace tailWord_5394682 prefixEnd_5394682 307784982684263057285035 := by
  unfold tailWord_5394682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49190054260498981794804575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131173478027997284786145533 49190054260498981794804575)
  ·
    refine ⟨73785081390748472692206863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49190054260498981794804575 73785081390748472692206863)
    ·
      refine ⟨110677622086122709038310295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73785081390748472692206863 110677622086122709038310295)
      ·
        refine ⟨166016433129184063557465443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110677622086122709038310295 166016433129184063557465443)
        ·
          refine ⟨249024649693776095336198165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166016433129184063557465443 249024649693776095336198165)
          ·
            refine ⟨11673030454395754468884289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249024649693776095336198165 11673030454395754468884289)
            ·
              refine ⟨8754772840796815851663217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11673030454395754468884289 8754772840796815851663217)
              ·
                refine ⟨6566079630597611888747413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754772840796815851663217 6566079630597611888747413)
                ·
                  refine ⟨307784982684263057285035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6566079630597611888747413 307784982684263057285035)
                  ·
                    rfl

theorem cell23_5394682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_5394682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394682 prefixEnd_5394682 := by exact prefixLift 5394682
  have htrace : WordTrace (prefixWord ++ tailWord_5394682) baseStart_5394682 baseEnd_5394682 := by
    simpa [prefixWord, tailWord_5394682, baseEnd_5394682] using wordTrace_append hprefix tailTrace_5394682
  have hstable : (prefixWord ++ tailWord_5394682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394682).length < 2 ^ (prefixWord ++ tailWord_5394682).sum := by decide
  have hdescent : baseEnd_5394682 < baseStart_5394682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394686 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5394686 : Nat := 118140960795 + 5394686 * 2 ^ 59
def prefixEnd_5394686 : Nat := 4983230072969 + 3 ^ 40 * 5394686 * 2
def baseEnd_5394686 : Nat := 923355632693661833305099

theorem tailTrace_5394686 : CollatzResearch.WordTrace tailWord_5394686 prefixEnd_5394686 923355632693661833305099 := by
  unfold tailWord_5394686
  simp only [CollatzResearch.WordTrace]
  refine ⟨24595045366747679482795489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131173575289320957241575941 24595045366747679482795489)
  ·
    refine ⟨18446284025060759612096617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24595045366747679482795489 18446284025060759612096617)
    ·
      refine ⟨13834713018795569709072463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18446284025060759612096617 13834713018795569709072463)
      ·
        refine ⟨20752069528193354563608695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13834713018795569709072463 20752069528193354563608695)
        ·
          refine ⟨31128104292290031845413043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20752069528193354563608695 31128104292290031845413043)
          ·
            refine ⟨46692156438435047768119565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31128104292290031845413043 46692156438435047768119565)
            ·
              refine ⟨17509558664413142913044837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46692156438435047768119565 17509558664413142913044837)
              ·
                refine ⟨3283042249577464296195907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17509558664413142913044837 3283042249577464296195907)
                ·
                  refine ⟨4924563374366196444293861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283042249577464296195907 4924563374366196444293861)
                  ·
                    refine ⟨923355632693661833305099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924563374366196444293861 923355632693661833305099)
                    ·
                      rfl

theorem cell23_5394686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5394686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394686 prefixEnd_5394686 := by exact prefixLift 5394686
  have htrace : WordTrace (prefixWord ++ tailWord_5394686) baseStart_5394686 baseEnd_5394686 := by
    simpa [prefixWord, tailWord_5394686, baseEnd_5394686] using wordTrace_append hprefix tailTrace_5394686
  have hstable : (prefixWord ++ tailWord_5394686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394686).length < 2 ^ (prefixWord ++ tailWord_5394686).sum := by decide
  have hdescent : baseEnd_5394686 < baseStart_5394686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394712 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_5394712 : Nat := 118140960795 + 5394712 * 2 ^ 59
def prefixEnd_5394712 : Nat := 4983230072969 + 3 ^ 40 * 5394712 * 2
def baseEnd_5394712 : Nat := 923360082859334132730059

theorem tailTrace_5394712 : CollatzResearch.WordTrace tailWord_5394712 prefixEnd_5394712 923360082859334132730059 := by
  unfold tailWord_5394712
  simp only [CollatzResearch.WordTrace]
  refine ⟨98380655615943621151405195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131174207487924828201873593 98380655615943621151405195)
  ·
    refine ⟨147570983423915431727107793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98380655615943621151405195 147570983423915431727107793)
    ·
      refine ⟨110678237567936573795330845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147570983423915431727107793 110678237567936573795330845)
      ·
        refine ⟨41504339087976215173249067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110678237567936573795330845 41504339087976215173249067)
        ·
          refine ⟨62256508631964322759873601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41504339087976215173249067 62256508631964322759873601)
          ·
            refine ⟨46692381473973242069905201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62256508631964322759873601 46692381473973242069905201)
            ·
              refine ⟨35019286105479931552428901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46692381473973242069905201 35019286105479931552428901)
              ·
                refine ⟨6566116144777487166080419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35019286105479931552428901 6566116144777487166080419)
                ·
                  refine ⟨9849174217166230749120629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566116144777487166080419 9849174217166230749120629)
                  ·
                    refine ⟨923360082859334132730059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9849174217166230749120629 923360082859334132730059)
                    ·
                      rfl

theorem cell23_5394712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_5394712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394712 prefixEnd_5394712 := by exact prefixLift 5394712
  have htrace : WordTrace (prefixWord ++ tailWord_5394712) baseStart_5394712 baseEnd_5394712 := by
    simpa [prefixWord, tailWord_5394712, baseEnd_5394712] using wordTrace_append hprefix tailTrace_5394712
  have hstable : (prefixWord ++ tailWord_5394712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394712).length < 2 ^ (prefixWord ++ tailWord_5394712).sum := by decide
  have hdescent : baseEnd_5394712 < baseStart_5394712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394719 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 5, 2]
def baseStart_5394719 : Nat := 118140960795 + 5394719 * 2 ^ 59
def prefixEnd_5394719 : Nat := 4983230072969 + 3 ^ 40 * 5394719 * 2
def baseEnd_5394719 : Nat := 2770083842942583870802645

theorem tailTrace_5394719 : CollatzResearch.WordTrace tailWord_5394719 prefixEnd_5394719 2770083842942583870802645 := by
  unfold tailWord_5394719
  simp only [CollatzResearch.WordTrace]
  refine ⟨196761566542861882498315211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131174377695241254998876807 196761566542861882498315211)
  ·
    refine ⟨295142349814292823747472817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196761566542861882498315211 295142349814292823747472817)
    ·
      refine ⟨221356762360719617810604613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295142349814292823747472817 221356762360719617810604613)
      ·
        refine ⟨41504392942634928339488365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221356762360719617810604613 41504392942634928339488365)
        ·
          refine ⟨15564147353488098127308137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41504392942634928339488365 15564147353488098127308137)
          ·
            refine ⟨11673110515116073595481103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15564147353488098127308137 11673110515116073595481103)
            ·
              refine ⟨17509665772674110393221655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11673110515116073595481103 17509665772674110393221655)
              ·
                refine ⟨26264498659011165589832483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17509665772674110393221655 26264498659011165589832483)
                ·
                  refine ⟨39396747988516748384748725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26264498659011165589832483 39396747988516748384748725)
                  ·
                    refine ⟨3693445123923445161070193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39396747988516748384748725 3693445123923445161070193)
                    ·
                      refine ⟨2770083842942583870802645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693445123923445161070193 2770083842942583870802645)
                      ·
                        rfl

theorem cell23_5394719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_5394719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394719 prefixEnd_5394719 := by exact prefixLift 5394719
  have htrace : WordTrace (prefixWord ++ tailWord_5394719) baseStart_5394719 baseEnd_5394719 := by
    simpa [prefixWord, tailWord_5394719, baseEnd_5394719] using wordTrace_append hprefix tailTrace_5394719
  have hstable : (prefixWord ++ tailWord_5394719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394719).length < 2 ^ (prefixWord ++ tailWord_5394719).sum := by decide
  have hdescent : baseEnd_5394719 < baseStart_5394719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394733 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5394733 : Nat := 118140960795 + 5394733 * 2 ^ 59
def prefixEnd_5394733 : Nat := 4983230072969 + 3 ^ 40 * 5394733 * 2
def baseEnd_5394733 : Nat := 307787892407971868447509

theorem tailTrace_5394733 : CollatzResearch.WordTrace tailWord_5394733 prefixEnd_5394733 307787892407971868447509 := by
  unfold tailWord_5394733
  simp only [CollatzResearch.WordTrace]
  refine ⟨196762077164811162889324853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131174718109874108592883235 196762077164811162889324853)
  ·
    refine ⟨18446444734201046520874205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196762077164811162889324853 18446444734201046520874205)
    ·
      refine ⟨6917416775325392445327827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18446444734201046520874205 6917416775325392445327827)
      ·
        refine ⟨10376125162988088667991741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917416775325392445327827 10376125162988088667991741)
        ·
          refine ⟨3891046936120533250496903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10376125162988088667991741 3891046936120533250496903)
          ·
            refine ⟨5836570404180799875745355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891046936120533250496903 5836570404180799875745355)
            ·
              refine ⟨8754855606271199813618033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836570404180799875745355 8754855606271199813618033)
              ·
                refine ⟨6566141704703399860213525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754855606271199813618033 6566141704703399860213525)
                ·
                  refine ⟨307787892407971868447509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6566141704703399860213525 307787892407971868447509)
                  ·
                    rfl

theorem cell23_5394733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5394733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394733 prefixEnd_5394733 := by exact prefixLift 5394733
  have htrace : WordTrace (prefixWord ++ tailWord_5394733) baseStart_5394733 baseEnd_5394733 := by
    simpa [prefixWord, tailWord_5394733, baseEnd_5394733] using wordTrace_append hprefix tailTrace_5394733
  have hstable : (prefixWord ++ tailWord_5394733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394733).length < 2 ^ (prefixWord ++ tailWord_5394733).sum := by decide
  have hdescent : baseEnd_5394733 < baseStart_5394733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394752 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_5394752 : Nat := 118140960795 + 5394752 * 2 ^ 59
def prefixEnd_5394752 : Nat := 4983230072969 + 3 ^ 40 * 5394752 * 2
def baseEnd_5394752 : Nat := 2770100787804182241689993

theorem tailTrace_5394752 : CollatzResearch.WordTrace tailWord_5394752 prefixEnd_5394752 2770100787804182241689993 := by
  unfold tailWord_5394752
  simp only [CollatzResearch.WordTrace]
  refine ⟨98381385075871164567133255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131175180101161552756177673 98381385075871164567133255)
  ·
    refine ⟨147572077613806746850699883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98381385075871164567133255 147572077613806746850699883)
    ·
      refine ⟨221358116420710120276049825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147572077613806746850699883 221358116420710120276049825)
      ·
        refine ⟨166018587315532590207037369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221358116420710120276049825 166018587315532590207037369)
        ·
          refine ⟨124513940486649442655278027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166018587315532590207037369 124513940486649442655278027)
          ·
            refine ⟨186770910729974163982917041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124513940486649442655278027 186770910729974163982917041)
            ·
              refine ⟨140078183047480622987187781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186770910729974163982917041 140078183047480622987187781)
              ·
                refine ⟨26264659321402616810097709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140078183047480622987187781 26264659321402616810097709)
                ·
                  refine ⟨9849247245525981303786641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26264659321402616810097709 9849247245525981303786641)
                  ·
                    refine ⟨7386935434144485977839981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9849247245525981303786641 7386935434144485977839981)
                    ·
                      refine ⟨2770100787804182241689993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386935434144485977839981 2770100787804182241689993)
                      ·
                        rfl

theorem cell23_5394752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_5394752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394752 prefixEnd_5394752 := by exact prefixLift 5394752
  have htrace : WordTrace (prefixWord ++ tailWord_5394752) baseStart_5394752 baseEnd_5394752 := by
    simpa [prefixWord, tailWord_5394752, baseEnd_5394752] using wordTrace_append hprefix tailTrace_5394752
  have hstable : (prefixWord ++ tailWord_5394752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394752).length < 2 ^ (prefixWord ++ tailWord_5394752).sum := by decide
  have hdescent : baseEnd_5394752 < baseStart_5394752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394769 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_5394769 : Nat := 118140960795 + 5394769 * 2 ^ 59
def prefixEnd_5394769 : Nat := 4983230072969 + 3 ^ 40 * 5394769 * 2
def baseEnd_5394769 : Nat := 2770109516975308675177415

theorem tailTrace_5394769 : CollatzResearch.WordTrace tailWord_5394769 prefixEnd_5394769 2770109516975308675177415 := by
  unfold tailWord_5394769
  simp only [CollatzResearch.WordTrace]
  refine ⟨196763390192680741037635361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131175593461787160691756907 196763390192680741037635361)
  ·
    refine ⟨147572542644510555778226521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196763390192680741037635361 147572542644510555778226521)
    ·
      refine ⟨110679406983382916833669891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147572542644510555778226521 110679406983382916833669891)
      ·
        refine ⟨166019110475074375250504837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110679406983382916833669891 166019110475074375250504837)
        ·
          refine ⟨31128583214076445359469657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166019110475074375250504837 31128583214076445359469657)
          ·
            refine ⟨23346437410557334019602243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31128583214076445359469657 23346437410557334019602243)
            ·
              refine ⟨35019656115836001029403365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23346437410557334019602243 35019656115836001029403365)
              ·
                refine ⟨6566185521719250193013131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35019656115836001029403365 6566185521719250193013131)
                ·
                  refine ⟨9849278282578875289519697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566185521719250193013131 9849278282578875289519697)
                  ·
                    refine ⟨7386958711934156467139773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9849278282578875289519697 7386958711934156467139773)
                    ·
                      refine ⟨2770109516975308675177415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386958711934156467139773 2770109516975308675177415)
                      ·
                        rfl

theorem cell23_5394769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_5394769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394769 prefixEnd_5394769 := by exact prefixLift 5394769
  have htrace : WordTrace (prefixWord ++ tailWord_5394769) baseStart_5394769 baseEnd_5394769 := by
    simpa [prefixWord, tailWord_5394769, baseEnd_5394769] using wordTrace_append hprefix tailTrace_5394769
  have hstable : (prefixWord ++ tailWord_5394769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394769).length < 2 ^ (prefixWord ++ tailWord_5394769).sum := by decide
  have hdescent : baseEnd_5394769 < baseStart_5394769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394772 : List Nat := [2, 4, 1, 1, 2, 3, 1, 9]
def baseStart_5394772 : Nat := 118140960795 + 5394772 * 2 ^ 59
def prefixEnd_5394772 : Nat := 4983230072969 + 3 ^ 40 * 5394772 * 2
def baseEnd_5394772 : Nat := 102596705830269339386663

theorem tailTrace_5394772 : CollatzResearch.WordTrace tailWord_5394772 prefixEnd_5394772 102596705830269339386663 := by
  unfold tailWord_5394772
  simp only [CollatzResearch.WordTrace]
  refine ⟨98381749805834936274997285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131175666407779915033329713 98381749805834936274997285)
  ·
    refine ⟨18446578088594050551561991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98381749805834936274997285 18446578088594050551561991)
    ·
      refine ⟨27669867132891075827342987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18446578088594050551561991 27669867132891075827342987)
      ·
        refine ⟨41504800699336613741014481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27669867132891075827342987 41504800699336613741014481)
        ·
          refine ⟨31128600524502460305760861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41504800699336613741014481 31128600524502460305760861)
          ·
            refine ⟨11673225196688422614660323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31128600524502460305760861 11673225196688422614660323)
            ·
              refine ⟨17509837795032633921990485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11673225196688422614660323 17509837795032633921990485)
              ·
                refine ⟨102596705830269339386663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17509837795032633921990485 102596705830269339386663)
                ·
                  rfl

theorem cell23_5394772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 9].length) (baseStart_5394772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394772 prefixEnd_5394772 := by exact prefixLift 5394772
  have htrace : WordTrace (prefixWord ++ tailWord_5394772) baseStart_5394772 baseEnd_5394772 := by
    simpa [prefixWord, tailWord_5394772, baseEnd_5394772] using wordTrace_append hprefix tailTrace_5394772
  have hstable : (prefixWord ++ tailWord_5394772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394772).length < 2 ^ (prefixWord ++ tailWord_5394772).sum := by decide
  have hdescent : baseEnd_5394772 < baseStart_5394772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394783 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 1, 2, 2]
def baseStart_5394783 : Nat := 118140960795 + 5394783 * 2 ^ 59
def prefixEnd_5394783 : Nat := 4983230072969 + 3 ^ 40 * 5394783 * 2
def baseEnd_5394783 : Nat := 2770116705704471620402351

theorem tailTrace_5394783 : CollatzResearch.WordTrace tailWord_5394783 prefixEnd_5394783 2770116705704471620402351 := by
  unfold tailWord_5394783
  simp only [CollatzResearch.WordTrace]
  refine ⟨196763900814630021428645003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131175933876420014285763335 196763900814630021428645003)
  ·
    refine ⟨295145851221945032142967505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196763900814630021428645003 295145851221945032142967505)
    ·
      refine ⟨221359388416458774107225629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295145851221945032142967505 221359388416458774107225629)
      ·
        refine ⟨83009770656172040290209611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221359388416458774107225629 83009770656172040290209611)
        ·
          refine ⟨124514655984258060435314417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83009770656172040290209611 124514655984258060435314417)
          ·
            refine ⟨93385991988193545326485813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124514655984258060435314417 93385991988193545326485813)
            ·
              refine ⟨8754936748893144874358045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93385991988193545326485813 8754936748893144874358045)
              ·
                refine ⟨3283101280834929327884267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8754936748893144874358045 3283101280834929327884267)
                ·
                  refine ⟨4924651921252393991826401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283101280834929327884267 4924651921252393991826401)
                  ·
                    refine ⟨3693488940939295493869801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924651921252393991826401 3693488940939295493869801)
                    ·
                      refine ⟨2770116705704471620402351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693488940939295493869801 2770116705704471620402351)
                      ·
                        rfl

theorem cell23_5394783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_5394783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394783 prefixEnd_5394783 := by exact prefixLift 5394783
  have htrace : WordTrace (prefixWord ++ tailWord_5394783) baseStart_5394783 baseEnd_5394783 := by
    simpa [prefixWord, tailWord_5394783, baseEnd_5394783] using wordTrace_append hprefix tailTrace_5394783
  have hstable : (prefixWord ++ tailWord_5394783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394783).length < 2 ^ (prefixWord ++ tailWord_5394783).sum := by decide
  have hdescent : baseEnd_5394783 < baseStart_5394783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394785 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_5394785 : Nat := 118140960795 + 5394785 * 2 ^ 59
def prefixEnd_5394785 : Nat := 4983230072969 + 3 ^ 40 * 5394785 * 2
def baseEnd_5394785 : Nat := 923372577555260204192447

theorem tailTrace_5394785 : CollatzResearch.WordTrace tailWord_5394785 prefixEnd_5394785 923372577555260204192447 := by
  unfold tailWord_5394785
  simp only [CollatzResearch.WordTrace]
  refine ⟨196763973760622775770217809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131175982507081850513478539 196763973760622775770217809)
  ·
    refine ⟨147572980320467081827663357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196763973760622775770217809 147572980320467081827663357)
    ·
      refine ⟨55339867620175155685373759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147572980320467081827663357 55339867620175155685373759)
      ·
        refine ⟨83009801430262733528060639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55339867620175155685373759 83009801430262733528060639)
        ·
          refine ⟨124514702145394100292090959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83009801430262733528060639 124514702145394100292090959)
          ·
            refine ⟨186772053218091150438136439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124514702145394100292090959 186772053218091150438136439)
            ·
              refine ⟨280158079827136725657204659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186772053218091150438136439 280158079827136725657204659)
              ·
                refine ⟨420237119740705088485806989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280158079827136725657204659 420237119740705088485806989)
                ·
                  refine ⟨157588919902764408182177621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420237119740705088485806989 157588919902764408182177621)
                  ·
                    refine ⟨923372577555260204192447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157588919902764408182177621 923372577555260204192447)
                    ·
                      rfl

theorem cell23_5394785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_5394785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394785 prefixEnd_5394785 := by exact prefixLift 5394785
  have htrace : WordTrace (prefixWord ++ tailWord_5394785) baseStart_5394785 baseEnd_5394785 := by
    simpa [prefixWord, tailWord_5394785, baseEnd_5394785] using wordTrace_append hprefix tailTrace_5394785
  have hstable : (prefixWord ++ tailWord_5394785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394785).length < 2 ^ (prefixWord ++ tailWord_5394785).sum := by decide
  have hdescent : baseEnd_5394785 < baseStart_5394785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394786 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5394786 : Nat := 118140960795 + 5394786 * 2 ^ 59
def prefixEnd_5394786 : Nat := 4983230072969 + 3 ^ 40 * 5394786 * 2
def baseEnd_5394786 : Nat := 2770118246146435108664837

theorem tailTrace_5394786 : CollatzResearch.WordTrace tailWord_5394786 prefixEnd_5394786 2770118246146435108664837 := by
  unfold tailWord_5394786
  simp only [CollatzResearch.WordTrace]
  refine ⟨49191002558404788235251053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131176006822412768627336141 49191002558404788235251053)
  ·
    refine ⟨18446625959401795588219145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49191002558404788235251053 18446625959401795588219145)
    ·
      refine ⟨13834969469551346691164359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18446625959401795588219145 13834969469551346691164359)
      ·
        refine ⟨20752454204327020036746539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13834969469551346691164359 20752454204327020036746539)
        ·
          refine ⟨31128681306490530055119809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20752454204327020036746539 31128681306490530055119809)
          ·
            refine ⟨23346510979867897541339857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31128681306490530055119809 23346510979867897541339857)
            ·
              refine ⟨17509883234900923156004893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23346510979867897541339857 17509883234900923156004893)
              ·
                refine ⟨6566206213087846183501835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17509883234900923156004893 6566206213087846183501835)
                ·
                  refine ⟨9849309319631769275252753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566206213087846183501835 9849309319631769275252753)
                  ·
                    refine ⟨7386981989723826956439565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9849309319631769275252753 7386981989723826956439565)
                    ·
                      refine ⟨2770118246146435108664837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7386981989723826956439565 2770118246146435108664837)
                      ·
                        rfl

theorem cell23_5394786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5394786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394786 prefixEnd_5394786 := by exact prefixLift 5394786
  have htrace : WordTrace (prefixWord ++ tailWord_5394786) baseStart_5394786 baseEnd_5394786 := by
    simpa [prefixWord, tailWord_5394786, baseEnd_5394786] using wordTrace_append hprefix tailTrace_5394786
  have hstable : (prefixWord ++ tailWord_5394786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394786).length < 2 ^ (prefixWord ++ tailWord_5394786).sum := by decide
  have hdescent : baseEnd_5394786 < baseStart_5394786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394800 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 1, 2, 2]
def baseStart_5394800 : Nat := 118140960795 + 5394800 * 2 ^ 59
def prefixEnd_5394800 : Nat := 4983230072969 + 3 ^ 40 * 5394800 * 2
def baseEnd_5394800 : Nat := 2770125434875598053889773

theorem tailTrace_5394800 : CollatzResearch.WordTrace tailWord_5394800 prefixEnd_5394800 2770125434875598053889773 := by
  unfold tailWord_5394800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98382260427784216666006927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131176347237045622221342569 98382260427784216666006927)
  ·
    refine ⟨147573390641676324999010391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98382260427784216666006927 147573390641676324999010391)
    ·
      refine ⟨221360085962514487498515587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147573390641676324999010391 221360085962514487498515587)
      ·
        refine ⟨332040128943771731247773381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221360085962514487498515587 332040128943771731247773381)
        ·
          refine ⟨62257524176957199608957509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332040128943771731247773381 62257524176957199608957509)
          ·
            refine ⟨11673285783179474926679533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62257524176957199608957509 11673285783179474926679533)
            ·
              refine ⟨4377482168692303097504825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11673285783179474926679533 4377482168692303097504825)
              ·
                refine ⟨3283111626519227323128619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4377482168692303097504825 3283111626519227323128619)
                ·
                  refine ⟨4924667439778840984692929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283111626519227323128619 4924667439778840984692929)
                  ·
                    refine ⟨3693500579834130738519697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924667439778840984692929 3693500579834130738519697)
                    ·
                      refine ⟨2770125434875598053889773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693500579834130738519697 2770125434875598053889773)
                      ·
                        rfl

theorem cell23_5394800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 2, 2].length) (baseStart_5394800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394800 prefixEnd_5394800 := by exact prefixLift 5394800
  have htrace : WordTrace (prefixWord ++ tailWord_5394800) baseStart_5394800 baseEnd_5394800 := by
    simpa [prefixWord, tailWord_5394800, baseEnd_5394800] using wordTrace_append hprefix tailTrace_5394800
  have hstable : (prefixWord ++ tailWord_5394800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394800).length < 2 ^ (prefixWord ++ tailWord_5394800).sum := by decide
  have hdescent : baseEnd_5394800 < baseStart_5394800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394806 : List Nat := [5, 1, 1, 4, 1, 1, 2, 8]
def baseStart_5394806 : Nat := 118140960795 + 5394806 * 2 ^ 59
def prefixEnd_5394806 : Nat := 4983230072969 + 3 ^ 40 * 5394806 * 2
def baseEnd_5394806 : Nat := 102597352435537964089435

theorem tailTrace_5394806 : CollatzResearch.WordTrace tailWord_5394806 prefixEnd_5394806 102597352435537964089435 := by
  unfold tailWord_5394806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12297796230846668522295767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131176493129031130904488181 12297796230846668522295767)
  ·
    refine ⟨18446694346270002783443651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12297796230846668522295767 18446694346270002783443651)
    ·
      refine ⟨27670041519405004175165477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18446694346270002783443651 27670041519405004175165477)
      ·
        refine ⟨5188132784888438282843527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27670041519405004175165477 5188132784888438282843527)
        ·
          refine ⟨7782199177332657424265291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188132784888438282843527 7782199177332657424265291)
          ·
            refine ⟨11673298765998986136397937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7782199177332657424265291 11673298765998986136397937)
            ·
              refine ⟨8754974074499239602298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11673298765998986136397937 8754974074499239602298453)
              ·
                refine ⟨102597352435537964089435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8754974074499239602298453 102597352435537964089435)
                ·
                  rfl

theorem cell23_5394806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_5394806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394806 prefixEnd_5394806 := by exact prefixLift 5394806
  have htrace : WordTrace (prefixWord ++ tailWord_5394806) baseStart_5394806 baseEnd_5394806 := by
    simpa [prefixWord, tailWord_5394806, baseEnd_5394806] using wordTrace_append hprefix tailTrace_5394806
  have hstable : (prefixWord ++ tailWord_5394806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394806).length < 2 ^ (prefixWord ++ tailWord_5394806).sum := by decide
  have hdescent : baseEnd_5394806 < baseStart_5394806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394809 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 3, 3, 2]
def baseStart_5394809 : Nat := 118140960795 + 5394809 * 2 ^ 59
def prefixEnd_5394809 : Nat := 4983230072969 + 3 ^ 40 * 5394809 * 2
def baseEnd_5394809 : Nat := 2770130056201488518677231

theorem tailTrace_5394809 : CollatzResearch.WordTrace tailWord_5394809 prefixEnd_5394809 2770130056201488518677231 := by
  unfold tailWord_5394809
  simp only [CollatzResearch.WordTrace]
  refine ⟨196764849112535827869091481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131176566075023885246060987 196764849112535827869091481)
  ·
    refine ⟨147573636834401870901818611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196764849112535827869091481 147573636834401870901818611)
    ·
      refine ⟨221360455251602806352727917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147573636834401870901818611 221360455251602806352727917)
      ·
        refine ⟨83010170719351052382272969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221360455251602806352727917 83010170719351052382272969)
        ·
          refine ⟨62257628039513289286704727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83010170719351052382272969 62257628039513289286704727)
          ·
            refine ⟨93386442059269933930057091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62257628039513289286704727 93386442059269933930057091)
            ·
              refine ⟨140079663088904900895085637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93386442059269933930057091 140079663088904900895085637)
              ·
                refine ⟨26264936829169668917828557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140079663088904900895085637 26264936829169668917828557)
                ·
                  refine ⟨9849351310938625844185709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26264936829169668917828557 9849351310938625844185709)
                  ·
                    refine ⟨3693506741601984691569641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9849351310938625844185709 3693506741601984691569641)
                    ·
                      refine ⟨2770130056201488518677231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693506741601984691569641 2770130056201488518677231)
                      ·
                        rfl

theorem cell23_5394809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_5394809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394809 prefixEnd_5394809 := by exact prefixLift 5394809
  have htrace : WordTrace (prefixWord ++ tailWord_5394809) baseStart_5394809 baseEnd_5394809 := by
    simpa [prefixWord, tailWord_5394809, baseEnd_5394809] using wordTrace_append hprefix tailTrace_5394809
  have hstable : (prefixWord ++ tailWord_5394809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394809).length < 2 ^ (prefixWord ++ tailWord_5394809).sum := by decide
  have hdescent : baseEnd_5394809 < baseStart_5394809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394839 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_5394839 : Nat := 118140960795 + 5394839 * 2 ^ 59
def prefixEnd_5394839 : Nat := 4983230072969 + 3 ^ 40 * 5394839 * 2
def baseEnd_5394839 : Nat := 2770145460621123401302093

theorem tailTrace_5394839 : CollatzResearch.WordTrace tailWord_5394839 prefixEnd_5394839 2770145460621123401302093 := by
  unfold tailWord_5394839
  simp only [CollatzResearch.WordTrace]
  refine ⟨196765943302427142992683571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131177295534951428661789047 196765943302427142992683571)
  ·
    refine ⟨295148914953640714489025357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196765943302427142992683571 295148914953640714489025357)
    ·
      refine ⟨110680843107615267933384509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295148914953640714489025357 110680843107615267933384509)
      ·
        refine ⟨41505316165355725475019191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110680843107615267933384509 41505316165355725475019191)
        ·
          refine ⟨62257974248033588212528787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41505316165355725475019191 62257974248033588212528787)
          ·
            refine ⟨93386961372050382318793181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62257974248033588212528787 93386961372050382318793181)
            ·
              refine ⟨35020110514518893369547443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93386961372050382318793181 35020110514518893369547443)
              ·
                refine ⟨52530165771778340054321165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35020110514518893369547443 52530165771778340054321165)
                ·
                  refine ⟨19698812164416877520370437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52530165771778340054321165 19698812164416877520370437)
                  ·
                    refine ⟨3693527280828164535069457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19698812164416877520370437 3693527280828164535069457)
                    ·
                      refine ⟨2770145460621123401302093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693527280828164535069457 2770145460621123401302093)
                      ·
                        rfl

theorem cell23_5394839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_5394839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394839 prefixEnd_5394839 := by exact prefixLift 5394839
  have htrace : WordTrace (prefixWord ++ tailWord_5394839) baseStart_5394839 baseEnd_5394839 := by
    simpa [prefixWord, tailWord_5394839, baseEnd_5394839] using wordTrace_append hprefix tailTrace_5394839
  have hstable : (prefixWord ++ tailWord_5394839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394839).length < 2 ^ (prefixWord ++ tailWord_5394839).sum := by decide
  have hdescent : baseEnd_5394839 < baseStart_5394839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394873 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5394873 : Nat := 118140960795 + 5394873 * 2 ^ 59
def prefixEnd_5394873 : Nat := 4983230072969 + 3 ^ 40 * 5394873 * 2
def baseEnd_5394873 : Nat := 2770162918963376268276937

theorem tailTrace_5394873 : CollatzResearch.WordTrace tailWord_5394873 prefixEnd_5394873 2770162918963376268276937 := by
  unfold tailWord_5394873
  simp only [CollatzResearch.WordTrace]
  refine ⟨196767183384303966799421273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131178122256202644532947515 196767183384303966799421273)
  ·
    refine ⟨147575387538227975099565955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196767183384303966799421273 147575387538227975099565955)
    ·
      refine ⟨221363081307341962649348933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147575387538227975099565955 221363081307341962649348933)
      ·
        refine ⟨41505577745126617996752925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221363081307341962649348933 41505577745126617996752925)
        ·
          refine ⟨15564591654422481748782347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41505577745126617996752925 15564591654422481748782347)
          ·
            refine ⟨23346887481633722623173521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15564591654422481748782347 23346887481633722623173521)
            ·
              refine ⟨17510165611225291967380141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23346887481633722623173521 17510165611225291967380141)
              ·
                refine ⟨6566312104209484487767553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17510165611225291967380141 6566312104209484487767553)
                ·
                  refine ⟨4924734078157113365825665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6566312104209484487767553 4924734078157113365825665)
                  ·
                    refine ⟨3693550558617835024369249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924734078157113365825665 3693550558617835024369249)
                    ·
                      refine ⟨2770162918963376268276937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693550558617835024369249 2770162918963376268276937)
                      ·
                        rfl

theorem cell23_5394873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5394873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394873 prefixEnd_5394873 := by exact prefixLift 5394873
  have htrace : WordTrace (prefixWord ++ tailWord_5394873) baseStart_5394873 baseEnd_5394873 := by
    simpa [prefixWord, tailWord_5394873, baseEnd_5394873] using wordTrace_append hprefix tailTrace_5394873
  have hstable : (prefixWord ++ tailWord_5394873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394873).length < 2 ^ (prefixWord ++ tailWord_5394873).sum := by decide
  have hdescent : baseEnd_5394873 < baseStart_5394873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394909 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5394909 : Nat := 118140960795 + 5394909 * 2 ^ 59
def prefixEnd_5394909 : Nat := 4983230072969 + 3 ^ 40 * 5394909 * 2
def baseEnd_5394909 : Nat := 923393801422312709142257

theorem tailTrace_5394909 : CollatzResearch.WordTrace tailWord_5394909 prefixEnd_5394909 923393801422312709142257 := by
  unfold tailWord_5394909
  simp only [CollatzResearch.WordTrace]
  refine ⟨196768496412173544947731781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131178997608115696631821187 196768496412173544947731781)
  ·
    refine ⟨36894093077282539677699709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196768496412173544947731781 36894093077282539677699709)
    ·
      refine ⟨13835284903980952379137391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36894093077282539677699709 13835284903980952379137391)
      ·
        refine ⟨20752927355971428568706087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13835284903980952379137391 20752927355971428568706087)
        ·
          refine ⟨31129391033957142853059131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20752927355971428568706087 31129391033957142853059131)
          ·
            refine ⟨46694086550935714279588697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31129391033957142853059131 46694086550935714279588697)
            ·
              refine ⟨35020564913201785709691523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46694086550935714279588697 35020564913201785709691523)
              ·
                refine ⟨52530847369802678564537285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35020564913201785709691523 52530847369802678564537285)
                ·
                  refine ⟨9849533881838002230850741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52530847369802678564537285 9849533881838002230850741)
                  ·
                    refine ⟨923393801422312709142257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9849533881838002230850741 923393801422312709142257)
                    ·
                      rfl

theorem cell23_5394909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5394909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394909 prefixEnd_5394909 := by exact prefixLift 5394909
  have htrace : WordTrace (prefixWord ++ tailWord_5394909) baseStart_5394909 baseEnd_5394909 := by
    simpa [prefixWord, tailWord_5394909, baseEnd_5394909] using wordTrace_append hprefix tailTrace_5394909
  have hstable : (prefixWord ++ tailWord_5394909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394909).length < 2 ^ (prefixWord ++ tailWord_5394909).sum := by decide
  have hdescent : baseEnd_5394909 < baseStart_5394909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394949 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_5394949 : Nat := 118140960795 + 5394949 * 2 ^ 59
def prefixEnd_5394949 : Nat := 4983230072969 + 3 ^ 40 * 5394949 * 2
def baseEnd_5394949 : Nat := 2770201943493117970926587

theorem tailTrace_5394949 : CollatzResearch.WordTrace tailWord_5394949 prefixEnd_5394949 2770201943493117970926587 := by
  unfold tailWord_5394949
  simp only [CollatzResearch.WordTrace]
  refine ⟨196769955332028631779187901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131179970221352421186125267 196769955332028631779187901)
  ·
    refine ⟨73788733249510736917195463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196769955332028631779187901 73788733249510736917195463)
    ·
      refine ⟨110683099874266105375793195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73788733249510736917195463 110683099874266105375793195)
      ·
        refine ⟨166024649811399158063689793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110683099874266105375793195 166024649811399158063689793)
        ·
          refine ⟨124518487358549368547767345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166024649811399158063689793 124518487358549368547767345)
          ·
            refine ⟨93388865518912026410825509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124518487358549368547767345 93388865518912026410825509)
            ·
              refine ⟨17510412284796004952029783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93388865518912026410825509 17510412284796004952029783)
              ·
                refine ⟨26265618427194007428044675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17510412284796004952029783 26265618427194007428044675)
                ·
                  refine ⟨39398427640791011142067013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26265618427194007428044675 39398427640791011142067013)
                  ·
                    refine ⟨7387205182648314589137565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39398427640791011142067013 7387205182648314589137565)
                    ·
                      refine ⟨2770201943493117970926587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7387205182648314589137565 2770201943493117970926587)
                      ·
                        rfl

theorem cell23_5394949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_5394949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394949 prefixEnd_5394949 := by exact prefixLift 5394949
  have htrace : WordTrace (prefixWord ++ tailWord_5394949) baseStart_5394949 baseEnd_5394949 := by
    simpa [prefixWord, tailWord_5394949, baseEnd_5394949] using wordTrace_append hprefix tailTrace_5394949
  have hstable : (prefixWord ++ tailWord_5394949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394949).length < 2 ^ (prefixWord ++ tailWord_5394949).sum := by decide
  have hdescent : baseEnd_5394949 < baseStart_5394949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394973 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_5394973 : Nat := 118140960795 + 5394973 * 2 ^ 59
def prefixEnd_5394973 : Nat := 4983230072969 + 3 ^ 40 * 5394973 * 2
def baseEnd_5394973 : Nat := 923404755676275292342159

theorem tailTrace_5394973 : CollatzResearch.WordTrace tailWord_5394973 prefixEnd_5394973 923404755676275292342159 := by
  unfold tailWord_5394973
  simp only [CollatzResearch.WordTrace]
  refine ⟨196770830683941683878061573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131180553789294455918707715 196770830683941683878061573)
  ·
    refine ⟨36894530753239065727136545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196770830683941683878061573 36894530753239065727136545)
    ·
      refine ⟨27670898064929299295352409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36894530753239065727136545 27670898064929299295352409)
      ·
        refine ⟨20753173548696974471514307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27670898064929299295352409 20753173548696974471514307)
        ·
          refine ⟨31129760323045461707271461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20753173548696974471514307 31129760323045461707271461)
          ·
            refine ⟨5836830060571024070113399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31129760323045461707271461 5836830060571024070113399)
            ·
              refine ⟨8755245090856536105170099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836830060571024070113399 8755245090856536105170099)
              ·
                refine ⟨13132867636284804157755149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8755245090856536105170099 13132867636284804157755149)
                ·
                  refine ⟨4924825363606801559158181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13132867636284804157755149 4924825363606801559158181)
                  ·
                    refine ⟨923404755676275292342159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4924825363606801559158181 923404755676275292342159)
                    ·
                      rfl

theorem cell23_5394973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_5394973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394973 prefixEnd_5394973 := by exact prefixLift 5394973
  have htrace : WordTrace (prefixWord ++ tailWord_5394973) baseStart_5394973 baseEnd_5394973 := by
    simpa [prefixWord, tailWord_5394973, baseEnd_5394973] using wordTrace_append hprefix tailTrace_5394973
  have hstable : (prefixWord ++ tailWord_5394973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394973).length < 2 ^ (prefixWord ++ tailWord_5394973).sum := by decide
  have hdescent : baseEnd_5394973 < baseStart_5394973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394986 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_5394986 : Nat := 118140960795 + 5394986 * 2 ^ 59
def prefixEnd_5394986 : Nat := 4983230072969 + 3 ^ 40 * 5394986 * 2
def baseEnd_5394986 : Nat := 307802326919703814018213

theorem tailTrace_5394986 : CollatzResearch.WordTrace tailWord_5394986 prefixEnd_5394986 307802326919703814018213 := by
  unfold tailWord_5394986
  simp only [CollatzResearch.WordTrace]
  refine ⟨49192826208223646774571203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131180869888596391398856541 49192826208223646774571203)
  ·
    refine ⟨73789239312335470161856805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49192826208223646774571203 73789239312335470161856805)
    ·
      refine ⟨13835482371062900655348151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73789239312335470161856805 13835482371062900655348151)
      ·
        refine ⟨20753223556594350983022227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13835482371062900655348151 20753223556594350983022227)
        ·
          refine ⟨31129835334891526474533341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20753223556594350983022227 31129835334891526474533341)
          ·
            refine ⟨11673688250584322427950003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31129835334891526474533341 11673688250584322427950003)
            ·
              refine ⟨17510532375876483641925005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11673688250584322427950003 17510532375876483641925005)
              ·
                refine ⟨6566449640953681365721877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17510532375876483641925005 6566449640953681365721877)
                ·
                  refine ⟨307802326919703814018213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6566449640953681365721877 307802326919703814018213)
                  ·
                    rfl

theorem cell23_5394986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_5394986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394986 prefixEnd_5394986 := by exact prefixLift 5394986
  have htrace : WordTrace (prefixWord ++ tailWord_5394986) baseStart_5394986 baseEnd_5394986 := by
    simpa [prefixWord, tailWord_5394986, baseEnd_5394986] using wordTrace_append hprefix tailTrace_5394986
  have hstable : (prefixWord ++ tailWord_5394986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394986).length < 2 ^ (prefixWord ++ tailWord_5394986).sum := by decide
  have hdescent : baseEnd_5394986 < baseStart_5394986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5394999 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 3, 5]
def baseStart_5394999 : Nat := 118140960795 + 5394999 * 2 ^ 59
def prefixEnd_5394999 : Nat := 4983230072969 + 3 ^ 40 * 5394999 * 2
def baseEnd_5394999 : Nat := 923409205841947591767119

theorem tailTrace_5394999 : CollatzResearch.WordTrace tailWord_5394999 prefixEnd_5394999 923409205841947591767119 := by
  unfold tailWord_5394999
  simp only [CollatzResearch.WordTrace]
  refine ⟨196771778981847490318508051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131181185987898326879005367 196771778981847490318508051)
  ·
    refine ⟨295157668472771235477762077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196771778981847490318508051 295157668472771235477762077)
    ·
      refine ⟨110684125677289213304160779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295157668472771235477762077 110684125677289213304160779)
      ·
        refine ⟨166026188515933819956241169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110684125677289213304160779 166026188515933819956241169)
        ·
          refine ⟨124519641386950364967180877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166026188515933819956241169 124519641386950364967180877)
          ·
            refine ⟨46694865520106386862692829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124519641386950364967180877 46694865520106386862692829)
            ·
              refine ⟨17510574570039895073509811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46694865520106386862692829 17510574570039895073509811)
              ·
                refine ⟨26265861855059842610264717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17510574570039895073509811 26265861855059842610264717)
                ·
                  refine ⟨9849698195647440978849269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26265861855059842610264717 9849698195647440978849269)
                  ·
                    refine ⟨923409205841947591767119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9849698195647440978849269 923409205841947591767119)
                    ·
                      rfl

theorem cell23_5394999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_5394999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5394999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5394999 prefixEnd_5394999 := by exact prefixLift 5394999
  have htrace : WordTrace (prefixWord ++ tailWord_5394999) baseStart_5394999 baseEnd_5394999 := by
    simpa [prefixWord, tailWord_5394999, baseEnd_5394999] using wordTrace_append hprefix tailTrace_5394999
  have hstable : (prefixWord ++ tailWord_5394999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5394999).length < 2 ^ (prefixWord ++ tailWord_5394999).sum := by decide
  have hdescent : baseEnd_5394999 < baseStart_5394999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5394999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_5395039 : Nat := 118140960795 + 5395039 * 2 ^ 59
def prefixEnd_5395039 : Nat := 4983230072969 + 3 ^ 40 * 5395039 * 2
def baseEnd_5395039 : Nat := 2770248156752022618801173

theorem tailTrace_5395039 : CollatzResearch.WordTrace tailWord_5395039 prefixEnd_5395039 2770248156752022618801173 := by
  unfold tailWord_5395039
  simp only [CollatzResearch.WordTrace]
  refine ⟨196773237901702577149964171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131182158601135051433309447 196773237901702577149964171)
  ·
    refine ⟨295159856852553865724946257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196773237901702577149964171 295159856852553865724946257)
    ·
      refine ⟨221369892639415399293709693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295159856852553865724946257 221369892639415399293709693)
      ·
        refine ⟨83013709739780774735141135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221369892639415399293709693 83013709739780774735141135)
        ·
          refine ⟨124520564609671162102711703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83013709739780774735141135 124520564609671162102711703)
          ·
            refine ⟨186780846914506743154067555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124520564609671162102711703 186780846914506743154067555)
            ·
              refine ⟨280171270371760114731101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186780846914506743154067555 280171270371760114731101333)
              ·
                refine ⟨13133028298676255378020375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280171270371760114731101333 13133028298676255378020375)
                ·
                  refine ⟨19699542448014383067030563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13133028298676255378020375 19699542448014383067030563)
                  ·
                    refine ⟨29549313672021574600545845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19699542448014383067030563 29549313672021574600545845)
                    ·
                      refine ⟨2770248156752022618801173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29549313672021574600545845 2770248156752022618801173)
                      ·
                        rfl

theorem cell23_5395039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_5395039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395039 prefixEnd_5395039 := by exact prefixLift 5395039
  have htrace : WordTrace (prefixWord ++ tailWord_5395039) baseStart_5395039 baseEnd_5395039 := by
    simpa [prefixWord, tailWord_5395039, baseEnd_5395039] using wordTrace_append hprefix tailTrace_5395039
  have hstable : (prefixWord ++ tailWord_5395039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395039).length < 2 ^ (prefixWord ++ tailWord_5395039).sum := by decide
  have hdescent : baseEnd_5395039 < baseStart_5395039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395073 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5395073 : Nat := 118140960795 + 5395073 * 2 ^ 59
def prefixEnd_5395073 : Nat := 4983230072969 + 3 ^ 40 * 5395073 * 2
def baseEnd_5395073 : Nat := 2770265615094275485776017

theorem tailTrace_5395073 : CollatzResearch.WordTrace tailWord_5395073 prefixEnd_5395073 2770265615094275485776017 := by
  unfold tailWord_5395073
  simp only [CollatzResearch.WordTrace]
  refine ⟨196774477983579400956701873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131182985322386267304467915 196774477983579400956701873)
  ·
    refine ⟨147580858487684550717526405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196774477983579400956701873 147580858487684550717526405)
    ·
      refine ⟨27671410966440853259536201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147580858487684550717526405 27671410966440853259536201)
      ·
        refine ⟨20753558224830639944652151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27671410966440853259536201 20753558224830639944652151)
        ·
          refine ⟨31130337337245959916978227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20753558224830639944652151 31130337337245959916978227)
          ·
            refine ⟨46695506005868939875467341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31130337337245959916978227 46695506005868939875467341)
            ·
              refine ⟨17510814752200852453300253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46695506005868939875467341 17510814752200852453300253)
              ·
                refine ⟨6566555532075319669987595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17510814752200852453300253 6566555532075319669987595)
                ·
                  refine ⟨9849833298112979504981393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566555532075319669987595 9849833298112979504981393)
                  ·
                    refine ⟨7387374973584734628736045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9849833298112979504981393 7387374973584734628736045)
                    ·
                      refine ⟨2770265615094275485776017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7387374973584734628736045 2770265615094275485776017)
                      ·
                        rfl

theorem cell23_5395073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5395073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395073 prefixEnd_5395073 := by exact prefixLift 5395073
  have htrace : WordTrace (prefixWord ++ tailWord_5395073) baseStart_5395073 baseEnd_5395073 := by
    simpa [prefixWord, tailWord_5395073, baseEnd_5395073] using wordTrace_append hprefix tailTrace_5395073
  have hstable : (prefixWord ++ tailWord_5395073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395073).length < 2 ^ (prefixWord ++ tailWord_5395073).sum := by decide
  have hdescent : baseEnd_5395073 < baseStart_5395073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395113 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 1, 3, 2]
def baseStart_5395113 : Nat := 118140960795 + 5395113 * 2 ^ 59
def prefixEnd_5395113 : Nat := 4983230072969 + 3 ^ 40 * 5395113 * 2
def baseEnd_5395113 : Nat := 2770286154320455329275833

theorem tailTrace_5395113 : CollatzResearch.WordTrace tailWord_5395113 prefixEnd_5395113 2770286154320455329275833 := by
  unfold tailWord_5395113
  simp only [CollatzResearch.WordTrace]
  refine ⟨196775936903434487788157993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131183957935622991858771995 196775936903434487788157993)
  ·
    refine ⟨147581952677575865841118495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196775936903434487788157993 147581952677575865841118495)
    ·
      refine ⟨221372929016363798761677743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147581952677575865841118495 221372929016363798761677743)
      ·
        refine ⟨332059393524545698142516615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221372929016363798761677743 332059393524545698142516615)
        ·
          refine ⟨498089090286818547213774923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332059393524545698142516615 498089090286818547213774923)
          ·
            refine ⟨747133635430227820820662385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498089090286818547213774923 747133635430227820820662385)
            ·
              refine ⟨560350226572670865615496789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747133635430227820820662385 560350226572670865615496789)
              ·
                refine ⟨6566604217648486706431603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 560350226572670865615496789 6566604217648486706431603)
                ·
                  refine ⟨9849906326472730059647405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566604217648486706431603 9849906326472730059647405)
                  ·
                    refine ⟨3693714872427273772367777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9849906326472730059647405 3693714872427273772367777)
                    ·
                      refine ⟨2770286154320455329275833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693714872427273772367777 2770286154320455329275833)
                      ·
                        rfl

theorem cell23_5395113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3, 2].length) (baseStart_5395113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395113 prefixEnd_5395113 := by exact prefixLift 5395113
  have htrace : WordTrace (prefixWord ++ tailWord_5395113) baseStart_5395113 baseEnd_5395113 := by
    simpa [prefixWord, tailWord_5395113, baseEnd_5395113] using wordTrace_append hprefix tailTrace_5395113
  have hstable : (prefixWord ++ tailWord_5395113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395113).length < 2 ^ (prefixWord ++ tailWord_5395113).sum := by decide
  have hdescent : baseEnd_5395113 < baseStart_5395113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395121 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5395121 : Nat := 118140960795 + 5395121 * 2 ^ 59
def prefixEnd_5395121 : Nat := 4983230072969 + 3 ^ 40 * 5395121 * 2
def baseEnd_5395121 : Nat := 2770290262165691297975797

theorem tailTrace_5395121 : CollatzResearch.WordTrace tailWord_5395121 prefixEnd_5395121 2770290262165691297975797 := by
  unfold tailWord_5395121
  simp only [CollatzResearch.WordTrace]
  refine ⟨196776228687405505154449217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131184152458270336769632811 196776228687405505154449217)
  ·
    refine ⟨147582171515554128865836913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196776228687405505154449217 147582171515554128865836913)
    ·
      refine ⟨110686628636665596649377685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147582171515554128865836913 110686628636665596649377685)
      ·
        refine ⟨5188435717343699842939579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110686628636665596649377685 5188435717343699842939579)
        ·
          refine ⟨7782653576015549764409369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188435717343699842939579 7782653576015549764409369)
          ·
            refine ⟨5836990182011662323307027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7782653576015549764409369 5836990182011662323307027)
            ·
              refine ⟨8755485273017493484960541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5836990182011662323307027 8755485273017493484960541)
              ·
                refine ⟨3283306977381560056860203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8755485273017493484960541 3283306977381560056860203)
                ·
                  refine ⟨4924960466072340085290305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283306977381560056860203 4924960466072340085290305)
                  ·
                    refine ⟨3693720349554255063967729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4924960466072340085290305 3693720349554255063967729)
                    ·
                      refine ⟨2770290262165691297975797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693720349554255063967729 2770290262165691297975797)
                      ·
                        rfl

theorem cell23_5395121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5395121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395121 prefixEnd_5395121 := by exact prefixLift 5395121
  have htrace : WordTrace (prefixWord ++ tailWord_5395121) baseStart_5395121 baseEnd_5395121 := by
    simpa [prefixWord, tailWord_5395121, baseEnd_5395121] using wordTrace_append hprefix tailTrace_5395121
  have hstable : (prefixWord ++ tailWord_5395121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395121).length < 2 ^ (prefixWord ++ tailWord_5395121).sum := by decide
  have hdescent : baseEnd_5395121 < baseStart_5395121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395154 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5395154 : Nat := 118140960795 + 5395154 * 2 ^ 59
def prefixEnd_5395154 : Nat := 4983230072969 + 3 ^ 40 * 5395154 * 2
def baseEnd_5395154 : Nat := 2770307207027289668863145

theorem tailTrace_5395154 : CollatzResearch.WordTrace tailWord_5395154 prefixEnd_5395154 2770307207027289668863145 := by
  unfold tailWord_5395154
  simp only [CollatzResearch.WordTrace]
  refine ⟨49194358074071487947600129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131184954864190634526933677 49194358074071487947600129)
  ·
    refine ⟨36895768555553615960700097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49194358074071487947600129 36895768555553615960700097)
    ·
      refine ⟨27671826416665211970525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36895768555553615960700097 27671826416665211970525073)
      ·
        refine ⟨20753869812498908977893805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27671826416665211970525073 20753869812498908977893805)
        ·
          refine ⟨7782701179687090866710177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20753869812498908977893805 7782701179687090866710177)
          ·
            refine ⟨5837025884765318150032633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7782701179687090866710177 5837025884765318150032633)
            ·
              refine ⟨4377769413573988612524475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837025884765318150032633 4377769413573988612524475)
              ·
                refine ⟨6566654120360982918786713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377769413573988612524475 6566654120360982918786713)
                ·
                  refine ⟨4924990590270737189090035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6566654120360982918786713 4924990590270737189090035)
                  ·
                    refine ⟨7387485885406105783635053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4924990590270737189090035 7387485885406105783635053)
                    ·
                      refine ⟨2770307207027289668863145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7387485885406105783635053 2770307207027289668863145)
                      ·
                        rfl

theorem cell23_5395154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5395154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395154 prefixEnd_5395154 := by exact prefixLift 5395154
  have htrace : WordTrace (prefixWord ++ tailWord_5395154) baseStart_5395154 baseEnd_5395154 := by
    simpa [prefixWord, tailWord_5395154, baseEnd_5395154] using wordTrace_append hprefix tailTrace_5395154
  have hstable : (prefixWord ++ tailWord_5395154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395154).length < 2 ^ (prefixWord ++ tailWord_5395154).sum := by decide
  have hdescent : baseEnd_5395154 < baseStart_5395154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395164 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5395164 : Nat := 118140960795 + 5395164 * 2 ^ 59
def prefixEnd_5395164 : Nat := 4983230072969 + 3 ^ 40 * 5395164 * 2
def baseEnd_5395164 : Nat := 2770312341833834629738099

theorem tailTrace_5395164 : CollatzResearch.WordTrace tailWord_5395164 prefixEnd_5395164 2770312341833834629738099 := by
  unfold tailWord_5395164
  simp only [CollatzResearch.WordTrace]
  refine ⟨98388898513124861749132273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131185198017499815665509697 98388898513124861749132273)
  ·
    refine ⟨73791673884843646311849205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98388898513124861749132273 73791673884843646311849205)
    ·
      refine ⟨6917969426704091841735863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73791673884843646311849205 6917969426704091841735863)
      ·
        refine ⟨10376954140056137762603795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917969426704091841735863 10376954140056137762603795)
        ·
          refine ⟨15565431210084206643905693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10376954140056137762603795 15565431210084206643905693)
          ·
            refine ⟨5837036703781577491464635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15565431210084206643905693 5837036703781577491464635)
            ·
              refine ⟨8755555055672366237196953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837036703781577491464635 8755555055672366237196953)
              ·
                refine ⟨6566666291754274677897715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8755555055672366237196953 6566666291754274677897715)
                ·
                  refine ⟨9849999437631412016846573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566666291754274677897715 9849999437631412016846573)
                  ·
                    refine ⟨3693749789111779506317465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9849999437631412016846573 3693749789111779506317465)
                    ·
                      refine ⟨2770312341833834629738099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693749789111779506317465 2770312341833834629738099)
                      ·
                        rfl

theorem cell23_5395164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5395164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395164 prefixEnd_5395164 := by exact prefixLift 5395164
  have htrace : WordTrace (prefixWord ++ tailWord_5395164) baseStart_5395164 baseEnd_5395164 := by
    simpa [prefixWord, tailWord_5395164, baseEnd_5395164] using wordTrace_append hprefix tailTrace_5395164
  have hstable : (prefixWord ++ tailWord_5395164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395164).length < 2 ^ (prefixWord ++ tailWord_5395164).sum := by decide
  have hdescent : baseEnd_5395164 < baseStart_5395164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395233 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5395233 : Nat := 118140960795 + 5395233 * 2 ^ 59
def prefixEnd_5395233 : Nat := 4983230072969 + 3 ^ 40 * 5395233 * 2
def baseEnd_5395233 : Nat := 2770347771998994859775281

theorem tailTrace_5395233 : CollatzResearch.WordTrace tailWord_5395233 prefixEnd_5395233 2770347771998994859775281 := by
  unfold tailWord_5395233
  simp only [CollatzResearch.WordTrace]
  refine ⟨196780313662999748282526353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131186875775333165521684235 196780313662999748282526353)
  ·
    refine ⟨147585235247249811211894765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196780313662999748282526353 147585235247249811211894765)
    ·
      refine ⟨55344463217718679204460537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147585235247249811211894765 55344463217718679204460537)
      ·
        refine ⟨41508347413289009403345403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55344463217718679204460537 41508347413289009403345403)
        ·
          refine ⟨62262521119933514105018105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41508347413289009403345403 62262521119933514105018105)
          ·
            refine ⟨46696890839950135578763579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62262521119933514105018105 46696890839950135578763579)
            ·
              refine ⟨70045336259925203368145369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46696890839950135578763579 70045336259925203368145369)
              ·
                refine ⟨52534002194943902526109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70045336259925203368145369 52534002194943902526109027)
                ·
                  refine ⟨78801003292415853789163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52534002194943902526109027 78801003292415853789163541)
                  ·
                    refine ⟨3693797029331993146367041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78801003292415853789163541 3693797029331993146367041)
                    ·
                      refine ⟨2770347771998994859775281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3693797029331993146367041 2770347771998994859775281)
                      ·
                        rfl

theorem cell23_5395233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5395233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395233 prefixEnd_5395233 := by exact prefixLift 5395233
  have htrace : WordTrace (prefixWord ++ tailWord_5395233) baseStart_5395233 baseEnd_5395233 := by
    simpa [prefixWord, tailWord_5395233, baseEnd_5395233] using wordTrace_append hprefix tailTrace_5395233
  have hstable : (prefixWord ++ tailWord_5395233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395233).length < 2 ^ (prefixWord ++ tailWord_5395233).sum := by decide
  have hdescent : baseEnd_5395233 < baseStart_5395233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395256 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 8]
def baseStart_5395256 : Nat := 118140960795 + 5395256 * 2 ^ 59
def prefixEnd_5395256 : Nat := 4983230072969 + 3 ^ 40 * 5395256 * 2
def baseEnd_5395256 : Nat := 307817731339338696643075

theorem tailTrace_5395256 : CollatzResearch.WordTrace tailWord_5395256 prefixEnd_5395256 307817731339338696643075 := by
  unfold tailWord_5395256
  simp only [CollatzResearch.WordTrace]
  refine ⟨98390576270958211605306811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131187435027944282140409081 98390576270958211605306811)
  ·
    refine ⟨147585864406437317407960217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98390576270958211605306811 147585864406437317407960217)
    ·
      refine ⟨110689398304827988055970163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147585864406437317407960217 110689398304827988055970163)
      ·
        refine ⟨166034097457241982083955245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110689398304827988055970163 166034097457241982083955245)
        ·
          refine ⟨62262786546465743281483217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166034097457241982083955245 62262786546465743281483217)
          ·
            refine ⟨46697089909849307461112413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62262786546465743281483217 46697089909849307461112413)
            ·
              refine ⟨17511408716193490297917155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46697089909849307461112413 17511408716193490297917155)
              ·
                refine ⟨26267113074290235446875733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17511408716193490297917155 26267113074290235446875733)
                ·
                  refine ⟨307817731339338696643075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26267113074290235446875733 307817731339338696643075)
                  ·
                    rfl

theorem cell23_5395256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_5395256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395256 prefixEnd_5395256 := by exact prefixLift 5395256
  have htrace : WordTrace (prefixWord ++ tailWord_5395256) baseStart_5395256 baseEnd_5395256 := by
    simpa [prefixWord, tailWord_5395256, baseEnd_5395256] using wordTrace_append hprefix tailTrace_5395256
  have hstable : (prefixWord ++ tailWord_5395256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395256).length < 2 ^ (prefixWord ++ tailWord_5395256).sum := by decide
  have hdescent : baseEnd_5395256 < baseStart_5395256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395317 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5395317 : Nat := 118140960795 + 5395317 * 2 ^ 59
def prefixEnd_5395317 : Nat := 4983230072969 + 3 ^ 40 * 5395317 * 2
def baseEnd_5395317 : Nat := 2770390904373972531124895

theorem tailTrace_5395317 : CollatzResearch.WordTrace tailWord_5395317 prefixEnd_5395317 2770390904373972531124895 := by
  unfold tailWord_5395317
  simp only [CollatzResearch.WordTrace]
  refine ⟨196783377394695430628584205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131188918263130287085722803 196783377394695430628584205)
  ·
    refine ⟨73793766523010786485719077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196783377394695430628584205 73793766523010786485719077)
    ·
      refine ⟨13836331223064522466072327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73793766523010786485719077 13836331223064522466072327)
      ·
        refine ⟨20754496834596783699108491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13836331223064522466072327 20754496834596783699108491)
        ·
          refine ⟨31131745251895175548662737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20754496834596783699108491 31131745251895175548662737)
          ·
            refine ⟨23348808938921381661497053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31131745251895175548662737 23348808938921381661497053)
            ·
              refine ⟨8755803352095518123061395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23348808938921381661497053 8755803352095518123061395)
              ·
                refine ⟨13133705028143277184592093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8755803352095518123061395 13133705028143277184592093)
                ·
                  refine ⟨4925139385553728944222035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13133705028143277184592093 4925139385553728944222035)
                  ·
                    refine ⟨7387709078330593416333053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925139385553728944222035 7387709078330593416333053)
                    ·
                      refine ⟨2770390904373972531124895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7387709078330593416333053 2770390904373972531124895)
                      ·
                        rfl

theorem cell23_5395317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5395317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395317 prefixEnd_5395317 := by exact prefixLift 5395317
  have htrace : WordTrace (prefixWord ++ tailWord_5395317) baseStart_5395317 baseEnd_5395317 := by
    simpa [prefixWord, tailWord_5395317, baseEnd_5395317] using wordTrace_append hprefix tailTrace_5395317
  have hstable : (prefixWord ++ tailWord_5395317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395317).length < 2 ^ (prefixWord ++ tailWord_5395317).sum := by decide
  have hdescent : baseEnd_5395317 < baseStart_5395317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395340 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_5395340 : Nat := 118140960795 + 5395340 * 2 ^ 59
def prefixEnd_5395340 : Nat := 4983230072969 + 3 ^ 40 * 5395340 * 2
def baseEnd_5395340 : Nat := 2770402714429025941137289

theorem tailTrace_5395340 : CollatzResearch.WordTrace tailWord_5395340 prefixEnd_5395340 2770402714429025941137289 := by
  unfold tailWord_5395340
  simp only [CollatzResearch.WordTrace]
  refine ⟨98392108136806052778335737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131189477515741403704447649 98392108136806052778335737)
  ·
    refine ⟨73794081102604539583751803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98392108136806052778335737 73794081102604539583751803)
    ·
      refine ⟨110691121653906809375627705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73794081102604539583751803 110691121653906809375627705)
      ·
        refine ⟨83018341240430107031720779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110691121653906809375627705 83018341240430107031720779)
        ·
          refine ⟨124527511860645160547581169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83018341240430107031720779 124527511860645160547581169)
          ·
            refine ⟨93395633895483870410685877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124527511860645160547581169 93395633895483870410685877)
            ·
              refine ⟨8755840677701612851001801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93395633895483870410685877 8755840677701612851001801)
              ·
                refine ⟨6566880508276209638251351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8755840677701612851001801 6566880508276209638251351)
                ·
                  refine ⟨9850320762414314457377027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566880508276209638251351 9850320762414314457377027)
                  ·
                    refine ⟨14775481143621471686065541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9850320762414314457377027 14775481143621471686065541)
                    ·
                      refine ⟨2770402714429025941137289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14775481143621471686065541 2770402714429025941137289)
                      ·
                        rfl

theorem cell23_5395340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_5395340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395340 prefixEnd_5395340 := by exact prefixLift 5395340
  have htrace : WordTrace (prefixWord ++ tailWord_5395340) baseStart_5395340 baseEnd_5395340 := by
    simpa [prefixWord, tailWord_5395340, baseEnd_5395340] using wordTrace_append hprefix tailTrace_5395340
  have hstable : (prefixWord ++ tailWord_5395340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395340).length < 2 ^ (prefixWord ++ tailWord_5395340).sum := by decide
  have hdescent : baseEnd_5395340 < baseStart_5395340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395357 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_5395357 : Nat := 118140960795 + 5395357 * 2 ^ 59
def prefixEnd_5395357 : Nat := 4983230072969 + 3 ^ 40 * 5395357 * 2
def baseEnd_5395357 : Nat := 2770411443600152374624711

theorem tailTrace_5395357 : CollatzResearch.WordTrace tailWord_5395357 prefixEnd_5395357 2770411443600152374624711 := by
  unfold tailWord_5395357
  simp only [CollatzResearch.WordTrace]
  refine ⟨196784836314550517460040325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131189890876367011640026883 196784836314550517460040325)
  ·
    refine ⟨36897156808978222023757561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196784836314550517460040325 36897156808978222023757561)
    ·
      refine ⟨27672867606733666517818171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36897156808978222023757561 27672867606733666517818171)
      ·
        refine ⟨41509301410100499776727257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27672867606733666517818171 41509301410100499776727257)
        ·
          refine ⟨31131976057575374832545443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41509301410100499776727257 31131976057575374832545443)
          ·
            refine ⟨46697964086363062248818165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31131976057575374832545443 46697964086363062248818165)
            ·
              refine ⟨4377934133096537085826703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46697964086363062248818165 4377934133096537085826703)
              ·
                refine ⟨6566901199644805628740055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377934133096537085826703 6566901199644805628740055)
                ·
                  refine ⟨9850351799467208443110083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566901199644805628740055 9850351799467208443110083)
                  ·
                    refine ⟨14775527699200812664665125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9850351799467208443110083 14775527699200812664665125)
                    ·
                      refine ⟨2770411443600152374624711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14775527699200812664665125 2770411443600152374624711)
                      ·
                        rfl

theorem cell23_5395357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_5395357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395357 prefixEnd_5395357 := by exact prefixLift 5395357
  have htrace : WordTrace (prefixWord ++ tailWord_5395357) baseStart_5395357 baseEnd_5395357 := by
    simpa [prefixWord, tailWord_5395357, baseEnd_5395357] using wordTrace_append hprefix tailTrace_5395357
  have hstable : (prefixWord ++ tailWord_5395357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395357).length < 2 ^ (prefixWord ++ tailWord_5395357).sum := by decide
  have hdescent : baseEnd_5395357 < baseStart_5395357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395360 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_5395360 : Nat := 118140960795 + 5395360 * 2 ^ 59
def prefixEnd_5395360 : Nat := 4983230072969 + 3 ^ 40 * 5395360 * 2
def baseEnd_5395360 : Nat := 2770412984042115862887197

theorem tailTrace_5395360 : CollatzResearch.WordTrace tailWord_5395360 prefixEnd_5395360 2770412984042115862887197 := by
  unfold tailWord_5395360
  simp only [CollatzResearch.WordTrace]
  refine ⟨98392472866769824486199767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131189963822359765981599689 98392472866769824486199767)
  ·
    refine ⟨147588709300154736729299651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98392472866769824486199767 147588709300154736729299651)
    ·
      refine ⟨221383063950232105093949477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147588709300154736729299651 221383063950232105093949477)
      ·
        refine ⟨41509324490668519705115527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221383063950232105093949477 41509324490668519705115527)
        ·
          refine ⟨62263986736002779557673291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41509324490668519705115527 62263986736002779557673291)
          ·
            refine ⟨93395980104004169336509937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62263986736002779557673291 93395980104004169336509937)
            ·
              refine ⟨70046985078003127002382453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93395980104004169336509937 70046985078003127002382453)
              ·
                refine ⟨6566904851062793156473355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70046985078003127002382453 6566904851062793156473355)
                ·
                  refine ⟨9850357276594189734710033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566904851062793156473355 9850357276594189734710033)
                  ·
                    refine ⟨7387767957445642301032525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9850357276594189734710033 7387767957445642301032525)
                    ·
                      refine ⟨2770412984042115862887197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7387767957445642301032525 2770412984042115862887197)
                      ·
                        rfl

theorem cell23_5395360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_5395360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395360 prefixEnd_5395360 := by exact prefixLift 5395360
  have htrace : WordTrace (prefixWord ++ tailWord_5395360) baseStart_5395360 baseEnd_5395360 := by
    simpa [prefixWord, tailWord_5395360, baseEnd_5395360] using wordTrace_append hprefix tailTrace_5395360
  have hstable : (prefixWord ++ tailWord_5395360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395360).length < 2 ^ (prefixWord ++ tailWord_5395360).sum := by decide
  have hdescent : baseEnd_5395360 < baseStart_5395360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395405 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5395405 : Nat := 118140960795 + 5395405 * 2 ^ 59
def prefixEnd_5395405 : Nat := 4983230072969 + 3 ^ 40 * 5395405 * 2
def baseEnd_5395405 : Nat := 923478696890522728941497

theorem tailTrace_5395405 : CollatzResearch.WordTrace tailWord_5395405 prefixEnd_5395405 923478696890522728941497 := by
  unfold tailWord_5395405
  simp only [CollatzResearch.WordTrace]
  refine ⟨196786587018376621657787669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131191058012251081105191779 196786587018376621657787669)
  ·
    refine ⟨9224371266486404140208797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196786587018376621657787669 9224371266486404140208797)
    ·
      refine ⟨3459139224932401552578299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9224371266486404140208797 3459139224932401552578299)
      ·
        refine ⟨5188708837398602328867449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3459139224932401552578299 5188708837398602328867449)
        ·
          refine ⟨3891531628048951746650587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188708837398602328867449 3891531628048951746650587)
          ·
            refine ⟨5837297442073427619975881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891531628048951746650587 5837297442073427619975881)
            ·
              refine ⟨4377973081555070714981911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837297442073427619975881 4377973081555070714981911)
              ·
                refine ⟨6566959622332606072472867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377973081555070714981911 6566959622332606072472867)
                ·
                  refine ⟨9850439433498909108709301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6566959622332606072472867 9850439433498909108709301)
                  ·
                    refine ⟨923478696890522728941497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9850439433498909108709301 923478696890522728941497)
                    ·
                      rfl

theorem cell23_5395405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5395405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395405 prefixEnd_5395405 := by exact prefixLift 5395405
  have htrace : WordTrace (prefixWord ++ tailWord_5395405) baseStart_5395405 baseEnd_5395405 := by
    simpa [prefixWord, tailWord_5395405, baseEnd_5395405] using wordTrace_append hprefix tailTrace_5395405
  have hstable : (prefixWord ++ tailWord_5395405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395405).length < 2 ^ (prefixWord ++ tailWord_5395405).sum := by decide
  have hdescent : baseEnd_5395405 < baseStart_5395405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395517 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_5395517 : Nat := 118140960795 + 5395517 * 2 ^ 59
def prefixEnd_5395517 : Nat := 4983230072969 + 3 ^ 40 * 5395517 * 2
def baseEnd_5395517 : Nat := 923497866834957249541325

theorem tailTrace_5395517 : CollatzResearch.WordTrace tailWord_5395517 prefixEnd_5395517 923497866834957249541325 := by
  unfold tailWord_5395517
  simp only [CollatzResearch.WordTrace]
  refine ⟨196790671993970864785864805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131193781329313909857243203 196790671993970864785864805)
  ·
    refine ⟨36898250998869537147349651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196790671993970864785864805 36898250998869537147349651)
    ·
      refine ⟨55347376498304305721024477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36898250998869537147349651 55347376498304305721024477)
      ·
        refine ⟨20755266186864114645384179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55347376498304305721024477 20755266186864114645384179)
        ·
          refine ⟨31132899280296171968076269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20755266186864114645384179 31132899280296171968076269)
          ·
            refine ⟨11674837230111064488028601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31132899280296171968076269 11674837230111064488028601)
            ·
              refine ⟨8756127922583298366021451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11674837230111064488028601 8756127922583298366021451)
              ·
                refine ⟨13134191883874947549032177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756127922583298366021451 13134191883874947549032177)
                ·
                  refine ⟨9850643912906210661774133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13134191883874947549032177 9850643912906210661774133)
                  ·
                    refine ⟨923497866834957249541325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9850643912906210661774133 923497866834957249541325)
                    ·
                      rfl

theorem cell23_5395517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_5395517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395517 prefixEnd_5395517 := by exact prefixLift 5395517
  have htrace : WordTrace (prefixWord ++ tailWord_5395517) baseStart_5395517 baseEnd_5395517 := by
    simpa [prefixWord, tailWord_5395517, baseEnd_5395517] using wordTrace_append hprefix tailTrace_5395517
  have hstable : (prefixWord ++ tailWord_5395517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395517).length < 2 ^ (prefixWord ++ tailWord_5395517).sum := by decide
  have hdescent : baseEnd_5395517 < baseStart_5395517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395554 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5395554 : Nat := 118140960795 + 5395554 * 2 ^ 59
def prefixEnd_5395554 : Nat := 4983230072969 + 3 ^ 40 * 5395554 * 2
def baseEnd_5395554 : Nat := 2770512599289088103861305

theorem tailTrace_5395554 : CollatzResearch.WordTrace tailWord_5395554 prefixEnd_5395554 2770512599289088103861305 := by
  unfold tailWord_5395554
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198005373709205026240429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131194680996557880069974477 49198005373709205026240429)
  ·
    refine ⟨18449252015140951884840161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49198005373709205026240429 18449252015140951884840161)
    ·
      refine ⟨13836939011355713913630121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18449252015140951884840161 13836939011355713913630121)
      ·
        refine ⟨10377704258516785435222591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13836939011355713913630121 10377704258516785435222591)
        ·
          refine ⟨15566556387775178152833887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10377704258516785435222591 15566556387775178152833887)
          ·
            refine ⟨23349834581662767229250831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15566556387775178152833887 23349834581662767229250831)
            ·
              refine ⟨35024751872494150843876247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23349834581662767229250831 35024751872494150843876247)
              ·
                refine ⟨52537127808741226265814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35024751872494150843876247 52537127808741226265814371)
                ·
                  refine ⟨78805691713111839398721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52537127808741226265814371 78805691713111839398721557)
                  ·
                    refine ⟨3694016799052117471815073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78805691713111839398721557 3694016799052117471815073)
                    ·
                      refine ⟨2770512599289088103861305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694016799052117471815073 2770512599289088103861305)
                      ·
                        rfl

theorem cell23_5395554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5395554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395554 prefixEnd_5395554 := by exact prefixLift 5395554
  have htrace : WordTrace (prefixWord ++ tailWord_5395554) baseStart_5395554 baseEnd_5395554 := by
    simpa [prefixWord, tailWord_5395554, baseEnd_5395554] using wordTrace_append hprefix tailTrace_5395554
  have hstable : (prefixWord ++ tailWord_5395554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395554).length < 2 ^ (prefixWord ++ tailWord_5395554).sum := by decide
  have hdescent : baseEnd_5395554 < baseStart_5395554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395587 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 3]
def baseStart_5395587 : Nat := 118140960795 + 5395587 * 2 ^ 59
def prefixEnd_5395587 : Nat := 4983230072969 + 3 ^ 40 * 5395587 * 2
def baseEnd_5395587 : Nat := 2770529544150686474748653

theorem tailTrace_5395587 : CollatzResearch.WordTrace tailWord_5395587 prefixEnd_5395587 2770529544150686474748653 := by
  unfold tailWord_5395587
  simp only [CollatzResearch.WordTrace]
  refine ⟨196793225103717266740913015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131195483402478177827275343 196793225103717266740913015)
  ·
    refine ⟨295189837655575900111369523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196793225103717266740913015 295189837655575900111369523)
    ·
      refine ⟨442784756483363850167054285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295189837655575900111369523 442784756483363850167054285)
      ·
        refine ⟨166044283681261443812645357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442784756483363850167054285 166044283681261443812645357)
        ·
          refine ⟨62266606380473041429742009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166044283681261443812645357 62266606380473041429742009)
          ·
            refine ⟨46699954785354781072306507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62266606380473041429742009 46699954785354781072306507)
            ·
              refine ⟨70049932178032171608459761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46699954785354781072306507 70049932178032171608459761)
              ·
                refine ⟨52537449133524128706344821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70049932178032171608459761 52537449133524128706344821)
                ·
                  refine ⟨4925385856267887066219827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52537449133524128706344821 4925385856267887066219827)
                  ·
                    refine ⟨7388078784401830599329741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925385856267887066219827 7388078784401830599329741)
                    ·
                      refine ⟨2770529544150686474748653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388078784401830599329741 2770529544150686474748653)
                      ·
                        rfl

theorem cell23_5395587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_5395587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395587 prefixEnd_5395587 := by exact prefixLift 5395587
  have htrace : WordTrace (prefixWord ++ tailWord_5395587) baseStart_5395587 baseEnd_5395587 := by
    simpa [prefixWord, tailWord_5395587, baseEnd_5395587] using wordTrace_append hprefix tailTrace_5395587
  have hstable : (prefixWord ++ tailWord_5395587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395587).length < 2 ^ (prefixWord ++ tailWord_5395587).sum := by decide
  have hdescent : baseEnd_5395587 < baseStart_5395587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395644 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_5395644 : Nat := 118140960795 + 5395644 * 2 ^ 59
def prefixEnd_5395644 : Nat := 4983230072969 + 3 ^ 40 * 5395644 * 2
def baseEnd_5395644 : Nat := 2770558812547992751735891

theorem tailTrace_5395644 : CollatzResearch.WordTrace tailWord_5395644 prefixEnd_5395644 2770558812547992751735891 := by
  unfold tailWord_5395644
  simp only [CollatzResearch.WordTrace]
  refine ⟨98397652032255382737868993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131196869376340510317158657 98397652032255382737868993)
  ·
    refine ⟨73798239024191537053401745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98397652032255382737868993 73798239024191537053401745)
    ·
      refine ⟨55348679268143652790051309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73798239024191537053401745 55348679268143652790051309)
      ·
        refine ⟨20755754725553869796269241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55348679268143652790051309 20755754725553869796269241)
        ·
          refine ⟨15566816044165402347201931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20755754725553869796269241 15566816044165402347201931)
          ·
            refine ⟨23350224066248103520802897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15566816044165402347201931 23350224066248103520802897)
            ·
              refine ⟨17512668049686077640602173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23350224066248103520802897 17512668049686077640602173)
              ·
                refine ⟨6567250518632279115225815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17512668049686077640602173 6567250518632279115225815)
                ·
                  refine ⟨9850875777948418672838723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567250518632279115225815 9850875777948418672838723)
                  ·
                    refine ⟨14776313666922628009258085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9850875777948418672838723 14776313666922628009258085)
                    ·
                      refine ⟨2770558812547992751735891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14776313666922628009258085 2770558812547992751735891)
                      ·
                        rfl

theorem cell23_5395644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_5395644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395644 prefixEnd_5395644 := by exact prefixLift 5395644
  have htrace : WordTrace (prefixWord ++ tailWord_5395644) baseStart_5395644 baseEnd_5395644 := by
    simpa [prefixWord, tailWord_5395644, baseEnd_5395644] using wordTrace_append hprefix tailTrace_5395644
  have hstable : (prefixWord ++ tailWord_5395644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395644).length < 2 ^ (prefixWord ++ tailWord_5395644).sum := by decide
  have hdescent : baseEnd_5395644 < baseStart_5395644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395681 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_5395681 : Nat := 118140960795 + 5395681 * 2 ^ 59
def prefixEnd_5395681 : Nat := 4983230072969 + 3 ^ 40 * 5395681 * 2
def baseEnd_5395681 : Nat := 2770577811332209106973221

theorem tailTrace_5395681 : CollatzResearch.WordTrace tailWord_5395681 prefixEnd_5395681 2770577811332209106973221 := by
  unfold tailWord_5395681
  simp only [CollatzResearch.WordTrace]
  refine ⟨196796653565376720794834897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131197769043584480529889931 196796653565376720794834897)
  ·
    refine ⟨147597490174032540596126173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196796653565376720794834897 147597490174032540596126173)
    ·
      refine ⟨55349058815262202723547315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147597490174032540596126173 55349058815262202723547315)
      ·
        refine ⟨83023588222893304085320973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55349058815262202723547315 83023588222893304085320973)
        ·
          refine ⟨31133845583584989031995365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83023588222893304085320973 31133845583584989031995365)
          ·
            refine ⟨5837596046922185443499131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31133845583584989031995365 5837596046922185443499131)
            ·
              refine ⟨8756394070383278165248697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837596046922185443499131 8756394070383278165248697)
              ·
                refine ⟨6567295552787458623936523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756394070383278165248697 6567295552787458623936523)
                ·
                  refine ⟨9850943329181187935904785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567295552787458623936523 9850943329181187935904785)
                  ·
                    refine ⟨7388207496885890951928589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9850943329181187935904785 7388207496885890951928589)
                    ·
                      refine ⟨2770577811332209106973221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388207496885890951928589 2770577811332209106973221)
                      ·
                        rfl

theorem cell23_5395681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_5395681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395681 prefixEnd_5395681 := by exact prefixLift 5395681
  have htrace : WordTrace (prefixWord ++ tailWord_5395681) baseStart_5395681 baseEnd_5395681 := by
    simpa [prefixWord, tailWord_5395681, baseEnd_5395681] using wordTrace_append hprefix tailTrace_5395681
  have hstable : (prefixWord ++ tailWord_5395681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395681).length < 2 ^ (prefixWord ++ tailWord_5395681).sum := by decide
  have hdescent : baseEnd_5395681 < baseStart_5395681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395694 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_5395694 : Nat := 118140960795 + 5395694 * 2 ^ 59
def prefixEnd_5395694 : Nat := 4983230072969 + 3 ^ 40 * 5395694 * 2
def baseEnd_5395694 : Nat := 2770584486580717556110661

theorem tailTrace_5395694 : CollatzResearch.WordTrace tailWord_5395694 prefixEnd_5395694 2770584486580717556110661 := by
  unfold tailWord_5395694
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599640964291203001882267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131198085142886416010038757 24599640964291203001882267)
  ·
    refine ⟨36899461446436804502823401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24599640964291203001882267 36899461446436804502823401)
    ·
      refine ⟨27674596084827603377117551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36899461446436804502823401 27674596084827603377117551)
      ·
        refine ⟨41511894127241405065676327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27674596084827603377117551 41511894127241405065676327)
        ·
          refine ⟨62267841190862107598514491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41511894127241405065676327 62267841190862107598514491)
          ·
            refine ⟨93401761786293161397771737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62267841190862107598514491 93401761786293161397771737)
            ·
              refine ⟨70051321339719871048328803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93401761786293161397771737 70051321339719871048328803)
              ·
                refine ⟨105076982009579806572493205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70051321339719871048328803 105076982009579806572493205)
                ·
                  refine ⟨4925483531699053433085619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105076982009579806572493205 4925483531699053433085619)
                  ·
                    refine ⟨7388225297548580149628429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925483531699053433085619 7388225297548580149628429)
                    ·
                      refine ⟨2770584486580717556110661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388225297548580149628429 2770584486580717556110661)
                      ·
                        rfl

theorem cell23_5395694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_5395694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395694 prefixEnd_5395694 := by exact prefixLift 5395694
  have htrace : WordTrace (prefixWord ++ tailWord_5395694) baseStart_5395694 baseEnd_5395694 := by
    simpa [prefixWord, tailWord_5395694, baseEnd_5395694] using wordTrace_append hprefix tailTrace_5395694
  have hstable : (prefixWord ++ tailWord_5395694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395694).length < 2 ^ (prefixWord ++ tailWord_5395694).sum := by decide
  have hdescent : baseEnd_5395694 < baseStart_5395694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395698 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5395698 : Nat := 118140960795 + 5395698 * 2 ^ 59
def prefixEnd_5395698 : Nat := 4983230072969 + 3 ^ 40 * 5395698 * 2
def baseEnd_5395698 : Nat := 2770586540503335540460643

theorem tailTrace_5395698 : CollatzResearch.WordTrace tailWord_5395698 prefixEnd_5395698 2770586540503335540460643 := by
  unfold tailWord_5395698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49199318401578783174550937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131198182404210088465469165 49199318401578783174550937)
  ·
    refine ⟨36899488801184087380913203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49199318401578783174550937 36899488801184087380913203)
    ·
      refine ⟨55349233201776131071369805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36899488801184087380913203 55349233201776131071369805)
      ·
        refine ⟨20755962450666049151763677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55349233201776131071369805 20755962450666049151763677)
        ·
          refine ⟨7783485918999768431911379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20755962450666049151763677 7783485918999768431911379)
          ·
            refine ⟨11675228878499652647867069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7783485918999768431911379 11675228878499652647867069)
            ·
              refine ⟨4378210829437369742950151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11675228878499652647867069 4378210829437369742950151)
              ·
                refine ⟨6567316244156054614425227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378210829437369742950151 6567316244156054614425227)
                ·
                  refine ⟨9850974366234081921637841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567316244156054614425227 9850974366234081921637841)
                  ·
                    refine ⟨7388230774675561441228381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9850974366234081921637841 7388230774675561441228381)
                    ·
                      refine ⟨2770586540503335540460643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388230774675561441228381 2770586540503335540460643)
                      ·
                        rfl

theorem cell23_5395698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5395698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395698 prefixEnd_5395698 := by exact prefixLift 5395698
  have htrace : WordTrace (prefixWord ++ tailWord_5395698) baseStart_5395698 baseEnd_5395698 := by
    simpa [prefixWord, tailWord_5395698, baseEnd_5395698] using wordTrace_append hprefix tailTrace_5395698
  have hstable : (prefixWord ++ tailWord_5395698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395698).length < 2 ^ (prefixWord ++ tailWord_5395698).sum := by decide
  have hdescent : baseEnd_5395698 < baseStart_5395698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395711 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_5395711 : Nat := 118140960795 + 5395711 * 2 ^ 59
def prefixEnd_5395711 : Nat := 4983230072969 + 3 ^ 40 * 5395711 * 2
def baseEnd_5395711 : Nat := 2770593215751843989598083

theorem tailTrace_5395711 : CollatzResearch.WordTrace tailWord_5395711 prefixEnd_5395711 2770593215751843989598083 := by
  unfold tailWord_5395711
  simp only [CollatzResearch.WordTrace]
  refine ⟨196797747755268035918426987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131198498503512023945617991 196797747755268035918426987)
  ·
    refine ⟨295196621632902053877640481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196797747755268035918426987 295196621632902053877640481)
    ·
      refine ⟨221397466224676540408230361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295196621632902053877640481 221397466224676540408230361)
      ·
        refine ⟨166048099668507405306172771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221397466224676540408230361 166048099668507405306172771)
        ·
          refine ⟨249072149502761107959259157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166048099668507405306172771 249072149502761107959259157)
          ·
            refine ⟨11675257007941926935590273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249072149502761107959259157 11675257007941926935590273)
            ·
              refine ⟨8756442755956445201692705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11675257007941926935590273 8756442755956445201692705)
              ·
                refine ⟨6567332066967333901269529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756442755956445201692705 6567332066967333901269529)
                ·
                  refine ⟨4925499050225500425952147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567332066967333901269529 4925499050225500425952147)
                  ·
                    refine ⟨7388248575338250638928221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925499050225500425952147 7388248575338250638928221)
                    ·
                      refine ⟨2770593215751843989598083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388248575338250638928221 2770593215751843989598083)
                      ·
                        rfl

theorem cell23_5395711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_5395711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395711 prefixEnd_5395711 := by exact prefixLift 5395711
  have htrace : WordTrace (prefixWord ++ tailWord_5395711) baseStart_5395711 baseEnd_5395711 := by
    simpa [prefixWord, tailWord_5395711, baseEnd_5395711] using wordTrace_append hprefix tailTrace_5395711
  have hstable : (prefixWord ++ tailWord_5395711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395711).length < 2 ^ (prefixWord ++ tailWord_5395711).sum := by decide
  have hdescent : baseEnd_5395711 < baseStart_5395711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395764 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5395764 : Nat := 118140960795 + 5395764 * 2 ^ 59
def prefixEnd_5395764 : Nat := 4983230072969 + 3 ^ 40 * 5395764 * 2
def baseEnd_5395764 : Nat := 2770620430226532282235339

theorem tailTrace_5395764 : CollatzResearch.WordTrace tailWord_5395764 prefixEnd_5395764 2770620430226532282235339 := by
  unfold tailWord_5395764
  simp only [CollatzResearch.WordTrace]
  refine ⟨98399840412038012985053173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131199787216050683980070897 98399840412038012985053173)
  ·
    refine ⟨9224985038628563717348735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98399840412038012985053173 9224985038628563717348735)
    ·
      refine ⟨13837477557942845576023103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9224985038628563717348735 13837477557942845576023103)
      ·
        refine ⟨20756216336914268364034655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13837477557942845576023103 20756216336914268364034655)
        ·
          refine ⟨31134324505371402546051983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20756216336914268364034655 31134324505371402546051983)
          ·
            refine ⟨46701486758057103819077975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31134324505371402546051983 46701486758057103819077975)
            ·
              refine ⟨70052230137085655728616963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46701486758057103819077975 70052230137085655728616963)
              ·
                refine ⟨105078345205628483592925445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70052230137085655728616963 105078345205628483592925445)
                ·
                  refine ⟨19702189726055340673673521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105078345205628483592925445 19702189726055340673673521)
                  ·
                    refine ⟨14776642294541505505255141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19702189726055340673673521 14776642294541505505255141)
                    ·
                      refine ⟨2770620430226532282235339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14776642294541505505255141 2770620430226532282235339)
                      ·
                        rfl

theorem cell23_5395764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5395764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395764 prefixEnd_5395764 := by exact prefixLift 5395764
  have htrace : WordTrace (prefixWord ++ tailWord_5395764) baseStart_5395764 baseEnd_5395764 := by
    simpa [prefixWord, tailWord_5395764, baseEnd_5395764] using wordTrace_append hprefix tailTrace_5395764
  have hstable : (prefixWord ++ tailWord_5395764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395764).length < 2 ^ (prefixWord ++ tailWord_5395764).sum := by decide
  have hdescent : baseEnd_5395764 < baseStart_5395764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395774 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_5395774 : Nat := 118140960795 + 5395774 * 2 ^ 59
def prefixEnd_5395774 : Nat := 4983230072969 + 3 ^ 40 * 5395774 * 2
def baseEnd_5395774 : Nat := 307847285003675249234477

theorem tailTrace_5395774 : CollatzResearch.WordTrace tailWord_5395774 prefixEnd_5395774 307847285003675249234477 := by
  unfold tailWord_5395774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600005694254974709746297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131200030369359865118646917 24600005694254974709746297)
  ·
    refine ⟨18450004270691231032309723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24600005694254974709746297 18450004270691231032309723)
    ·
      refine ⟨27675006406036846548464585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450004270691231032309723 27675006406036846548464585)
      ·
        refine ⟨20756254804527634911348439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27675006406036846548464585 20756254804527634911348439)
        ·
          refine ⟨31134382206791452367022659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20756254804527634911348439 31134382206791452367022659)
          ·
            refine ⟨46701573310187178550533989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31134382206791452367022659 46701573310187178550533989)
            ·
              refine ⟨8756544995660095978225123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46701573310187178550533989 8756544995660095978225123)
              ·
                refine ⟨13134817493490143967337685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756544995660095978225123 13134817493490143967337685)
                ·
                  refine ⟨307847285003675249234477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13134817493490143967337685 307847285003675249234477)
                  ·
                    rfl

theorem cell23_5395774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_5395774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395774 prefixEnd_5395774 := by exact prefixLift 5395774
  have htrace : WordTrace (prefixWord ++ tailWord_5395774) baseStart_5395774 baseEnd_5395774 := by
    simpa [prefixWord, tailWord_5395774, baseEnd_5395774] using wordTrace_append hprefix tailTrace_5395774
  have hstable : (prefixWord ++ tailWord_5395774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395774).length < 2 ^ (prefixWord ++ tailWord_5395774).sum := by decide
  have hdescent : baseEnd_5395774 < baseStart_5395774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395824 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_5395824 : Nat := 118140960795 + 5395824 * 2 ^ 59
def prefixEnd_5395824 : Nat := 4983230072969 + 3 ^ 40 * 5395824 * 2
def baseEnd_5395824 : Nat := 2770651239065802047485063

theorem tailTrace_5395824 : CollatzResearch.WordTrace tailWord_5395824 prefixEnd_5395824 2770651239065802047485063 := by
  unfold tailWord_5395824
  simp only [CollatzResearch.WordTrace]
  refine ⟨98400934601929328108645263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131201246135905770811527017 98400934601929328108645263)
  ·
    refine ⟨147601401902893992162967895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98400934601929328108645263 147601401902893992162967895)
    ·
      refine ⟨221402102854340988244451843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147601401902893992162967895 221402102854340988244451843)
      ·
        refine ⟨332103154281511482366677765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221402102854340988244451843 332103154281511482366677765)
        ·
          refine ⟨62269341427783402943752081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332103154281511482366677765 62269341427783402943752081)
          ·
            refine ⟨46702006070837552207814061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62269341427783402943752081 46702006070837552207814061)
            ·
              refine ⟨17513252276564082077930273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46702006070837552207814061 17513252276564082077930273)
              ·
                refine ⟨13134939207423061558447705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17513252276564082077930273 13134939207423061558447705)
                ·
                  refine ⟨9851204405567296168835779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13134939207423061558447705 9851204405567296168835779)
                  ·
                    refine ⟨14776806608350944253253669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9851204405567296168835779 14776806608350944253253669)
                    ·
                      refine ⟨2770651239065802047485063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14776806608350944253253669 2770651239065802047485063)
                      ·
                        rfl

theorem cell23_5395824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_5395824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395824 prefixEnd_5395824 := by exact prefixLift 5395824
  have htrace : WordTrace (prefixWord ++ tailWord_5395824) baseStart_5395824 baseEnd_5395824 := by
    simpa [prefixWord, tailWord_5395824, baseEnd_5395824] using wordTrace_append hprefix tailTrace_5395824
  have hstable : (prefixWord ++ tailWord_5395824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395824).length < 2 ^ (prefixWord ++ tailWord_5395824).sum := by decide
  have hdescent : baseEnd_5395824 < baseStart_5395824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395885 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5395885 : Nat := 118140960795 + 5395885 * 2 ^ 59
def prefixEnd_5395885 : Nat := 4983230072969 + 3 ^ 40 * 5395885 * 2
def baseEnd_5395885 : Nat := 923560853795242102940761

theorem tailTrace_5395885 : CollatzResearch.WordTrace tailWord_5395885 prefixEnd_5395885 923560853795242102940761 := by
  unfold tailWord_5395885
  simp only [CollatzResearch.WordTrace]
  refine ⟨196804094056637663635261109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131202729371091775756840739 196804094056637663635261109)
  ·
    refine ⟨18450383817809780965805729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196804094056637663635261109 18450383817809780965805729)
    ·
      refine ⟨13837787863357335724354297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18450383817809780965805729 13837787863357335724354297)
      ·
        refine ⟨10378340897518001793265723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13837787863357335724354297 10378340897518001793265723)
        ·
          refine ⟨15567511346277002689898585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378340897518001793265723 15567511346277002689898585)
          ·
            refine ⟨11675633509707752017423939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15567511346277002689898585 11675633509707752017423939)
            ·
              refine ⟨17513450264561628026135909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11675633509707752017423939 17513450264561628026135909)
              ·
                refine ⟨3283771924605305254900483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17513450264561628026135909 3283771924605305254900483)
                ·
                  refine ⟨4925657886907957882350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283771924605305254900483 4925657886907957882350725)
                  ·
                    refine ⟨923560853795242102940761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925657886907957882350725 923560853795242102940761)
                    ·
                      rfl

theorem cell23_5395885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5395885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395885 prefixEnd_5395885 := by exact prefixLift 5395885
  have htrace : WordTrace (prefixWord ++ tailWord_5395885) baseStart_5395885 baseEnd_5395885 := by
    simpa [prefixWord, tailWord_5395885, baseEnd_5395885] using wordTrace_append hprefix tailTrace_5395885
  have hstable : (prefixWord ++ tailWord_5395885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395885).length < 2 ^ (prefixWord ++ tailWord_5395885).sum := by decide
  have hdescent : baseEnd_5395885 < baseStart_5395885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395887 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_5395887 : Nat := 118140960795 + 5395887 * 2 ^ 59
def prefixEnd_5395887 : Nat := 4983230072969 + 3 ^ 40 * 5395887 * 2
def baseEnd_5395887 : Nat := 2770683588347035300997273

theorem tailTrace_5395887 : CollatzResearch.WordTrace tailWord_5395887 prefixEnd_5395887 2770683588347035300997273 := by
  unfold tailWord_5395887
  simp only [CollatzResearch.WordTrace]
  refine ⟨196804167002630417976833915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131202778001753611984555943 196804167002630417976833915)
  ·
    refine ⟨295206250503945626965250873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196804167002630417976833915 295206250503945626965250873)
    ·
      refine ⟨221404687877959220223938155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295206250503945626965250873 221404687877959220223938155)
      ·
        refine ⟨332107031816938830335907233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221404687877959220223938155 332107031816938830335907233)
        ·
          refine ⟨249080273862704122751930425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332107031816938830335907233 249080273862704122751930425)
          ·
            refine ⟨186810205397028092063947819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249080273862704122751930425 186810205397028092063947819)
            ·
              refine ⟨280215308095542138095921729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186810205397028092063947819 280215308095542138095921729)
              ·
                refine ⟨210161481071656603571941297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280215308095542138095921729 210161481071656603571941297)
                ·
                  refine ⟨157621110803742452678955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210161481071656603571941297 157621110803742452678955973)
                  ·
                    refine ⟨29553958275701709877304245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157621110803742452678955973 29553958275701709877304245)
                    ·
                      refine ⟨2770683588347035300997273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29553958275701709877304245 2770683588347035300997273)
                      ·
                        rfl

theorem cell23_5395887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_5395887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395887 prefixEnd_5395887 := by exact prefixLift 5395887
  have htrace : WordTrace (prefixWord ++ tailWord_5395887) baseStart_5395887 baseEnd_5395887 := by
    simpa [prefixWord, tailWord_5395887, baseEnd_5395887] using wordTrace_append hprefix tailTrace_5395887
  have hstable : (prefixWord ++ tailWord_5395887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395887).length < 2 ^ (prefixWord ++ tailWord_5395887).sum := by decide
  have hdescent : baseEnd_5395887 < baseStart_5395887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395901 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5395901 : Nat := 118140960795 + 5395901 * 2 ^ 59
def prefixEnd_5395901 : Nat := 4983230072969 + 3 ^ 40 * 5395901 * 2
def baseEnd_5395901 : Nat := 2770690777076198246222209

theorem tailTrace_5395901 : CollatzResearch.WordTrace tailWord_5395901 prefixEnd_5395901 2770690777076198246222209 := by
  unfold tailWord_5395901
  simp only [CollatzResearch.WordTrace]
  refine ⟨196804677624579698367843557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131203118416386465578562371 196804677624579698367843557)
  ·
    refine ⟨36900877054608693443970667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196804677624579698367843557 36900877054608693443970667)
    ·
      refine ⟨55351315581913040165956001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36900877054608693443970667 55351315581913040165956001)
      ·
        refine ⟨41513486686434780124467001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55351315581913040165956001 41513486686434780124467001)
        ·
          refine ⟨31135115014826085093350251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41513486686434780124467001 31135115014826085093350251)
          ·
            refine ⟨46702672522239127640025377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31135115014826085093350251 46702672522239127640025377)
            ·
              refine ⟨35027004391679345730019033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46702672522239127640025377 35027004391679345730019033)
              ·
                refine ⟨26270253293759509297514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35027004391679345730019033 26270253293759509297514275)
                ·
                  refine ⟨39405379940639263946271413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26270253293759509297514275 39405379940639263946271413)
                  ·
                    refine ⟨3694254369434930994962945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39405379940639263946271413 3694254369434930994962945)
                    ·
                      refine ⟨2770690777076198246222209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694254369434930994962945 2770690777076198246222209)
                      ·
                        rfl

theorem cell23_5395901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5395901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395901 prefixEnd_5395901 := by exact prefixLift 5395901
  have htrace : WordTrace (prefixWord ++ tailWord_5395901) baseStart_5395901 baseEnd_5395901 := by
    simpa [prefixWord, tailWord_5395901, baseEnd_5395901] using wordTrace_append hprefix tailTrace_5395901
  have hstable : (prefixWord ++ tailWord_5395901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395901).length < 2 ^ (prefixWord ++ tailWord_5395901).sum := by decide
  have hdescent : baseEnd_5395901 < baseStart_5395901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395908 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5395908 : Nat := 118140960795 + 5395908 * 2 ^ 59
def prefixEnd_5395908 : Nat := 4983230072969 + 3 ^ 40 * 5395908 * 2
def baseEnd_5395908 : Nat := 2770694371440779718834677

theorem tailTrace_5395908 : CollatzResearch.WordTrace tailWord_5395908 prefixEnd_5395908 2770694371440779718834677 := by
  unfold tailWord_5395908
  simp only [CollatzResearch.WordTrace]
  refine ⟨98402466467777169281674189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131203288623702892375565585 98402466467777169281674189)
  ·
    refine ⟨36900924925416438480627821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98402466467777169281674189 36900924925416438480627821)
    ·
      refine ⟨13837846847031164430235433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36900924925416438480627821 13837846847031164430235433)
      ·
        refine ⟨10378385135273373322676575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13837846847031164430235433 10378385135273373322676575)
        ·
          refine ⟨15567577702910059984014863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378385135273373322676575 15567577702910059984014863)
          ·
            refine ⟨23351366554365089976022295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15567577702910059984014863 23351366554365089976022295)
            ·
              refine ⟨35027049831547634964033443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23351366554365089976022295 35027049831547634964033443)
              ·
                refine ⟨52540574747321452446050165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35027049831547634964033443 52540574747321452446050165)
                ·
                  refine ⟨4925678882561386166817203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52540574747321452446050165 4925678882561386166817203)
                  ·
                    refine ⟨7388518323842079250225805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925678882561386166817203 7388518323842079250225805)
                    ·
                      refine ⟨2770694371440779718834677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388518323842079250225805 2770694371440779718834677)
                      ·
                        rfl

theorem cell23_5395908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5395908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395908 prefixEnd_5395908 := by exact prefixLift 5395908
  have htrace : WordTrace (prefixWord ++ tailWord_5395908) baseStart_5395908 baseEnd_5395908 := by
    simpa [prefixWord, tailWord_5395908, baseEnd_5395908] using wordTrace_append hprefix tailTrace_5395908
  have hstable : (prefixWord ++ tailWord_5395908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395908).length < 2 ^ (prefixWord ++ tailWord_5395908).sum := by decide
  have hdescent : baseEnd_5395908 < baseStart_5395908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395918 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_5395918 : Nat := 118140960795 + 5395918 * 2 ^ 59
def prefixEnd_5395918 : Nat := 4983230072969 + 3 ^ 40 * 5395918 * 2
def baseEnd_5395918 : Nat := 2770699506247324679709631

theorem tailTrace_5395918 : CollatzResearch.WordTrace tailWord_5395918 prefixEnd_5395918 2770699506247324679709631 := by
  unfold tailWord_5395918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600662208189763783901551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131203531777012073514141605 24600662208189763783901551)
  ·
    refine ⟨36900993312284645675852327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24600662208189763783901551 36900993312284645675852327)
    ·
      refine ⟨55351489968426968513778491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36900993312284645675852327 55351489968426968513778491)
      ·
        refine ⟨83027234952640452770667737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55351489968426968513778491 83027234952640452770667737)
        ·
          refine ⟨62270426214480339578000803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83027234952640452770667737 62270426214480339578000803)
          ·
            refine ⟨93405639321720509367001205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62270426214480339578000803 93405639321720509367001205)
            ·
              refine ⟨8756778686411297753156363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93405639321720509367001205 8756778686411297753156363)
              ·
                refine ⟨13135168029616946629734545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756778686411297753156363 13135168029616946629734545)
                ·
                  refine ⟨9851376022212709972300909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13135168029616946629734545 9851376022212709972300909)
                  ·
                    refine ⟨3694266008329766239612841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9851376022212709972300909 3694266008329766239612841)
                    ·
                      refine ⟨2770699506247324679709631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694266008329766239612841 2770699506247324679709631)
                      ·
                        rfl

theorem cell23_5395918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_5395918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395918 prefixEnd_5395918 := by exact prefixLift 5395918
  have htrace : WordTrace (prefixWord ++ tailWord_5395918) baseStart_5395918 baseEnd_5395918 := by
    simpa [prefixWord, tailWord_5395918, baseEnd_5395918] using wordTrace_append hprefix tailTrace_5395918
  have hstable : (prefixWord ++ tailWord_5395918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395918).length < 2 ^ (prefixWord ++ tailWord_5395918).sum := by decide
  have hdescent : baseEnd_5395918 < baseStart_5395918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395925 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5395925 : Nat := 118140960795 + 5395925 * 2 ^ 59
def prefixEnd_5395925 : Nat := 4983230072969 + 3 ^ 40 * 5395925 * 2
def baseEnd_5395925 : Nat := 2770703100611906152322099

theorem tailTrace_5395925 : CollatzResearch.WordTrace tailWord_5395925 prefixEnd_5395925 2770703100611906152322099 := by
  unfold tailWord_5395925
  simp only [CollatzResearch.WordTrace]
  refine ⟨196805552976492750466717229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131203701984328500311144819 196805552976492750466717229)
  ·
    refine ⟨73802082366184781425018961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196805552976492750466717229 73802082366184781425018961)
    ·
      refine ⟨55351561774638586068764221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73802082366184781425018961 55351561774638586068764221)
      ·
        refine ⟨20756835665489469775786583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55351561774638586068764221 20756835665489469775786583)
        ·
          refine ⟨31135253498234204663679875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20756835665489469775786583 31135253498234204663679875)
          ·
            refine ⟨46702880247351306995519813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31135253498234204663679875 46702880247351306995519813)
            ·
              refine ⟨8756790046378370061659965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46702880247351306995519813 8756790046378370061659965)
              ·
                refine ⟨3283796267391888773122487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8756790046378370061659965 3283796267391888773122487)
                ·
                  refine ⟨4925694401087833159683731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283796267391888773122487 4925694401087833159683731)
                  ·
                    refine ⟨7388541601631749739525597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4925694401087833159683731 7388541601631749739525597)
                    ·
                      refine ⟨2770703100611906152322099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388541601631749739525597 2770703100611906152322099)
                      ·
                        rfl

theorem cell23_5395925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5395925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395925 prefixEnd_5395925 := by exact prefixLift 5395925
  have htrace : WordTrace (prefixWord ++ tailWord_5395925) baseStart_5395925 baseEnd_5395925 := by
    simpa [prefixWord, tailWord_5395925, baseEnd_5395925] using wordTrace_append hprefix tailTrace_5395925
  have hstable : (prefixWord ++ tailWord_5395925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395925).length < 2 ^ (prefixWord ++ tailWord_5395925).sum := by decide
  have hdescent : baseEnd_5395925 < baseStart_5395925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395944 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5395944 : Nat := 118140960795 + 5395944 * 2 ^ 59
def prefixEnd_5395944 : Nat := 4983230072969 + 3 ^ 40 * 5395944 * 2
def baseEnd_5395944 : Nat := 2770712856744341577984511

theorem tailTrace_5395944 : CollatzResearch.WordTrace tailWord_5395944 prefixEnd_5395944 2770712856744341577984511 := by
  unfold tailWord_5395944
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403122981711958355829443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131204163975615944474439257 98403122981711958355829443)
  ·
    refine ⟨147604684472567937533744165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98403122981711958355829443 147604684472567937533744165)
    ·
      refine ⟨27675878338606488287577031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147604684472567937533744165 27675878338606488287577031)
      ·
        refine ⟨41513817507909732431365547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27675878338606488287577031 41513817507909732431365547)
        ·
          refine ⟨62270726261864598647048321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41513817507909732431365547 62270726261864598647048321)
          ·
            refine ⟨46703044696398448985286241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62270726261864598647048321 46703044696398448985286241)
            ·
              refine ⟨35027283522298836738964681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46703044696398448985286241 35027283522298836738964681)
              ·
                refine ⟨26270462641724127554223511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35027283522298836738964681 26270462641724127554223511)
                ·
                  refine ⟨39405693962586191331335267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26270462641724127554223511 39405693962586191331335267)
                  ·
                    refine ⟨59108540943879286997002901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39405693962586191331335267 59108540943879286997002901)
                    ·
                      refine ⟨2770712856744341577984511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59108540943879286997002901 2770712856744341577984511)
                      ·
                        rfl

theorem cell23_5395944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5395944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395944 prefixEnd_5395944 := by exact prefixLift 5395944
  have htrace : WordTrace (prefixWord ++ tailWord_5395944) baseStart_5395944 baseEnd_5395944 := by
    simpa [prefixWord, tailWord_5395944, baseEnd_5395944] using wordTrace_append hprefix tailTrace_5395944
  have hstable : (prefixWord ++ tailWord_5395944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395944).length < 2 ^ (prefixWord ++ tailWord_5395944).sum := by decide
  have hdescent : baseEnd_5395944 < baseStart_5395944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395958 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5395958 : Nat := 118140960795 + 5395958 * 2 ^ 59
def prefixEnd_5395958 : Nat := 4983230072969 + 3 ^ 40 * 5395958 * 2
def baseEnd_5395958 : Nat := 923573348491168174403149

theorem tailTrace_5395958 : CollatzResearch.WordTrace tailWord_5395958 prefixEnd_5395958 923573348491168174403149 := by
  unfold tailWord_5395958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300422286585824818916783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131204504390248798068445685 12300422286585824818916783)
  ·
    refine ⟨18450633429878737228375175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12300422286585824818916783 18450633429878737228375175)
    ·
      refine ⟨27675950144818105842562763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450633429878737228375175 27675950144818105842562763)
      ·
        refine ⟨41513925217227158763844145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27675950144818105842562763 41513925217227158763844145)
        ·
          refine ⟨31135443912920369072883109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41513925217227158763844145 31135443912920369072883109)
          ·
            refine ⟨5837895733672569201165583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31135443912920369072883109 5837895733672569201165583)
            ·
              refine ⟨8756843600508853801748375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837895733672569201165583 8756843600508853801748375)
              ·
                refine ⟨13135265400763280702622563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8756843600508853801748375 13135265400763280702622563)
                ·
                  refine ⟨19702898101144921053933845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13135265400763280702622563 19702898101144921053933845)
                  ·
                    refine ⟨923573348491168174403149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19702898101144921053933845 923573348491168174403149)
                    ·
                      rfl

theorem cell23_5395958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5395958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395958 prefixEnd_5395958 := by exact prefixLift 5395958
  have htrace : WordTrace (prefixWord ++ tailWord_5395958) baseStart_5395958 baseEnd_5395958 := by
    simpa [prefixWord, tailWord_5395958, baseEnd_5395958] using wordTrace_append hprefix tailTrace_5395958
  have hstable : (prefixWord ++ tailWord_5395958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395958).length < 2 ^ (prefixWord ++ tailWord_5395958).sum := by decide
  have hdescent : baseEnd_5395958 < baseStart_5395958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395988 : List Nat := [2, 4, 3, 1, 2, 2, 9]
def baseStart_5395988 : Nat := 118140960795 + 5395988 * 2 ^ 59
def prefixEnd_5395988 : Nat := 4983230072969 + 3 ^ 40 * 5395988 * 2
def baseEnd_5395988 : Nat := 34206610492507893899189

theorem tailTrace_5395988 : CollatzResearch.WordTrace tailWord_5395988 prefixEnd_5395988 34206610492507893899189 := by
  unfold tailWord_5395988
  simp only [CollatzResearch.WordTrace]
  refine ⟨98403925387632256113130309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131205233850176341484173745 98403925387632256113130309)
  ·
    refine ⟨18450736010181048021211933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98403925387632256113130309 18450736010181048021211933)
    ·
      refine ⟨6919026003817893007954475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18450736010181048021211933 6919026003817893007954475)
      ·
        refine ⟨10378539005726839511931713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919026003817893007954475 10378539005726839511931713)
        ·
          refine ⟨7783904254295129633948785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10378539005726839511931713 7783904254295129633948785)
          ·
            refine ⟨5837928190721347225461589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7783904254295129633948785 5837928190721347225461589)
            ·
              refine ⟨34206610492507893899189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5837928190721347225461589 34206610492507893899189)
              ·
                rfl

theorem cell23_5395988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 9].length) (baseStart_5395988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395988 prefixEnd_5395988 := by exact prefixLift 5395988
  have htrace : WordTrace (prefixWord ++ tailWord_5395988) baseStart_5395988 baseEnd_5395988 := by
    simpa [prefixWord, tailWord_5395988, baseEnd_5395988] using wordTrace_append hprefix tailTrace_5395988
  have hstable : (prefixWord ++ tailWord_5395988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395988).length < 2 ^ (prefixWord ++ tailWord_5395988).sum := by decide
  have hdescent : baseEnd_5395988 < baseStart_5395988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5395994 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5395994 : Nat := 118140960795 + 5395994 * 2 ^ 59
def prefixEnd_5395994 : Nat := 4983230072969 + 3 ^ 40 * 5395994 * 2
def baseEnd_5395994 : Nat := 2770738530777066382359281

theorem tailTrace_5395994 : CollatzResearch.WordTrace tailWord_5395994 prefixEnd_5395994 2770738530777066382359281 := by
  unfold tailWord_5395994
  simp only [CollatzResearch.WordTrace]
  refine ⟨49202017403310693812744759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131205379742161850167319357 49202017403310693812744759)
  ·
    refine ⟨73803026104966040719117139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49202017403310693812744759 73803026104966040719117139)
    ·
      refine ⟨110704539157449061078675709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73803026104966040719117139 110704539157449061078675709)
      ·
        refine ⟨41514202184043397904503391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110704539157449061078675709 41514202184043397904503391)
        ·
          refine ⟨62271303276065096856755087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41514202184043397904503391 62271303276065096856755087)
          ·
            refine ⟨93406954914097645285132631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62271303276065096856755087 93406954914097645285132631)
            ·
              refine ⟨140110432371146467927698947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93406954914097645285132631 140110432371146467927698947)
              ·
                refine ⟨210165648556719701891548421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140110432371146467927698947 210165648556719701891548421)
                ·
                  refine ⟨39406059104384944104665329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210165648556719701891548421 39406059104384944104665329)
                  ·
                    refine ⟨29554544328288708078498997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39406059104384944104665329 29554544328288708078498997)
                    ·
                      refine ⟨2770738530777066382359281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29554544328288708078498997 2770738530777066382359281)
                      ·
                        rfl

theorem cell23_5395994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5395994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5395994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5395994 prefixEnd_5395994 := by exact prefixLift 5395994
  have htrace : WordTrace (prefixWord ++ tailWord_5395994) baseStart_5395994 baseEnd_5395994 := by
    simpa [prefixWord, tailWord_5395994, baseEnd_5395994] using wordTrace_append hprefix tailTrace_5395994
  have hstable : (prefixWord ++ tailWord_5395994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5395994).length < 2 ^ (prefixWord ++ tailWord_5395994).sum := by decide
  have hdescent : baseEnd_5395994 < baseStart_5395994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5395994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396025 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5396025 : Nat := 118140960795 + 5396025 * 2 ^ 59
def prefixEnd_5396025 : Nat := 4983230072969 + 3 ^ 40 * 5396025 * 2
def baseEnd_5396025 : Nat := 2770754448677355761071639

theorem tailTrace_5396025 : CollatzResearch.WordTrace tailWord_5396025 prefixEnd_5396025 2770754448677355761071639 := by
  unfold tailWord_5396025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196809200276130467545357529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131206133517420311696905019 196809200276130467545357529)
  ·
    refine ⟨147606900207097850659018147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196809200276130467545357529 147606900207097850659018147)
    ·
      refine ⟨221410350310646775988527221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147606900207097850659018147 221410350310646775988527221)
      ·
        refine ⟨20757220341623135248924427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221410350310646775988527221 20757220341623135248924427)
        ·
          refine ⟨31135830512434702873386641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20757220341623135248924427 31135830512434702873386641)
          ·
            refine ⟨23351872884326027155039981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31135830512434702873386641 23351872884326027155039981)
            ·
              refine ⟨8756952331622260183139993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23351872884326027155039981 8756952331622260183139993)
              ·
                refine ⟨6567714248716695137354995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756952331622260183139993 6567714248716695137354995)
                ·
                  refine ⟨9851571373075042706032493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567714248716695137354995 9851571373075042706032493)
                  ·
                    refine ⟨3694339264903141014762185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9851571373075042706032493 3694339264903141014762185)
                    ·
                      refine ⟨2770754448677355761071639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694339264903141014762185 2770754448677355761071639)
                      ·
                        rfl

theorem cell23_5396025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5396025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396025 prefixEnd_5396025 := by exact prefixLift 5396025
  have htrace : WordTrace (prefixWord ++ tailWord_5396025) baseStart_5396025 baseEnd_5396025 := by
    simpa [prefixWord, tailWord_5396025, baseEnd_5396025] using wordTrace_append hprefix tailTrace_5396025
  have hstable : (prefixWord ++ tailWord_5396025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396025).length < 2 ^ (prefixWord ++ tailWord_5396025).sum := by decide
  have hdescent : baseEnd_5396025 < baseStart_5396025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396055 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_5396055 : Nat := 118140960795 + 5396055 * 2 ^ 59
def prefixEnd_5396055 : Nat := 4983230072969 + 3 ^ 40 * 5396055 * 2
def baseEnd_5396055 : Nat := 2770769853096990643696501

theorem tailTrace_5396055 : CollatzResearch.WordTrace tailWord_5396055 prefixEnd_5396055 2770769853096990643696501 := by
  unfold tailWord_5396055
  simp only [CollatzResearch.WordTrace]
  refine ⟨196810294466021782668949619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131206862977347855112633079 196810294466021782668949619)
  ·
    refine ⟨295215441699032674003424429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196810294466021782668949619 295215441699032674003424429)
    ·
      refine ⟨110705790637137252751284161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295215441699032674003424429 110705790637137252751284161)
      ·
        refine ⟨83029342977852939563463121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110705790637137252751284161 83029342977852939563463121)
        ·
          refine ⟨62272007233389704672597341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83029342977852939563463121 62272007233389704672597341)
          ·
            refine ⟨23352002712521139252224003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62272007233389704672597341 23352002712521139252224003)
            ·
              refine ⟨35028004068781708878336005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23352002712521139252224003 35028004068781708878336005)
              ·
                refine ⟨6567750762896570414688001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35028004068781708878336005 6567750762896570414688001)
                ·
                  refine ⟨4925813072172427811016001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567750762896570414688001 4925813072172427811016001)
                  ·
                    refine ⟨3694359804129320858262001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4925813072172427811016001 3694359804129320858262001)
                    ·
                      refine ⟨2770769853096990643696501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694359804129320858262001 2770769853096990643696501)
                      ·
                        rfl

theorem cell23_5396055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_5396055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396055 prefixEnd_5396055 := by exact prefixLift 5396055
  have htrace : WordTrace (prefixWord ++ tailWord_5396055) baseStart_5396055 baseEnd_5396055 := by
    simpa [prefixWord, tailWord_5396055, baseEnd_5396055] using wordTrace_append hprefix tailTrace_5396055
  have hstable : (prefixWord ++ tailWord_5396055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396055).length < 2 ^ (prefixWord ++ tailWord_5396055).sum := by decide
  have hdescent : baseEnd_5396055 < baseStart_5396055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396064 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_5396064 : Nat := 118140960795 + 5396064 * 2 ^ 59
def prefixEnd_5396064 : Nat := 4983230072969 + 3 ^ 40 * 5396064 * 2
def baseEnd_5396064 : Nat := 2770774474422881108483959

theorem tailTrace_5396064 : CollatzResearch.WordTrace tailWord_5396064 prefixEnd_5396064 2770774474422881108483959 := by
  unfold tailWord_5396064
  simp only [CollatzResearch.WordTrace]
  refine ⟨98405311361494588603013623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131207081815326118137351497 98405311361494588603013623)
  ·
    refine ⟨147607967042241882904520435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98405311361494588603013623 147607967042241882904520435)
    ·
      refine ⟨221411950563362824356780653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147607967042241882904520435 221411950563362824356780653)
      ·
        refine ⟨83029481461261059133792745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221411950563362824356780653 83029481461261059133792745)
        ·
          refine ⟨62272111095945794350344559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83029481461261059133792745 62272111095945794350344559)
          ·
            refine ⟨93408166643918691525516839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62272111095945794350344559 93408166643918691525516839)
            ·
              refine ⟨140112249965878037288275259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93408166643918691525516839 140112249965878037288275259)
              ·
                refine ⟨210168374948817055932412889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140112249965878037288275259 210168374948817055932412889)
                ·
                  refine ⟨157626281211612791949309667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210168374948817055932412889 157626281211612791949309667)
                  ·
                    refine ⟨236439421817419187923964501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157626281211612791949309667 236439421817419187923964501)
                    ·
                      refine ⟨2770774474422881108483959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236439421817419187923964501 2770774474422881108483959)
                      ·
                        rfl

theorem cell23_5396064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_5396064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396064 prefixEnd_5396064 := by exact prefixLift 5396064
  have htrace : WordTrace (prefixWord ++ tailWord_5396064) baseStart_5396064 baseEnd_5396064 := by
    simpa [prefixWord, tailWord_5396064, baseEnd_5396064] using wordTrace_append hprefix tailTrace_5396064
  have hstable : (prefixWord ++ tailWord_5396064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396064).length < 2 ^ (prefixWord ++ tailWord_5396064).sum := by decide
  have hdescent : baseEnd_5396064 < baseStart_5396064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396071 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_5396071 : Nat := 118140960795 + 5396071 * 2 ^ 59
def prefixEnd_5396071 : Nat := 4983230072969 + 3 ^ 40 * 5396071 * 2
def baseEnd_5396071 : Nat := 2770778068787462581096427

theorem tailTrace_5396071 : CollatzResearch.WordTrace tailWord_5396071 prefixEnd_5396071 2770778068787462581096427 := by
  unfold tailWord_5396071
  simp only [CollatzResearch.WordTrace]
  refine ⟨196810878033963817401532067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131207252022642544934354711 196810878033963817401532067)
  ·
    refine ⟨295216317050945726102298101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196810878033963817401532067 295216317050945726102298101)
    ·
      refine ⟨27676529723526161822090447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295216317050945726102298101 27676529723526161822090447)
      ·
        refine ⟨41514794585289242733135671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27676529723526161822090447 41514794585289242733135671)
        ·
          refine ⟨62272191877933864099703507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41514794585289242733135671 62272191877933864099703507)
          ·
            refine ⟨93408287816900796149555261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62272191877933864099703507 93408287816900796149555261)
            ·
              refine ⟨35028107931337798556083223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93408287816900796149555261 35028107931337798556083223)
              ·
                refine ⟨52542161897006697834124835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35028107931337798556083223 52542161897006697834124835)
                ·
                  refine ⟨78813242845510046751187253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52542161897006697834124835 78813242845510046751187253)
                  ·
                    refine ⟨7388741516766566882923805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78813242845510046751187253 7388741516766566882923805)
                    ·
                      refine ⟨2770778068787462581096427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388741516766566882923805 2770778068787462581096427)
                      ·
                        rfl

theorem cell23_5396071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_5396071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396071 prefixEnd_5396071 := by exact prefixLift 5396071
  have htrace : WordTrace (prefixWord ++ tailWord_5396071) baseStart_5396071 baseEnd_5396071 := by
    simpa [prefixWord, tailWord_5396071, baseEnd_5396071] using wordTrace_append hprefix tailTrace_5396071
  have hstable : (prefixWord ++ tailWord_5396071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396071).length < 2 ^ (prefixWord ++ tailWord_5396071).sum := by decide
  have hdescent : baseEnd_5396071 < baseStart_5396071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396072 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5396072 : Nat := 118140960795 + 5396072 * 2 ^ 59
def prefixEnd_5396072 : Nat := 4983230072969 + 3 ^ 40 * 5396072 * 2
def baseEnd_5396072 : Nat := 2770778582268117077183923

theorem tailTrace_5396072 : CollatzResearch.WordTrace tailWord_5396072 prefixEnd_5396072 2770778582268117077183923 := by
  unfold tailWord_5396072
  simp only [CollatzResearch.WordTrace]
  refine ⟨98405457253480097286159235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131207276337973463048212313 98405457253480097286159235)
  ·
    refine ⟨147608185880220145929238853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98405457253480097286159235 147608185880220145929238853)
    ·
      refine ⟨27676534852541277361732285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147608185880220145929238853 27676534852541277361732285)
      ·
        refine ⟨10378700569702979010649607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27676534852541277361732285 10378700569702979010649607)
        ·
          refine ⟨15568050854554468515974411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378700569702979010649607 15568050854554468515974411)
          ·
            refine ⟨23352076281831702773961617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568050854554468515974411 23352076281831702773961617)
            ·
              refine ⟨17514057211373777080471213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23352076281831702773961617 17514057211373777080471213)
              ·
                refine ⟨6567771454265166405176705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17514057211373777080471213 6567771454265166405176705)
                ·
                  refine ⟨4925828590698874803882529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567771454265166405176705 4925828590698874803882529)
                  ·
                    refine ⟨3694371443024156102911897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4925828590698874803882529 3694371443024156102911897)
                    ·
                      refine ⟨2770778582268117077183923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694371443024156102911897 2770778582268117077183923)
                      ·
                        rfl

theorem cell23_5396072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5396072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396072 prefixEnd_5396072 := by exact prefixLift 5396072
  have htrace : WordTrace (prefixWord ++ tailWord_5396072) baseStart_5396072 baseEnd_5396072 := by
    simpa [prefixWord, tailWord_5396072, baseEnd_5396072] using wordTrace_append hprefix tailTrace_5396072
  have hstable : (prefixWord ++ tailWord_5396072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396072).length < 2 ^ (prefixWord ++ tailWord_5396072).sum := by decide
  have hdescent : baseEnd_5396072 < baseStart_5396072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396078 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_5396078 : Nat := 118140960795 + 5396078 * 2 ^ 59
def prefixEnd_5396078 : Nat := 4983230072969 + 3 ^ 40 * 5396078 * 2
def baseEnd_5396078 : Nat := 307864629239116005967655

theorem tailTrace_5396078 : CollatzResearch.WordTrace tailWord_5396078 prefixEnd_5396078 307864629239116005967655 := by
  unfold tailWord_5396078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24601391668117307199629611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131207422229958971731357925 24601391668117307199629611)
  ·
    refine ⟨36902087502175960799444417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24601391668117307199629611 36902087502175960799444417)
    ·
      refine ⟨27676565626631970599583313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36902087502175960799444417 27676565626631970599583313)
      ·
        refine ⟨20757424219973977949687485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27676565626631970599583313 20757424219973977949687485)
        ·
          refine ⟨7784034082490241731132807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20757424219973977949687485 7784034082490241731132807)
          ·
            refine ⟨11676051123735362596699211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784034082490241731132807 11676051123735362596699211)
            ·
              refine ⟨17514076685603043895048817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11676051123735362596699211 17514076685603043895048817)
              ·
                refine ⟨13135557514202282921286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17514076685603043895048817 13135557514202282921286613)
                ·
                  refine ⟨307864629239116005967655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13135557514202282921286613 307864629239116005967655)
                  ·
                    rfl

theorem cell23_5396078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_5396078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396078 prefixEnd_5396078 := by exact prefixLift 5396078
  have htrace : WordTrace (prefixWord ++ tailWord_5396078) baseStart_5396078 baseEnd_5396078 := by
    simpa [prefixWord, tailWord_5396078, baseEnd_5396078] using wordTrace_append hprefix tailTrace_5396078
  have hstable : (prefixWord ++ tailWord_5396078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396078).length < 2 ^ (prefixWord ++ tailWord_5396078).sum := by decide
  have hdescent : baseEnd_5396078 < baseStart_5396078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396131 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3]
def baseStart_5396131 : Nat := 118140960795 + 5396131 * 2 ^ 59
def prefixEnd_5396131 : Nat := 4983230072969 + 3 ^ 40 * 5396131 * 2
def baseEnd_5396131 : Nat := 2770808877626732346346151

theorem tailTrace_5396131 : CollatzResearch.WordTrace tailWord_5396131 prefixEnd_5396131 2770808877626732346346151 := by
  unfold tailWord_5396131
  simp only [CollatzResearch.WordTrace]
  refine ⟨196813066413746447648716247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131208710942497631765810831 196813066413746447648716247)
  ·
    refine ⟨295219599620619671473074371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196813066413746447648716247 295219599620619671473074371)
    ·
      refine ⟨442829399430929507209611557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295219599620619671473074371 442829399430929507209611557)
      ·
        refine ⟨83030512393299282601802167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442829399430929507209611557 83030512393299282601802167)
        ·
          refine ⟨124545768589948923902703251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83030512393299282601802167 124545768589948923902703251)
          ·
            refine ⟨186818652884923385854054877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124545768589948923902703251 186818652884923385854054877)
            ·
              refine ⟨70056994831846269695270579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186818652884923385854054877 70056994831846269695270579)
              ·
                refine ⟨105085492247769404542905869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70056994831846269695270579 105085492247769404542905869)
                ·
                  refine ⟨39407059592913526703589701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105085492247769404542905869 39407059592913526703589701)
                  ·
                    refine ⟨7388823673671286256923069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39407059592913526703589701 7388823673671286256923069)
                    ·
                      refine ⟨2770808877626732346346151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388823673671286256923069 2770808877626732346346151)
                      ·
                        rfl

theorem cell23_5396131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_5396131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396131 prefixEnd_5396131 := by exact prefixLift 5396131
  have htrace : WordTrace (prefixWord ++ tailWord_5396131) baseStart_5396131 baseEnd_5396131 := by
    simpa [prefixWord, tailWord_5396131, baseEnd_5396131] using wordTrace_append hprefix tailTrace_5396131
  have hstable : (prefixWord ++ tailWord_5396131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396131).length < 2 ^ (prefixWord ++ tailWord_5396131).sum := by decide
  have hdescent : baseEnd_5396131 < baseStart_5396131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396151 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 8]
def baseStart_5396151 : Nat := 118140960795 + 5396151 * 2 ^ 59
def prefixEnd_5396151 : Nat := 4983230072969 + 3 ^ 40 * 5396151 * 2
def baseEnd_5396151 : Nat := 307868794137758029788451

theorem tailTrace_5396151 : CollatzResearch.WordTrace tailWord_5396151 prefixEnd_5396151 307868794137758029788451 := by
  unfold tailWord_5396151
  simp only [CollatzResearch.WordTrace]
  refine ⟨196813795873673991064444307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131209197249115994042962871 196813795873673991064444307)
  ·
    refine ⟨295220693810510986596666461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196813795873673991064444307 295220693810510986596666461)
    ·
      refine ⟨110707760178941619973749923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295220693810510986596666461 110707760178941619973749923)
      ·
        refine ⟨166061640268412429960624885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110707760178941619973749923 166061640268412429960624885)
        ·
          refine ⟨15568278775163665308808583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166061640268412429960624885 15568278775163665308808583)
          ·
            refine ⟨23352418162745497963212875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568278775163665308808583 23352418162745497963212875)
            ·
              refine ⟨35028627244118246944819313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23352418162745497963212875 35028627244118246944819313)
              ·
                refine ⟨26271470433088685208614485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35028627244118246944819313 26271470433088685208614485)
                ·
                  refine ⟨307868794137758029788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26271470433088685208614485 307868794137758029788451)
                  ·
                    rfl

theorem cell23_5396151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 8].length) (baseStart_5396151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396151 prefixEnd_5396151 := by exact prefixLift 5396151
  have htrace : WordTrace (prefixWord ++ tailWord_5396151) baseStart_5396151 baseEnd_5396151 := by
    simpa [prefixWord, tailWord_5396151, baseEnd_5396151] using wordTrace_append hprefix tailTrace_5396151
  have hstable : (prefixWord ++ tailWord_5396151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396151).length < 2 ^ (prefixWord ++ tailWord_5396151).sum := by decide
  have hdescent : baseEnd_5396151 < baseStart_5396151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396172 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_5396172 : Nat := 118140960795 + 5396172 * 2 ^ 59
def prefixEnd_5396172 : Nat := 4983230072969 + 3 ^ 40 * 5396172 * 2
def baseEnd_5396172 : Nat := 923609976777855561977821

theorem tailTrace_5396172 : CollatzResearch.WordTrace tailWord_5396172 prefixEnd_5396172 923609976777855561977821 := by
  unfold tailWord_5396172
  simp only [CollatzResearch.WordTrace]
  refine ⟨98407280903298955825479385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131209707871065274433972513 98407280903298955825479385)
  ·
    refine ⟨73805460677474216869109539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98407280903298955825479385 73805460677474216869109539)
    ·
      refine ⟨110708191016211325303664309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73805460677474216869109539 110708191016211325303664309)
      ·
        refine ⟨10378892907769811747218529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110708191016211325303664309 10378892907769811747218529)
        ·
          refine ⟨7784169680827358810413897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10378892907769811747218529 7784169680827358810413897)
          ·
            refine ⟨5838127260620519107810423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784169680827358810413897 5838127260620519107810423)
            ·
              refine ⟨8757190890930778661715635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838127260620519107810423 8757190890930778661715635)
              ·
                refine ⟨13135786336396167992573453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757190890930778661715635 13135786336396167992573453)
                ·
                  refine ⟨4925919876148562997215045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13135786336396167992573453 4925919876148562997215045)
                  ·
                    refine ⟨923609976777855561977821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925919876148562997215045 923609976777855561977821)
                    ·
                      rfl

theorem cell23_5396172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_5396172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396172 prefixEnd_5396172 := by exact prefixLift 5396172
  have htrace : WordTrace (prefixWord ++ tailWord_5396172) baseStart_5396172 baseEnd_5396172 := by
    simpa [prefixWord, tailWord_5396172, baseEnd_5396172] using wordTrace_append hprefix tailTrace_5396172
  have hstable : (prefixWord ++ tailWord_5396172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396172).length < 2 ^ (prefixWord ++ tailWord_5396172).sum := by decide
  have hdescent : baseEnd_5396172 < baseStart_5396172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396185 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 6]
def baseStart_5396185 : Nat := 118140960795 + 5396185 * 2 ^ 59
def prefixEnd_5396185 : Nat := 4983230072969 + 3 ^ 40 * 5396185 * 2
def baseEnd_5396185 : Nat := 307870733953563903896767

theorem tailTrace_5396185 : CollatzResearch.WordTrace tailWord_5396185 prefixEnd_5396185 307870733953563903896767 := by
  unfold tailWord_5396185
  simp only [CollatzResearch.WordTrace]
  refine ⟨196815035955550814871182009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131210023970367209914121339 196815035955550814871182009)
  ·
    refine ⟨147611276966663111153386507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196815035955550814871182009 147611276966663111153386507)
    ·
      refine ⟨221416915449994666730079761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147611276966663111153386507 221416915449994666730079761)
      ·
        refine ⟨166062686587496000047559821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221416915449994666730079761 166062686587496000047559821)
        ·
          refine ⟨62273507470311000017834933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166062686587496000047559821 62273507470311000017834933)
          ·
            refine ⟨5838141325341656251672025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62273507470311000017834933 5838141325341656251672025)
            ·
              refine ⟨4378605994006242188754019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838141325341656251672025 4378605994006242188754019)
              ·
                refine ⟨6567908991009363283131029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378605994006242188754019 6567908991009363283131029)
                ·
                  refine ⟨307870733953563903896767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6567908991009363283131029 307870733953563903896767)
                  ·
                    rfl

theorem cell23_5396185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_5396185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396185 prefixEnd_5396185 := by exact prefixLift 5396185
  have htrace : WordTrace (prefixWord ++ tailWord_5396185) baseStart_5396185 baseEnd_5396185 := by
    simpa [prefixWord, tailWord_5396185, baseEnd_5396185] using wordTrace_append hprefix tailTrace_5396185
  have hstable : (prefixWord ++ tailWord_5396185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396185).length < 2 ^ (prefixWord ++ tailWord_5396185).sum := by decide
  have hdescent : baseEnd_5396185 < baseStart_5396185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396211 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 6]
def baseStart_5396211 : Nat := 118140960795 + 5396211 * 2 ^ 59
def prefixEnd_5396211 : Nat := 4983230072969 + 3 ^ 40 * 5396211 * 2
def baseEnd_5396211 : Nat := 923616652026364011115261

theorem tailTrace_5396211 : CollatzResearch.WordTrace tailWord_5396211 prefixEnd_5396211 923616652026364011115261 := by
  unfold tailWord_5396211
  simp only [CollatzResearch.WordTrace]
  refine ⟨196815984253456621311628487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131210656168971080874418991 196815984253456621311628487)
  ·
    refine ⟨295223976380184931967442731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196815984253456621311628487 295223976380184931967442731)
    ·
      refine ⟨442835964570277397951164097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295223976380184931967442731 442835964570277397951164097)
      ·
        refine ⟨332126973427708048463373073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442835964570277397951164097 332126973427708048463373073)
        ·
          refine ⟨249095230070781036347529805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332126973427708048463373073 249095230070781036347529805)
          ·
            refine ⟨93410711276542888630323677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249095230070781036347529805 93410711276542888630323677)
            ·
              refine ⟨35029016728703583236371379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93410711276542888630323677 35029016728703583236371379)
              ·
                refine ⟨52543525093055374854557069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35029016728703583236371379 52543525093055374854557069)
                ·
                  refine ⟨19703821909895765570458901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52543525093055374854557069 19703821909895765570458901)
                  ·
                    refine ⟨923616652026364011115261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19703821909895765570458901 923616652026364011115261)
                    ·
                      rfl

theorem cell23_5396211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_5396211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396211 prefixEnd_5396211 := by exact prefixLift 5396211
  have htrace : WordTrace (prefixWord ++ tailWord_5396211) baseStart_5396211 baseEnd_5396211 := by
    simpa [prefixWord, tailWord_5396211, baseEnd_5396211] using wordTrace_append hprefix tailTrace_5396211
  have hstable : (prefixWord ++ tailWord_5396211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396211).length < 2 ^ (prefixWord ++ tailWord_5396211).sum := by decide
  have hdescent : baseEnd_5396211 < baseStart_5396211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396238 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5396238 : Nat := 118140960795 + 5396238 * 2 ^ 59
def prefixEnd_5396238 : Nat := 4983230072969 + 3 ^ 40 * 5396238 * 2
def baseEnd_5396238 : Nat := 2770863820056763427708159

theorem tailTrace_5396238 : CollatzResearch.WordTrace tailWord_5396238 prefixEnd_5396238 2770863820056763427708159 := by
  unfold tailWord_5396238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602121128044850615357671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131211312682905869948574245 24602121128044850615357671)
  ·
    refine ⟨36903181692067275923036507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24602121128044850615357671 36903181692067275923036507)
    ·
      refine ⟨55354772538100913884554761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36903181692067275923036507 55354772538100913884554761)
      ·
        refine ⟨41516079403575685413416071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55354772538100913884554761 41516079403575685413416071)
        ·
          refine ⟨62274119105363528120124107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41516079403575685413416071 62274119105363528120124107)
          ·
            refine ⟨93411178658045292180186161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62274119105363528120124107 93411178658045292180186161)
            ·
              refine ⟨70058383993533969135139621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93411178658045292180186161 70058383993533969135139621)
              ·
                refine ⟨13135946998787619212838679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70058383993533969135139621 13135946998787619212838679)
                ·
                  refine ⟨19703920498181428819258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13135946998787619212838679 19703920498181428819258019)
                  ·
                    refine ⟨29555880747272143228887029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19703920498181428819258019 29555880747272143228887029)
                    ·
                      refine ⟨2770863820056763427708159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29555880747272143228887029 2770863820056763427708159)
                      ·
                        rfl

theorem cell23_5396238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5396238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396238 prefixEnd_5396238 := by exact prefixLift 5396238
  have htrace : WordTrace (prefixWord ++ tailWord_5396238) baseStart_5396238 baseEnd_5396238 := by
    simpa [prefixWord, tailWord_5396238, baseEnd_5396238] using wordTrace_append hprefix tailTrace_5396238
  have hstable : (prefixWord ++ tailWord_5396238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396238).length < 2 ^ (prefixWord ++ tailWord_5396238).sum := by decide
  have hdescent : baseEnd_5396238 < baseStart_5396238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396245 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_5396245 : Nat := 118140960795 + 5396245 * 2 ^ 59
def prefixEnd_5396245 : Nat := 4983230072969 + 3 ^ 40 * 5396245 * 2
def baseEnd_5396245 : Nat := 923622471473781633440209

theorem tailTrace_5396245 : CollatzResearch.WordTrace tailWord_5396245 prefixEnd_5396245 923622471473781633440209 := by
  unfold tailWord_5396245
  simp only [CollatzResearch.WordTrace]
  refine ⟨196817224335333445118366189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131211482890222296745577459 196817224335333445118366189)
  ·
    refine ⟨73806459125750041919387321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196817224335333445118366189 73806459125750041919387321)
    ·
      refine ⟨55354844344312531439540491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73806459125750041919387321 55354844344312531439540491)
      ·
        refine ⟨83032266516468797159310737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55354844344312531439540491 83032266516468797159310737)
        ·
          refine ⟨62274199887351597869483053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83032266516468797159310737 62274199887351597869483053)
          ·
            refine ⟨23352824957756849201056145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62274199887351597869483053 23352824957756849201056145)
            ·
              refine ⟨17514618718317636900792109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23352824957756849201056145 17514618718317636900792109)
              ·
                refine ⟨6567982019369113837797041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17514618718317636900792109 6567982019369113837797041)
                ·
                  refine ⟨4925986514526835378347781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6567982019369113837797041 4925986514526835378347781)
                  ·
                    refine ⟨923622471473781633440209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4925986514526835378347781 923622471473781633440209)
                    ·
                      rfl

theorem cell23_5396245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_5396245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396245 prefixEnd_5396245 := by exact prefixLift 5396245
  have htrace : WordTrace (prefixWord ++ tailWord_5396245) baseStart_5396245 baseEnd_5396245 := by
    simpa [prefixWord, tailWord_5396245, baseEnd_5396245] using wordTrace_append hprefix tailTrace_5396245
  have hstable : (prefixWord ++ tailWord_5396245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396245).length < 2 ^ (prefixWord ++ tailWord_5396245).sum := by decide
  have hdescent : baseEnd_5396245 < baseStart_5396245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396248 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5396248 : Nat := 118140960795 + 5396248 * 2 ^ 59
def prefixEnd_5396248 : Nat := 4983230072969 + 3 ^ 40 * 5396248 * 2
def baseEnd_5396248 : Nat := 2770868954863308388583113

theorem tailTrace_5396248 : CollatzResearch.WordTrace tailWord_5396248 prefixEnd_5396248 2770868954863308388583113 := by
  unfold tailWord_5396248
  simp only [CollatzResearch.WordTrace]
  refine ⟨98408666877161288315362699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131211555836215051087150265 98408666877161288315362699)
  ·
    refine ⟨147613000315741932473044049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98408666877161288315362699 147613000315741932473044049)
    ·
      refine ⟨110709750236806449354783037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147613000315741932473044049 110709750236806449354783037)
      ·
        refine ⟨41516156338802418508043639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110709750236806449354783037 41516156338802418508043639)
        ·
          refine ⟨62274234508203627762065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41516156338802418508043639 62274234508203627762065459)
          ·
            refine ⟨93411351762305441643098189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62274234508203627762065459 93411351762305441643098189)
            ·
              refine ⟨35029256910864540616161821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93411351762305441643098189 35029256910864540616161821)
              ·
                refine ⟨13135971341574202731060683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35029256910864540616161821 13135971341574202731060683)
                ·
                  refine ⟨19703957012361304096591025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13135971341574202731060683 19703957012361304096591025)
                  ·
                    refine ⟨14777967759270978072443269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19703957012361304096591025 14777967759270978072443269)
                    ·
                      refine ⟨2770868954863308388583113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14777967759270978072443269 2770868954863308388583113)
                      ·
                        rfl

theorem cell23_5396248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5396248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396248 prefixEnd_5396248 := by exact prefixLift 5396248
  have htrace : WordTrace (prefixWord ++ tailWord_5396248) baseStart_5396248 baseEnd_5396248 := by
    simpa [prefixWord, tailWord_5396248, baseEnd_5396248] using wordTrace_append hprefix tailTrace_5396248
  have hstable : (prefixWord ++ tailWord_5396248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396248).length < 2 ^ (prefixWord ++ tailWord_5396248).sum := by decide
  have hdescent : baseEnd_5396248 < baseStart_5396248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396252 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5396252 : Nat := 118140960795 + 5396252 * 2 ^ 59
def prefixEnd_5396252 : Nat := 4983230072969 + 3 ^ 40 * 5396252 * 2
def baseEnd_5396252 : Nat := 2770871008785926372933095

theorem tailTrace_5396252 : CollatzResearch.WordTrace tailWord_5396252 prefixEnd_5396252 2770871008785926372933095 := by
  unfold tailWord_5396252
  simp only [CollatzResearch.WordTrace]
  refine ⟨98408739823154042656935505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131211653097538723542580673 98408739823154042656935505)
  ·
    refine ⟨73806554867365531992701629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98408739823154042656935505 73806554867365531992701629)
    ·
      refine ⟨27677458075262074497263111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73806554867365531992701629 27677458075262074497263111)
      ·
        refine ⟨41516187112893111745894667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27677458075262074497263111 41516187112893111745894667)
        ·
          refine ⟨62274280669339667618842001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41516187112893111745894667 62274280669339667618842001)
          ·
            refine ⟨46705710502004750714131501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62274280669339667618842001 46705710502004750714131501)
            ·
              refine ⟨17514641438251781517799313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46705710502004750714131501 17514641438251781517799313)
              ·
                refine ⟨13135981078688836138349485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17514641438251781517799313 13135981078688836138349485)
                ·
                  refine ⟨4925992904508313551881057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13135981078688836138349485 4925992904508313551881057)
                  ·
                    refine ⟨3694494678381235163910793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4925992904508313551881057 3694494678381235163910793)
                    ·
                      refine ⟨2770871008785926372933095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694494678381235163910793 2770871008785926372933095)
                      ·
                        rfl

theorem cell23_5396252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5396252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396252 prefixEnd_5396252 := by exact prefixLift 5396252
  have htrace : WordTrace (prefixWord ++ tailWord_5396252) baseStart_5396252 baseEnd_5396252 := by
    simpa [prefixWord, tailWord_5396252, baseEnd_5396252] using wordTrace_append hprefix tailTrace_5396252
  have hstable : (prefixWord ++ tailWord_5396252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396252).length < 2 ^ (prefixWord ++ tailWord_5396252).sum := by decide
  have hdescent : baseEnd_5396252 < baseStart_5396252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396255 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_5396255 : Nat := 118140960795 + 5396255 * 2 ^ 59
def prefixEnd_5396255 : Nat := 4983230072969 + 3 ^ 40 * 5396255 * 2
def baseEnd_5396255 : Nat := 2770872549227889861195581

theorem tailTrace_5396255 : CollatzResearch.WordTrace tailWord_5396255 prefixEnd_5396255 2770872549227889861195581 := by
  unfold tailWord_5396255
  simp only [CollatzResearch.WordTrace]
  refine ⟨196817589065297216826230219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131211726043531477884153479 196817589065297216826230219)
  ·
    refine ⟨295226383597945825239345329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196817589065297216826230219 295226383597945825239345329)
    ·
      refine ⟨221419787698459368929508997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295226383597945825239345329 221419787698459368929508997)
      ·
        refine ⟨41516210193461131674282937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221419787698459368929508997 41516210193461131674282937)
        ·
          refine ⟨31137157645095848755712203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41516210193461131674282937 31137157645095848755712203)
          ·
            refine ⟨46705736467643773133568305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31137157645095848755712203 46705736467643773133568305)
            ·
              refine ⟨35029302350732829850176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46705736467643773133568305 35029302350732829850176229)
              ·
                refine ⟨6567994190762405596908043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35029302350732829850176229 6567994190762405596908043)
                ·
                  refine ⟨9851991286143608395362065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6567994190762405596908043 9851991286143608395362065)
                  ·
                    refine ⟨7388993464607706296521549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9851991286143608395362065 7388993464607706296521549)
                    ·
                      refine ⟨2770872549227889861195581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7388993464607706296521549 2770872549227889861195581)
                      ·
                        rfl

theorem cell23_5396255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_5396255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396255 prefixEnd_5396255 := by exact prefixLift 5396255
  have htrace : WordTrace (prefixWord ++ tailWord_5396255) baseStart_5396255 baseEnd_5396255 := by
    simpa [prefixWord, tailWord_5396255, baseEnd_5396255] using wordTrace_append hprefix tailTrace_5396255
  have hstable : (prefixWord ++ tailWord_5396255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396255).length < 2 ^ (prefixWord ++ tailWord_5396255).sum := by decide
  have hdescent : baseEnd_5396255 < baseStart_5396255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396271 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 7]
def baseStart_5396271 : Nat := 118140960795 + 5396271 * 2 ^ 59
def prefixEnd_5396271 : Nat := 4983230072969 + 3 ^ 40 * 5396271 * 2
def baseEnd_5396271 : Nat := 923626921639453932865169

theorem tailTrace_5396271 : CollatzResearch.WordTrace tailWord_5396271 prefixEnd_5396271 923626921639453932865169 := by
  unfold tailWord_5396271
  simp only [CollatzResearch.WordTrace]
  refine ⟨196818172633239251558812667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131212115088826167705875111 196818172633239251558812667)
  ·
    refine ⟨295227258949858877338219001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196818172633239251558812667 295227258949858877338219001)
    ·
      refine ⟨221420444212394158003664251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295227258949858877338219001 221420444212394158003664251)
      ·
        refine ⟨332130666318591237005496377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221420444212394158003664251 332130666318591237005496377)
        ·
          refine ⟨249097999738943427754122283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332130666318591237005496377 249097999738943427754122283)
          ·
            refine ⟨373646999608415141631183425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249097999738943427754122283 373646999608415141631183425)
            ·
              refine ⟨280235249706311356223387569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373646999608415141631183425 280235249706311356223387569)
              ·
                refine ⟨210176437279733517167540677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280235249706311356223387569 210176437279733517167540677)
                ·
                  refine ⟨39408081989950034468913877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210176437279733517167540677 39408081989950034468913877)
                  ·
                    refine ⟨923626921639453932865169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39408081989950034468913877 923626921639453932865169)
                    ·
                      rfl

theorem cell23_5396271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_5396271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396271 prefixEnd_5396271 := by exact prefixLift 5396271
  have htrace : WordTrace (prefixWord ++ tailWord_5396271) baseStart_5396271 baseEnd_5396271 := by
    simpa [prefixWord, tailWord_5396271, baseEnd_5396271] using wordTrace_append hprefix tailTrace_5396271
  have hstable : (prefixWord ++ tailWord_5396271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396271).length < 2 ^ (prefixWord ++ tailWord_5396271).sum := by decide
  have hdescent : baseEnd_5396271 < baseStart_5396271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396286 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_5396286 : Nat := 118140960795 + 5396286 * 2 ^ 59
def prefixEnd_5396286 : Nat := 4983230072969 + 3 ^ 40 * 5396286 * 2
def baseEnd_5396286 : Nat := 2770888467128179239907939

theorem tailTrace_5396286 : CollatzResearch.WordTrace tailWord_5396286 prefixEnd_5396286 2770888467128179239907939 := by
  unfold tailWord_5396286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602339966023113640076089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131212479818789939413739141 24602339966023113640076089)
  ·
    refine ⟨18451754974517335230057067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24602339966023113640076089 18451754974517335230057067)
    ·
      refine ⟨27677632461776002845085601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18451754974517335230057067 27677632461776002845085601)
      ·
        refine ⟨20758224346332002133814201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27677632461776002845085601 20758224346332002133814201)
        ·
          refine ⟨15568668259749001600360651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20758224346332002133814201 15568668259749001600360651)
          ·
            refine ⟨23353002389623502400540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568668259749001600360651 23353002389623502400540977)
            ·
              refine ⟨17514751792217626800405733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23353002389623502400540977 17514751792217626800405733)
              ·
                refine ⟨3284015961040805025076075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17514751792217626800405733 3284015961040805025076075)
                ·
                  refine ⟨4926023941561207537614113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284015961040805025076075 4926023941561207537614113)
                  ·
                    refine ⟨3694517956170905653210585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4926023941561207537614113 3694517956170905653210585)
                    ·
                      refine ⟨2770888467128179239907939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694517956170905653210585 2770888467128179239907939)
                      ·
                        rfl

theorem cell23_5396286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_5396286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396286 prefixEnd_5396286 := by exact prefixLift 5396286
  have htrace : WordTrace (prefixWord ++ tailWord_5396286) baseStart_5396286 baseEnd_5396286 := by
    simpa [prefixWord, tailWord_5396286, baseEnd_5396286] using wordTrace_append hprefix tailTrace_5396286
  have hstable : (prefixWord ++ tailWord_5396286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396286).length < 2 ^ (prefixWord ++ tailWord_5396286).sum := by decide
  have hdescent : baseEnd_5396286 < baseStart_5396286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396295 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_5396295 : Nat := 118140960795 + 5396295 * 2 ^ 59
def prefixEnd_5396295 : Nat := 4983230072969 + 3 ^ 40 * 5396295 * 2
def baseEnd_5396295 : Nat := 2770893088454069704695397

theorem tailTrace_5396295 : CollatzResearch.WordTrace tailWord_5396295 prefixEnd_5396295 2770893088454069704695397 := by
  unfold tailWord_5396295
  simp only [CollatzResearch.WordTrace]
  refine ⟨196819047985152303657686339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131212698656768202438457559 196819047985152303657686339)
  ·
    refine ⟨295228571977728455486529509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196819047985152303657686339 295228571977728455486529509)
    ·
      refine ⟨55355357245824085403724283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295228571977728455486529509 55355357245824085403724283)
      ·
        refine ⟨83033035868736128105586425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55355357245824085403724283 83033035868736128105586425)
        ·
          refine ⟨62274776901552096079189819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83033035868736128105586425 62274776901552096079189819)
          ·
            refine ⟨93412165352328144118784729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62274776901552096079189819 93412165352328144118784729)
            ·
              refine ⟨70059124014246108089088547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93412165352328144118784729 70059124014246108089088547)
              ·
                refine ⟨105088686021369162133632821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70059124014246108089088547 105088686021369162133632821)
                ·
                  refine ⟨9852064314503358950028077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105088686021369162133632821 9852064314503358950028077)
                  ·
                    refine ⟨3694524117938759606260529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852064314503358950028077 3694524117938759606260529)
                    ·
                      refine ⟨2770893088454069704695397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694524117938759606260529 2770893088454069704695397)
                      ·
                        rfl

theorem cell23_5396295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_5396295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396295 prefixEnd_5396295 := by exact prefixLift 5396295
  have htrace : WordTrace (prefixWord ++ tailWord_5396295) baseStart_5396295 baseEnd_5396295 := by
    simpa [prefixWord, tailWord_5396295, baseEnd_5396295] using wordTrace_append hprefix tailTrace_5396295
  have hstable : (prefixWord ++ tailWord_5396295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396295).length < 2 ^ (prefixWord ++ tailWord_5396295).sum := by decide
  have hdescent : baseEnd_5396295 < baseStart_5396295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396325 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_5396325 : Nat := 118140960795 + 5396325 * 2 ^ 59
def prefixEnd_5396325 : Nat := 4983230072969 + 3 ^ 40 * 5396325 * 2
def baseEnd_5396325 : Nat := 2770908492873704587320259

theorem tailTrace_5396325 : CollatzResearch.WordTrace tailWord_5396325 prefixEnd_5396325 2770908492873704587320259 := by
  unfold tailWord_5396325
  simp only [CollatzResearch.WordTrace]
  refine ⟨196820142175043618781278429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131213428116695745854185619 196820142175043618781278429)
  ·
    refine ⟨73807553315641357042979411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196820142175043618781278429 73807553315641357042979411)
    ·
      refine ⟨110711329973462035564469117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73807553315641357042979411 110711329973462035564469117)
      ·
        refine ⟨41516748740048263336675919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110711329973462035564469117 41516748740048263336675919)
        ·
          refine ⟨62275123110072395005013879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41516748740048263336675919 62275123110072395005013879)
          ·
            refine ⟨93412684665108592507520819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62275123110072395005013879 93412684665108592507520819)
            ·
              refine ⟨140119026997662888761281229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93412684665108592507520819 140119026997662888761281229)
              ·
                refine ⟨52544635124123583285480461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140119026997662888761281229 52544635124123583285480461)
                ·
                  refine ⟨19704238171546343732055173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52544635124123583285480461 19704238171546343732055173)
                  ·
                    refine ⟨3694544657164939449760345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19704238171546343732055173 3694544657164939449760345)
                    ·
                      refine ⟨2770908492873704587320259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694544657164939449760345 2770908492873704587320259)
                      ·
                        rfl

theorem cell23_5396325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_5396325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396325 prefixEnd_5396325 := by exact prefixLift 5396325
  have htrace : WordTrace (prefixWord ++ tailWord_5396325) baseStart_5396325 baseEnd_5396325 := by
    simpa [prefixWord, tailWord_5396325, baseEnd_5396325] using wordTrace_append hprefix tailTrace_5396325
  have hstable : (prefixWord ++ tailWord_5396325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396325).length < 2 ^ (prefixWord ++ tailWord_5396325).sum := by decide
  have hdescent : baseEnd_5396325 < baseStart_5396325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396353 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5396353 : Nat := 118140960795 + 5396353 * 2 ^ 59
def prefixEnd_5396353 : Nat := 4983230072969 + 3 ^ 40 * 5396353 * 2
def baseEnd_5396353 : Nat := 2770922870332030477770131

theorem tailTrace_5396353 : CollatzResearch.WordTrace tailWord_5396353 prefixEnd_5396353 2770922870332030477770131 := by
  unfold tailWord_5396353
  simp only [CollatzResearch.WordTrace]
  refine ⟨196821163418942179563297713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131214108945961453042198475 196821163418942179563297713)
  ·
    refine ⟨147615872564206634672473285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196821163418942179563297713 147615872564206634672473285)
    ·
      refine ⟨27677976105788744001088741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147615872564206634672473285 27677976105788744001088741)
      ·
        refine ⟨5189620519835389500204139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27677976105788744001088741 5189620519835389500204139)
        ·
          refine ⟨7784430779753084250306209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189620519835389500204139 7784430779753084250306209)
          ·
            refine ⟨5838323084814813187729657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784430779753084250306209 5838323084814813187729657)
            ·
              refine ⟨4378742313611109890797243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838323084814813187729657 4378742313611109890797243)
              ·
                refine ⟨6568113470416664836195865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378742313611109890797243 6568113470416664836195865)
                ·
                  refine ⟨4926085102812498627146899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6568113470416664836195865 4926085102812498627146899)
                  ·
                    refine ⟨7389127654218747940720349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926085102812498627146899 7389127654218747940720349)
                    ·
                      refine ⟨2770922870332030477770131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389127654218747940720349 2770922870332030477770131)
                      ·
                        rfl

theorem cell23_5396353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5396353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396353 prefixEnd_5396353 := by exact prefixLift 5396353
  have htrace : WordTrace (prefixWord ++ tailWord_5396353) baseStart_5396353 baseEnd_5396353 := by
    simpa [prefixWord, tailWord_5396353, baseEnd_5396353] using wordTrace_append hprefix tailTrace_5396353
  have hstable : (prefixWord ++ tailWord_5396353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396353).length < 2 ^ (prefixWord ++ tailWord_5396353).sum := by decide
  have hdescent : baseEnd_5396353 < baseStart_5396353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396405 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_5396405 : Nat := 118140960795 + 5396405 * 2 ^ 59
def prefixEnd_5396405 : Nat := 4983230072969 + 3 ^ 40 * 5396405 * 2
def baseEnd_5396405 : Nat := 2770949571326064274319891

theorem tailTrace_5396405 : CollatzResearch.WordTrace tailWord_5396405 prefixEnd_5396405 2770949571326064274319891 := by
  unfold tailWord_5396405
  simp only [CollatzResearch.WordTrace]
  refine ⟨196823060014753792444190669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131215373343169194962793779 196823060014753792444190669)
  ·
    refine ⟨73808647505532672166571501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196823060014753792444190669 73808647505532672166571501)
    ·
      refine ⟨27678242814574752062464313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73808647505532672166571501 27678242814574752062464313)
      ·
        refine ⟨20758682110931064046848235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27678242814574752062464313 20758682110931064046848235)
        ·
          refine ⟨31138023166396596070272353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20758682110931064046848235 31138023166396596070272353)
          ·
            refine ⟨23353517374797447052704265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31138023166396596070272353 23353517374797447052704265)
            ·
              refine ⟨17515138031098085289528199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23353517374797447052704265 17515138031098085289528199)
              ·
                refine ⟨26272707046647127934292299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17515138031098085289528199 26272707046647127934292299)
                ·
                  refine ⟨39409060569970691901438449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26272707046647127934292299 39409060569970691901438449)
                  ·
                    refine ⟨29556795427478018926078837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39409060569970691901438449 29556795427478018926078837)
                    ·
                      refine ⟨2770949571326064274319891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29556795427478018926078837 2770949571326064274319891)
                      ·
                        rfl

theorem cell23_5396405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_5396405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396405 prefixEnd_5396405 := by exact prefixLift 5396405
  have htrace : WordTrace (prefixWord ++ tailWord_5396405) baseStart_5396405 baseEnd_5396405 := by
    simpa [prefixWord, tailWord_5396405, baseEnd_5396405] using wordTrace_append hprefix tailTrace_5396405
  have hstable : (prefixWord ++ tailWord_5396405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396405).length < 2 ^ (prefixWord ++ tailWord_5396405).sum := by decide
  have hdescent : baseEnd_5396405 < baseStart_5396405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396425 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_5396425 : Nat := 118140960795 + 5396425 * 2 ^ 59
def prefixEnd_5396425 : Nat := 4983230072969 + 3 ^ 40 * 5396425 * 2
def baseEnd_5396425 : Nat := 923653280313051398689933

theorem tailTrace_5396425 : CollatzResearch.WordTrace tailWord_5396425 prefixEnd_5396425 923653280313051398689933 := by
  unfold tailWord_5396425
  simp only [CollatzResearch.WordTrace]
  refine ⟨196823789474681335859918729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131215859649787557239945819 196823789474681335859918729)
  ·
    refine ⟨147617842106011001894939047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196823789474681335859918729 147617842106011001894939047)
    ·
      refine ⟨221426763159016502842408571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147617842106011001894939047 221426763159016502842408571)
      ·
        refine ⟨332140144738524754263612857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221426763159016502842408571 332140144738524754263612857)
        ·
          refine ⟨249105108553893565697709643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332140144738524754263612857 249105108553893565697709643)
          ·
            refine ⟨373657662830840348546564465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249105108553893565697709643 373657662830840348546564465)
            ·
              refine ⟨280243247123130261409923349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373657662830840348546564465 280243247123130261409923349)
              ·
                refine ⟨13136402208896731003590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280243247123130261409923349 13136402208896731003590157)
                ·
                  refine ⟨4926150828336274126346309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13136402208896731003590157 4926150828336274126346309)
                  ·
                    refine ⟨923653280313051398689933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4926150828336274126346309 923653280313051398689933)
                    ·
                      rfl

theorem cell23_5396425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_5396425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396425 prefixEnd_5396425 := by exact prefixLift 5396425
  have htrace : WordTrace (prefixWord ++ tailWord_5396425) baseStart_5396425 baseEnd_5396425 := by
    simpa [prefixWord, tailWord_5396425, baseEnd_5396425] using wordTrace_append hprefix tailTrace_5396425
  have hstable : (prefixWord ++ tailWord_5396425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396425).length < 2 ^ (prefixWord ++ tailWord_5396425).sum := by decide
  have hdescent : baseEnd_5396425 < baseStart_5396425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396492 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_5396492 : Nat := 118140960795 + 5396492 * 2 ^ 59
def prefixEnd_5396492 : Nat := 4983230072969 + 3 ^ 40 * 5396492 * 2
def baseEnd_5396492 : Nat := 2770994244143005433931991

theorem tailTrace_5396492 : CollatzResearch.WordTrace tailWord_5396492 prefixEnd_5396492 2770994244143005433931991 := by
  unfold tailWord_5396492
  simp only [CollatzResearch.WordTrace]
  refine ⟨98413116582719303151303865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131217488776959070868405153 98413116582719303151303865)
  ·
    refine ⟨73809837437039477363477899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98413116582719303151303865 73809837437039477363477899)
    ·
      refine ⟨110714756155559216045216849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73809837437039477363477899 110714756155559216045216849)
      ·
        refine ⟨83036067116669412033912637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110714756155559216045216849 83036067116669412033912637)
        ·
          refine ⟨31138525168751029512717239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83036067116669412033912637 31138525168751029512717239)
          ·
            refine ⟨46707787753126544269075859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31138525168751029512717239 46707787753126544269075859)
            ·
              refine ⟨70061681629689816403613789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46707787753126544269075859 70061681629689816403613789)
              ·
                refine ⟨26273130611133681151355171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70061681629689816403613789 26273130611133681151355171)
                ·
                  refine ⟨39409695916700521727032757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26273130611133681151355171 39409695916700521727032757)
                  ·
                    refine ⟨3694658992190673911909321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39409695916700521727032757 3694658992190673911909321)
                    ·
                      refine ⟨2770994244143005433931991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694658992190673911909321 2770994244143005433931991)
                      ·
                        rfl

theorem cell23_5396492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_5396492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396492 prefixEnd_5396492 := by exact prefixLift 5396492
  have htrace : WordTrace (prefixWord ++ tailWord_5396492) baseStart_5396492 baseEnd_5396492 := by
    simpa [prefixWord, tailWord_5396492, baseEnd_5396492] using wordTrace_append hprefix tailTrace_5396492
  have hstable : (prefixWord ++ tailWord_5396492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396492).length < 2 ^ (prefixWord ++ tailWord_5396492).sum := by decide
  have hdescent : baseEnd_5396492 < baseStart_5396492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396505 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_5396505 : Nat := 118140960795 + 5396505 * 2 ^ 59
def prefixEnd_5396505 : Nat := 4983230072969 + 3 ^ 40 * 5396505 * 2
def baseEnd_5396505 : Nat := 2771000919391513883069431

theorem tailTrace_5396505 : CollatzResearch.WordTrace tailWord_5396505 prefixEnd_5396505 2771000919391513883069431 := by
  unfold tailWord_5396505
  simp only [CollatzResearch.WordTrace]
  refine ⟨196826707314391509522830969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131217804876261006348553979 196826707314391509522830969)
  ·
    refine ⟨147620030485793632142123227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196826707314391509522830969 147620030485793632142123227)
    ·
      refine ⟨221430045728690448213184841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147620030485793632142123227 221430045728690448213184841)
      ·
        refine ⟨166072534296517836159888631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221430045728690448213184841 166072534296517836159888631)
        ·
          refine ⟨249108801444776754239832947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166072534296517836159888631 249108801444776754239832947)
          ·
            refine ⟨373663202167165131359749421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249108801444776754239832947 373663202167165131359749421)
            ·
              refine ⟨140123700812686924259906033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373663202167165131359749421 140123700812686924259906033)
              ·
                refine ⟨105092775609515193194929525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140123700812686924259906033 105092775609515193194929525)
                ·
                  refine ⟨9852447713392049362024643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105092775609515193194929525 9852447713392049362024643)
                  ·
                    refine ⟨14778671570088074043036965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9852447713392049362024643 14778671570088074043036965)
                    ·
                      refine ⟨2771000919391513883069431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14778671570088074043036965 2771000919391513883069431)
                      ·
                        rfl

theorem cell23_5396505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_5396505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396505 prefixEnd_5396505 := by exact prefixLift 5396505
  have htrace : WordTrace (prefixWord ++ tailWord_5396505) baseStart_5396505 baseEnd_5396505 := by
    simpa [prefixWord, tailWord_5396505, baseEnd_5396505] using wordTrace_append hprefix tailTrace_5396505
  have hstable : (prefixWord ++ tailWord_5396505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396505).length < 2 ^ (prefixWord ++ tailWord_5396505).sum := by decide
  have hdescent : baseEnd_5396505 < baseStart_5396505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396509 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_5396509 : Nat := 118140960795 + 5396509 * 2 ^ 59
def prefixEnd_5396509 : Nat := 4983230072969 + 3 ^ 40 * 5396509 * 2
def baseEnd_5396509 : Nat := 2771002973314131867419413

theorem tailTrace_5396509 : CollatzResearch.WordTrace tailWord_5396509 prefixEnd_5396509 2771002973314131867419413 := by
  unfold tailWord_5396509
  simp only [CollatzResearch.WordTrace]
  refine ⟨196826853206377018205976581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131217902137584678803984387 196826853206377018205976581)
  ·
    refine ⟨36905034976195690913620609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196826853206377018205976581 36905034976195690913620609)
    ·
      refine ⟨27678776232146768185215457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36905034976195690913620609 27678776232146768185215457)
      ·
        refine ⟨20759082174110076138911593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27678776232146768185215457 20759082174110076138911593)
        ·
          refine ⟨15569311630582557104183695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20759082174110076138911593 15569311630582557104183695)
          ·
            refine ⟨23353967445873835656275543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569311630582557104183695 23353967445873835656275543)
            ·
              refine ⟨35030951168810753484413315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23353967445873835656275543 35030951168810753484413315)
              ·
                refine ⟨52546426753216130226619973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35030951168810753484413315 52546426753216130226619973)
                ·
                  refine ⟨9852455016228024417491245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52546426753216130226619973 9852455016228024417491245)
                  ·
                    refine ⟨3694670631085509156559217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852455016228024417491245 3694670631085509156559217)
                    ·
                      refine ⟨2771002973314131867419413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694670631085509156559217 2771002973314131867419413)
                      ·
                        rfl

theorem cell23_5396509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_5396509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396509 prefixEnd_5396509 := by exact prefixLift 5396509
  have htrace : WordTrace (prefixWord ++ tailWord_5396509) baseStart_5396509 baseEnd_5396509 := by
    simpa [prefixWord, tailWord_5396509, baseEnd_5396509] using wordTrace_append hprefix tailTrace_5396509
  have hstable : (prefixWord ++ tailWord_5396509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396509).length < 2 ^ (prefixWord ++ tailWord_5396509).sum := by decide
  have hdescent : baseEnd_5396509 < baseStart_5396509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396535 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_5396535 : Nat := 118140960795 + 5396535 * 2 ^ 59
def prefixEnd_5396535 : Nat := 4983230072969 + 3 ^ 40 * 5396535 * 2
def baseEnd_5396535 : Nat := 2771016323811148765694293

theorem tailTrace_5396535 : CollatzResearch.WordTrace tailWord_5396535 prefixEnd_5396535 2771016323811148765694293 := by
  unfold tailWord_5396535
  simp only [CollatzResearch.WordTrace]
  refine ⟨196827801504282824646423059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131218534336188549764282039 196827801504282824646423059)
  ·
    refine ⟨295241702256424236969634589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196827801504282824646423059 295241702256424236969634589)
    ·
      refine ⟨110715638346159088863612971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295241702256424236969634589 110715638346159088863612971)
      ·
        refine ⟨166073457519238633295419457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110715638346159088863612971 166073457519238633295419457)
        ·
          refine ⟨124555093139428974971564593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166073457519238633295419457 124555093139428974971564593)
          ·
            refine ⟨93416319854571731228673445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124555093139428974971564593 93416319854571731228673445)
            ·
              refine ⟨17515559972732199605376271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93416319854571731228673445 17515559972732199605376271)
              ·
                refine ⟨26273339959098299408064407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17515559972732199605376271 26273339959098299408064407)
                ·
                  refine ⟨39410009938647449112096611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26273339959098299408064407 39410009938647449112096611)
                  ·
                    refine ⟨59115014907971173668144917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39410009938647449112096611 59115014907971173668144917)
                    ·
                      refine ⟨2771016323811148765694293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59115014907971173668144917 2771016323811148765694293)
                      ·
                        rfl

theorem cell23_5396535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_5396535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396535 prefixEnd_5396535 := by exact prefixLift 5396535
  have htrace : WordTrace (prefixWord ++ tailWord_5396535) baseStart_5396535 baseEnd_5396535 := by
    simpa [prefixWord, tailWord_5396535, baseEnd_5396535] using wordTrace_append hprefix tailTrace_5396535
  have hstable : (prefixWord ++ tailWord_5396535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396535).length < 2 ^ (prefixWord ++ tailWord_5396535).sum := by decide
  have hdescent : baseEnd_5396535 < baseStart_5396535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396536 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_5396536 : Nat := 118140960795 + 5396536 * 2 ^ 59
def prefixEnd_5396536 : Nat := 4983230072969 + 3 ^ 40 * 5396536 * 2
def baseEnd_5396536 : Nat := 923672279097267753927263

theorem tailTrace_5396536 : CollatzResearch.WordTrace tailWord_5396536 prefixEnd_5396536 923672279097267753927263 := by
  unfold tailWord_5396536
  simp only [CollatzResearch.WordTrace]
  refine ⟨98413918988639600908604731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131218558651519467878139641 98413918988639600908604731)
  ·
    refine ⟨147620878482959401362907097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98413918988639600908604731 147620878482959401362907097)
    ·
      refine ⟨110715658862219551022180323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147620878482959401362907097 110715658862219551022180323)
      ·
        refine ⟨166073488293329326533270485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110715658862219551022180323 166073488293329326533270485)
        ·
          refine ⟨3892347381874906090623527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166073488293329326533270485 3892347381874906090623527)
          ·
            refine ⟨5838521072812359135935291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892347381874906090623527 5838521072812359135935291)
            ·
              refine ⟨8757781609218538703902937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838521072812359135935291 8757781609218538703902937)
              ·
                refine ⟨6568336206913904027927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757781609218538703902937 6568336206913904027927203)
                ·
                  refine ⟨9852504310370856041890805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568336206913904027927203 9852504310370856041890805)
                  ·
                    refine ⟨923672279097267753927263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9852504310370856041890805 923672279097267753927263)
                    ·
                      rfl

theorem cell23_5396536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_5396536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396536 prefixEnd_5396536 := by exact prefixLift 5396536
  have htrace : WordTrace (prefixWord ++ tailWord_5396536) baseStart_5396536 baseEnd_5396536 := by
    simpa [prefixWord, tailWord_5396536, baseEnd_5396536] using wordTrace_append hprefix tailTrace_5396536
  have hstable : (prefixWord ++ tailWord_5396536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396536).length < 2 ^ (prefixWord ++ tailWord_5396536).sum := by decide
  have hdescent : baseEnd_5396536 < baseStart_5396536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396562 : List Nat := [3, 2, 2, 1, 5, 10]
def baseStart_5396562 : Nat := 118140960795 + 5396562 * 2 ^ 59
def prefixEnd_5396562 : Nat := 4983230072969 + 3 ^ 40 * 5396562 * 2
def baseEnd_5396562 : Nat := 11403416410653580905583

theorem tailTrace_5396562 : CollatzResearch.WordTrace tailWord_5396562 prefixEnd_5396562 11403416410653580905583 := by
  unfold tailWord_5396562
  simp only [CollatzResearch.WordTrace]
  refine ⟨49207196568796252064413985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131219190850123338838437293 49207196568796252064413985)
  ·
    refine ⟨36905397426597189048310489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49207196568796252064413985 36905397426597189048310489)
    ·
      refine ⟨27679048069947891786232867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36905397426597189048310489 27679048069947891786232867)
      ·
        refine ⟨41518572104921837679349301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27679048069947891786232867 41518572104921837679349301)
        ·
          refine ⟨3892366134836422282438997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41518572104921837679349301 3892366134836422282438997)
          ·
            refine ⟨11403416410653580905583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3892366134836422282438997 11403416410653580905583)
            ·
              rfl

theorem cell23_5396562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 10].length) (baseStart_5396562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396562 prefixEnd_5396562 := by exact prefixLift 5396562
  have htrace : WordTrace (prefixWord ++ tailWord_5396562) baseStart_5396562 baseEnd_5396562 := by
    simpa [prefixWord, tailWord_5396562, baseEnd_5396562] using wordTrace_append hprefix tailTrace_5396562
  have hstable : (prefixWord ++ tailWord_5396562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396562).length < 2 ^ (prefixWord ++ tailWord_5396562).sum := by decide
  have hdescent : baseEnd_5396562 < baseStart_5396562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396589 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5396589 : Nat := 118140960795 + 5396589 * 2 ^ 59
def prefixEnd_5396589 : Nat := 4983230072969 + 3 ^ 40 * 5396589 * 2
def baseEnd_5396589 : Nat := 2771044051766491554419045

theorem tailTrace_5396589 : CollatzResearch.WordTrace tailWord_5396589 prefixEnd_5396589 2771044051766491554419045 := by
  unfold tailWord_5396589
  simp only [CollatzResearch.WordTrace]
  refine ⟨196829771046087191868888821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131219847364058127912592547 196829771046087191868888821)
  ·
    refine ⟨18452791035570674237708327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196829771046087191868888821 18452791035570674237708327)
    ·
      refine ⟨27679186553356011356562491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18452791035570674237708327 27679186553356011356562491)
      ·
        refine ⟨41518779830034017034843737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27679186553356011356562491 41518779830034017034843737)
        ·
          refine ⟨31139084872525512776132803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41518779830034017034843737 31139084872525512776132803)
          ·
            refine ⟨46708627308788269164199205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31139084872525512776132803 46708627308788269164199205)
            ·
              refine ⟨8757867620397800468287351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46708627308788269164199205 8757867620397800468287351)
              ·
                refine ⟨13136801430596700702431027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757867620397800468287351 13136801430596700702431027)
                ·
                  refine ⟨19705202145895051053646541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13136801430596700702431027 19705202145895051053646541)
                  ·
                    refine ⟨7389450804710644145117453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19705202145895051053646541 7389450804710644145117453)
                    ·
                      refine ⟨2771044051766491554419045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389450804710644145117453 2771044051766491554419045)
                      ·
                        rfl

theorem cell23_5396589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5396589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396589 prefixEnd_5396589 := by exact prefixLift 5396589
  have htrace : WordTrace (prefixWord ++ tailWord_5396589) baseStart_5396589 baseEnd_5396589 := by
    simpa [prefixWord, tailWord_5396589, baseEnd_5396589] using wordTrace_append hprefix tailTrace_5396589
  have hstable : (prefixWord ++ tailWord_5396589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396589).length < 2 ^ (prefixWord ++ tailWord_5396589).sum := by decide
  have hdescent : baseEnd_5396589 < baseStart_5396589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396599 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_5396599 : Nat := 118140960795 + 5396599 * 2 ^ 59
def prefixEnd_5396599 : Nat := 4983230072969 + 3 ^ 40 * 5396599 * 2
def baseEnd_5396599 : Nat := 2771049186573036515293999

theorem tailTrace_5396599 : CollatzResearch.WordTrace tailWord_5396599 prefixEnd_5396599 2771049186573036515293999 := by
  unfold tailWord_5396599
  simp only [CollatzResearch.WordTrace]
  refine ⟨196830135776050963576752851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131220090517367309051168567 196830135776050963576752851)
  ·
    refine ⟨295245203664076445365129277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196830135776050963576752851 295245203664076445365129277)
    ·
      refine ⟨110716951374028667011923479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295245203664076445365129277 110716951374028667011923479)
      ·
        refine ⟨166075427061043000517885219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110716951374028667011923479 166075427061043000517885219)
        ·
          refine ⟨249113140591564500776827829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166075427061043000517885219 249113140591564500776827829)
          ·
            refine ⟨23354356930459171947827609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249113140591564500776827829 23354356930459171947827609)
            ·
              refine ⟨17515767697844378960870707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23354356930459171947827609 17515767697844378960870707)
              ·
                refine ⟨26273651546766568441306061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17515767697844378960870707 26273651546766568441306061)
                ·
                  refine ⟨9852619330037463165489773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26273651546766568441306061 9852619330037463165489773)
                  ·
                    refine ⟨3694732248764048687058665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852619330037463165489773 3694732248764048687058665)
                    ·
                      refine ⟨2771049186573036515293999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694732248764048687058665 2771049186573036515293999)
                      ·
                        rfl

theorem cell23_5396599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_5396599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396599 prefixEnd_5396599 := by exact prefixLift 5396599
  have htrace : WordTrace (prefixWord ++ tailWord_5396599) baseStart_5396599 baseEnd_5396599 := by
    simpa [prefixWord, tailWord_5396599, baseEnd_5396599] using wordTrace_append hprefix tailTrace_5396599
  have hstable : (prefixWord ++ tailWord_5396599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396599).length < 2 ^ (prefixWord ++ tailWord_5396599).sum := by decide
  have hdescent : baseEnd_5396599 < baseStart_5396599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396650 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5396650 : Nat := 118140960795 + 5396650 * 2 ^ 59
def prefixEnd_5396650 : Nat := 4983230072969 + 3 ^ 40 * 5396650 * 2
def baseEnd_5396650 : Nat := 2771075374086415815756265

theorem tailTrace_5396650 : CollatzResearch.WordTrace tailWord_5396650 prefixEnd_5396650 2771075374086415815756265 := by
  unfold tailWord_5396650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49207998974716549821714851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131221330599244132857906269 49207998974716549821714851)
  ·
    refine ⟨73811998462074824732572277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49207998974716549821714851 73811998462074824732572277)
    ·
      refine ⟨6919874855819514818678651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73811998462074824732572277 6919874855819514818678651)
      ·
        refine ⟨10379812283729272228017977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919874855819514818678651 10379812283729272228017977)
        ·
          refine ⟨7784859212796954171013483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10379812283729272228017977 7784859212796954171013483)
          ·
            refine ⟨11677288819195431256520225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784859212796954171013483 11677288819195431256520225)
            ·
              refine ⟨8757966614396573442390169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677288819195431256520225 8757966614396573442390169)
              ·
                refine ⟨6568474960797430081792627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757966614396573442390169 6568474960797430081792627)
                ·
                  refine ⟨9852712441196145122688941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568474960797430081792627 9852712441196145122688941)
                  ·
                    refine ⟨3694767165448554421008353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852712441196145122688941 3694767165448554421008353)
                    ·
                      refine ⟨2771075374086415815756265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694767165448554421008353 2771075374086415815756265)
                      ·
                        rfl

theorem cell23_5396650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5396650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396650 prefixEnd_5396650 := by exact prefixLift 5396650
  have htrace : WordTrace (prefixWord ++ tailWord_5396650) baseStart_5396650 baseEnd_5396650 := by
    simpa [prefixWord, tailWord_5396650, baseEnd_5396650] using wordTrace_append hprefix tailTrace_5396650
  have hstable : (prefixWord ++ tailWord_5396650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396650).length < 2 ^ (prefixWord ++ tailWord_5396650).sum := by decide
  have hdescent : baseEnd_5396650 < baseStart_5396650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396719 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_5396719 : Nat := 118140960795 + 5396719 * 2 ^ 59
def prefixEnd_5396719 : Nat := 4983230072969 + 3 ^ 40 * 5396719 * 2
def baseEnd_5396719 : Nat := 2771110804251576045793447

theorem tailTrace_5396719 : CollatzResearch.WordTrace tailWord_5396719 prefixEnd_5396719 2771110804251576045793447 := by
  unfold tailWord_5396719
  simp only [CollatzResearch.WordTrace]
  refine ⟨196834512535616224071121211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131223008357077482714080807 196834512535616224071121211)
  ·
    refine ⟨295251768803424336106681817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196834512535616224071121211 295251768803424336106681817)
    ·
      refine ⟨221438826602568252080011363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295251768803424336106681817 221438826602568252080011363)
      ·
        refine ⟨332158239903852378120017045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221438826602568252080011363 332158239903852378120017045)
        ·
          refine ⟨15569917495493080224375799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 332158239903852378120017045 15569917495493080224375799)
          ·
            refine ⟨23354876243239620336563699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15569917495493080224375799 23354876243239620336563699)
            ·
              refine ⟨35032314364859430504845549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23354876243239620336563699 35032314364859430504845549)
              ·
                refine ⟨13137117886822286439317081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35032314364859430504845549 13137117886822286439317081)
                ·
                  refine ⟨9852838415116714829487811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13137117886822286439317081 9852838415116714829487811)
                  ·
                    refine ⟨14779257622675072244231717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9852838415116714829487811 14779257622675072244231717)
                    ·
                      refine ⟨2771110804251576045793447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14779257622675072244231717 2771110804251576045793447)
                      ·
                        rfl

theorem cell23_5396719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_5396719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396719 prefixEnd_5396719 := by exact prefixLift 5396719
  have htrace : WordTrace (prefixWord ++ tailWord_5396719) baseStart_5396719 baseEnd_5396719 := by
    simpa [prefixWord, tailWord_5396719, baseEnd_5396719] using wordTrace_append hprefix tailTrace_5396719
  have hstable : (prefixWord ++ tailWord_5396719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396719).length < 2 ^ (prefixWord ++ tailWord_5396719).sum := by decide
  have hdescent : baseEnd_5396719 < baseStart_5396719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396739 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3]
def baseStart_5396739 : Nat := 118140960795 + 5396739 * 2 ^ 59
def prefixEnd_5396739 : Nat := 4983230072969 + 3 ^ 40 * 5396739 * 2
def baseEnd_5396739 : Nat := 2771121073864665967543355

theorem tailTrace_5396739 : CollatzResearch.WordTrace tailWord_5396739 prefixEnd_5396739 2771121073864665967543355 := by
  unfold tailWord_5396739
  simp only [CollatzResearch.WordTrace]
  refine ⟨196835241995543767486849271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131223494663695844991232847 196835241995543767486849271)
  ·
    refine ⟨295252862993315651230273907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196835241995543767486849271 295252862993315651230273907)
    ·
      refine ⟨442879294489973476845410861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295252862993315651230273907 442879294489973476845410861)
      ·
        refine ⟨166079735433740053817029073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442879294489973476845410861 166079735433740053817029073)
        ·
          refine ⟨124559801575305040362771805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166079735433740053817029073 124559801575305040362771805)
          ·
            refine ⟨46709925590739390136039427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124559801575305040362771805 46709925590739390136039427)
            ·
              refine ⟨70064888386109085204059141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46709925590739390136039427 70064888386109085204059141)
              ·
                refine ⟨13137166572395453475761089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70064888386109085204059141 13137166572395453475761089)
                ·
                  refine ⟨9852874929296590106820817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13137166572395453475761089 9852874929296590106820817)
                  ·
                    refine ⟨7389656196972442580115613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9852874929296590106820817 7389656196972442580115613)
                    ·
                      refine ⟨2771121073864665967543355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389656196972442580115613 2771121073864665967543355)
                      ·
                        rfl

theorem cell23_5396739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_5396739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396739 prefixEnd_5396739 := by exact prefixLift 5396739
  have htrace : WordTrace (prefixWord ++ tailWord_5396739) baseStart_5396739 baseEnd_5396739 := by
    simpa [prefixWord, tailWord_5396739, baseEnd_5396739] using wordTrace_append hprefix tailTrace_5396739
  have hstable : (prefixWord ++ tailWord_5396739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396739).length < 2 ^ (prefixWord ++ tailWord_5396739).sum := by decide
  have hdescent : baseEnd_5396739 < baseStart_5396739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396759 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 6]
def baseStart_5396759 : Nat := 118140960795 + 5396759 * 2 ^ 59
def prefixEnd_5396759 : Nat := 4983230072969 + 3 ^ 40 * 5396759 * 2
def baseEnd_5396759 : Nat := 307903482608639543254807

theorem tailTrace_5396759 : CollatzResearch.WordTrace tailWord_5396759 prefixEnd_5396759 307903482608639543254807 := by
  unfold tailWord_5396759
  simp only [CollatzResearch.WordTrace]
  refine ⟨196835971455471310902577331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131223980970314207268384887 196835971455471310902577331)
  ·
    refine ⟨295253957183206966353865997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196835971455471310902577331 295253957183206966353865997)
    ·
      refine ⟨110720233943702612382699749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295253957183206966353865997 110720233943702612382699749)
      ·
        refine ⟨20760043864444239821756203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110720233943702612382699749 20760043864444239821756203)
        ·
          refine ⟨31140065796666359732634305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20760043864444239821756203 31140065796666359732634305)
          ·
            refine ⟨23355049347499769799475729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31140065796666359732634305 23355049347499769799475729)
            ·
              refine ⟨17516287010624827349606797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23355049347499769799475729 17516287010624827349606797)
              ·
                refine ⟨6568607628984310256102549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17516287010624827349606797 6568607628984310256102549)
                ·
                  refine ⟨307903482608639543254807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6568607628984310256102549 307903482608639543254807)
                  ·
                    rfl

theorem cell23_5396759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 6].length) (baseStart_5396759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396759 prefixEnd_5396759 := by exact prefixLift 5396759
  have htrace : WordTrace (prefixWord ++ tailWord_5396759) baseStart_5396759 baseEnd_5396759 := by
    simpa [prefixWord, tailWord_5396759, baseEnd_5396759] using wordTrace_append hprefix tailTrace_5396759
  have hstable : (prefixWord ++ tailWord_5396759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396759).length < 2 ^ (prefixWord ++ tailWord_5396759).sum := by decide
  have hdescent : baseEnd_5396759 < baseStart_5396759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396773 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_5396773 : Nat := 118140960795 + 5396773 * 2 ^ 59
def prefixEnd_5396773 : Nat := 4983230072969 + 3 ^ 40 * 5396773 * 2
def baseEnd_5396773 : Nat := 2771138532206918834518199

theorem tailTrace_5396773 : CollatzResearch.WordTrace tailWord_5396773 prefixEnd_5396773 2771138532206918834518199 := by
  unfold tailWord_5396773
  simp only [CollatzResearch.WordTrace]
  refine ⟨196836482077420591293586973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131224321384947060862391315 196836482077420591293586973)
  ·
    refine ⟨73813680779032721735095115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196836482077420591293586973 73813680779032721735095115)
    ·
      refine ⟨110720521168549082602642673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73813680779032721735095115 110720521168549082602642673)
      ·
        refine ⟨83040390876411811951982005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110720521168549082602642673 83040390876411811951982005)
        ·
          refine ⟨7785036644663607370498313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83040390876411811951982005 7785036644663607370498313)
          ·
            refine ⟨5838777483497705527873735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7785036644663607370498313 5838777483497705527873735)
            ·
              refine ⟨8758166225246558291810603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838777483497705527873735 8758166225246558291810603)
              ·
                refine ⟨13137249337869837437715905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758166225246558291810603 13137249337869837437715905)
                ·
                  refine ⟨9852937003402378078286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13137249337869837437715905 9852937003402378078286929)
                  ·
                    refine ⟨7389702752551783558715197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9852937003402378078286929 7389702752551783558715197)
                    ·
                      refine ⟨2771138532206918834518199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389702752551783558715197 2771138532206918834518199)
                      ·
                        rfl

theorem cell23_5396773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_5396773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396773 prefixEnd_5396773 := by exact prefixLift 5396773
  have htrace : WordTrace (prefixWord ++ tailWord_5396773) baseStart_5396773 baseEnd_5396773 := by
    simpa [prefixWord, tailWord_5396773, baseEnd_5396773] using wordTrace_append hprefix tailTrace_5396773
  have hstable : (prefixWord ++ tailWord_5396773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396773).length < 2 ^ (prefixWord ++ tailWord_5396773).sum := by decide
  have hdescent : baseEnd_5396773 < baseStart_5396773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396796 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_5396796 : Nat := 118140960795 + 5396796 * 2 ^ 59
def prefixEnd_5396796 : Nat := 4983230072969 + 3 ^ 40 * 5396796 * 2
def baseEnd_5396796 : Nat := 2771150342261972244530593

theorem tailTrace_5396796 : CollatzResearch.WordTrace tailWord_5396796 prefixEnd_5396796 2771150342261972244530593 := by
  unfold tailWord_5396796
  simp only [CollatzResearch.WordTrace]
  refine ⟨98418660478168633110837121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131224880637558177481116161 98418660478168633110837121)
  ·
    refine ⟨73813995358626474833127841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98418660478168633110837121 73813995358626474833127841)
    ·
      refine ⟨55360496518969856124845881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73813995358626474833127841 55360496518969856124845881)
      ·
        refine ⟨41520372389227392093634411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55360496518969856124845881 41520372389227392093634411)
        ·
          refine ⟨62280558583841088140451617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41520372389227392093634411 62280558583841088140451617)
          ·
            refine ⟨46710418937880816105338713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62280558583841088140451617 46710418937880816105338713)
            ·
              refine ⟨35032814203410612079004035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46710418937880816105338713 35032814203410612079004035)
              ·
                refine ⟨52549221305115918118506053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35032814203410612079004035 52549221305115918118506053)
                ·
                  refine ⟨9852978994709234647219885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52549221305115918118506053 9852978994709234647219885)
                  ·
                    refine ⟨3694867123015962992707457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852978994709234647219885 3694867123015962992707457)
                    ·
                      refine ⟨2771150342261972244530593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694867123015962992707457 2771150342261972244530593)
                      ·
                        rfl

theorem cell23_5396796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_5396796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396796 prefixEnd_5396796 := by exact prefixLift 5396796
  have htrace : WordTrace (prefixWord ++ tailWord_5396796) baseStart_5396796 baseEnd_5396796 := by
    simpa [prefixWord, tailWord_5396796, baseEnd_5396796] using wordTrace_append hprefix tailTrace_5396796
  have hstable : (prefixWord ++ tailWord_5396796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396796).length < 2 ^ (prefixWord ++ tailWord_5396796).sum := by decide
  have hdescent : baseEnd_5396796 < baseStart_5396796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396803 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 1, 1, 3]
def baseStart_5396803 : Nat := 118140960795 + 5396803 * 2 ^ 59
def prefixEnd_5396803 : Nat := 4983230072969 + 3 ^ 40 * 5396803 * 2
def baseEnd_5396803 : Nat := 2771153936626553717143061

theorem tailTrace_5396803 : CollatzResearch.WordTrace tailWord_5396803 prefixEnd_5396803 2771153936626553717143061 := by
  unfold tailWord_5396803
  simp only [CollatzResearch.WordTrace]
  refine ⟨196837576267311906417179063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131225050844874604278119375 196837576267311906417179063)
  ·
    refine ⟨295256364400967859625768595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196837576267311906417179063 295256364400967859625768595)
    ·
      refine ⟨442884546601451789438652893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295256364400967859625768595 442884546601451789438652893)
      ·
        refine ⟨166081704975544421039494835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442884546601451789438652893 166081704975544421039494835)
        ·
          refine ⟨249122557463316631559242253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166081704975544421039494835 249122557463316631559242253)
          ·
            refine ⟨93420959048743736834715845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249122557463316631559242253 93420959048743736834715845)
            ·
              refine ⟨17516429821639450656509221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93420959048743736834715845 17516429821639450656509221)
              ·
                refine ⟨3284330591557396998095479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17516429821639450656509221 3284330591557396998095479)
                ·
                  refine ⟨4926495887336095497143219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284330591557396998095479 4926495887336095497143219)
                  ·
                    refine ⟨7389743831004143245714829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926495887336095497143219 7389743831004143245714829)
                    ·
                      refine ⟨2771153936626553717143061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389743831004143245714829 2771153936626553717143061)
                      ·
                        rfl

theorem cell23_5396803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_5396803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396803 prefixEnd_5396803 := by exact prefixLift 5396803
  have htrace : WordTrace (prefixWord ++ tailWord_5396803) baseStart_5396803 baseEnd_5396803 := by
    simpa [prefixWord, tailWord_5396803, baseEnd_5396803] using wordTrace_append hprefix tailTrace_5396803
  have hstable : (prefixWord ++ tailWord_5396803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396803).length < 2 ^ (prefixWord ++ tailWord_5396803).sum := by decide
  have hdescent : baseEnd_5396803 < baseStart_5396803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396854 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5396854 : Nat := 118140960795 + 5396854 * 2 ^ 59
def prefixEnd_5396854 : Nat := 4983230072969 + 3 ^ 40 * 5396854 * 2
def baseEnd_5396854 : Nat := 2771180124139933017605327

theorem tailTrace_5396854 : CollatzResearch.WordTrace tailWord_5396854 prefixEnd_5396854 2771180124139933017605327 := by
  unfold tailWord_5396854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302464774382946382955351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131226290926751428084857077 12302464774382946382955351)
  ·
    refine ⟨18453697161574419574433027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12302464774382946382955351 18453697161574419574433027)
    ·
      refine ⟨27680545742361629361649541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18453697161574419574433027 27680545742361629361649541)
      ·
        refine ⟨5190102326692805505309289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27680545742361629361649541 5190102326692805505309289)
        ·
          refine ⟨3892576745019604128981967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190102326692805505309289 3892576745019604128981967)
          ·
            refine ⟨5838865117529406193472951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892576745019604128981967 5838865117529406193472951)
            ·
              refine ⟨8758297676294109290209427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838865117529406193472951 8758297676294109290209427)
              ·
                refine ⟨13137446514441163935314141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758297676294109290209427 13137446514441163935314141)
                ·
                  refine ⟨4926542442915436475742803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13137446514441163935314141 4926542442915436475742803)
                  ·
                    refine ⟨7389813664373154713614205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926542442915436475742803 7389813664373154713614205)
                    ·
                      refine ⟨2771180124139933017605327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389813664373154713614205 2771180124139933017605327)
                      ·
                        rfl

theorem cell23_5396854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5396854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396854 prefixEnd_5396854 := by exact prefixLift 5396854
  have htrace : WordTrace (prefixWord ++ tailWord_5396854) baseStart_5396854 baseEnd_5396854 := by
    simpa [prefixWord, tailWord_5396854, baseEnd_5396854] using wordTrace_append hprefix tailTrace_5396854
  have hstable : (prefixWord ++ tailWord_5396854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396854).length < 2 ^ (prefixWord ++ tailWord_5396854).sum := by decide
  have hdescent : baseEnd_5396854 < baseStart_5396854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396893 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_5396893 : Nat := 118140960795 + 5396893 * 2 ^ 59
def prefixEnd_5396893 : Nat := 4983230072969 + 3 ^ 40 * 5396893 * 2
def baseEnd_5396893 : Nat := 2771200149885458365017647

theorem tailTrace_5396893 : CollatzResearch.WordTrace tailWord_5396893 prefixEnd_5396893 2771200149885458365017647 := by
  unfold tailWord_5396893
  simp only [CollatzResearch.WordTrace]
  refine ⟨196840858836985851787955333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131227239224657234525303555 196840858836985851787955333)
  ·
    refine ⟨36907661031934847210241625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196840858836985851787955333 36907661031934847210241625)
    ·
      refine ⟨27680745773951135407681219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36907661031934847210241625 27680745773951135407681219)
      ·
        refine ⟨41521118660926703111521829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27680745773951135407681219 41521118660926703111521829)
        ·
          refine ⟨7785209748923756833410343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41521118660926703111521829 7785209748923756833410343)
          ·
            refine ⟨11677814623385635250115515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785209748923756833410343 11677814623385635250115515)
            ·
              refine ⟨17516721935078452875173273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11677814623385635250115515 17516721935078452875173273)
              ·
                refine ⟨13137541451308839656379955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17516721935078452875173273 13137541451308839656379955)
                ·
                  refine ⟨19706312176963259484569933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13137541451308839656379955 19706312176963259484569933)
                  ·
                    refine ⟨7389867066361222306713725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19706312176963259484569933 7389867066361222306713725)
                    ·
                      refine ⟨2771200149885458365017647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389867066361222306713725 2771200149885458365017647)
                      ·
                        rfl

theorem cell23_5396893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_5396893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396893 prefixEnd_5396893 := by exact prefixLift 5396893
  have htrace : WordTrace (prefixWord ++ tailWord_5396893) baseStart_5396893 baseEnd_5396893 := by
    simpa [prefixWord, tailWord_5396893, baseEnd_5396893] using wordTrace_append hprefix tailTrace_5396893
  have hstable : (prefixWord ++ tailWord_5396893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396893).length < 2 ^ (prefixWord ++ tailWord_5396893).sum := by decide
  have hdescent : baseEnd_5396893 < baseStart_5396893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396897 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5396897 : Nat := 118140960795 + 5396897 * 2 ^ 59
def prefixEnd_5396897 : Nat := 4983230072969 + 3 ^ 40 * 5396897 * 2
def baseEnd_5396897 : Nat := 2771202203808076349367629

theorem tailTrace_5396897 : CollatzResearch.WordTrace tailWord_5396897 prefixEnd_5396897 2771202203808076349367629 := by
  unfold tailWord_5396897
  simp only [CollatzResearch.WordTrace]
  refine ⟨196841004728971360471100945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131227336485980906980733963 196841004728971360471100945)
  ·
    refine ⟨147630753546728520353325709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196841004728971360471100945 147630753546728520353325709)
    ·
      refine ⟨55361532580023195132497141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147630753546728520353325709 55361532580023195132497141)
      ·
        refine ⟨5190143679377174543671607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55361532580023195132497141 5190143679377174543671607)
        ·
          refine ⟨7785215519065761815507411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190143679377174543671607 7785215519065761815507411)
          ·
            refine ⟨11677823278598642723261117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785215519065761815507411 11677823278598642723261117)
            ·
              refine ⟨4379183729474491021222919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11677823278598642723261117 4379183729474491021222919)
              ·
                refine ⟨6568775594211736531834379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379183729474491021222919 6568775594211736531834379)
                ·
                  refine ⟨9853163391317604797751569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568775594211736531834379 9853163391317604797751569)
                  ·
                    refine ⟨7389872543488203598313677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9853163391317604797751569 7389872543488203598313677)
                    ·
                      refine ⟨2771202203808076349367629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7389872543488203598313677 2771202203808076349367629)
                      ·
                        rfl

theorem cell23_5396897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5396897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396897 prefixEnd_5396897 := by exact prefixLift 5396897
  have htrace : WordTrace (prefixWord ++ tailWord_5396897) baseStart_5396897 baseEnd_5396897 := by
    simpa [prefixWord, tailWord_5396897, baseEnd_5396897] using wordTrace_append hprefix tailTrace_5396897
  have hstable : (prefixWord ++ tailWord_5396897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396897).length < 2 ^ (prefixWord ++ tailWord_5396897).sum := by decide
  have hdescent : baseEnd_5396897 < baseStart_5396897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396950 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5396950 : Nat := 118140960795 + 5396950 * 2 ^ 59
def prefixEnd_5396950 : Nat := 4983230072969 + 3 ^ 40 * 5396950 * 2
def baseEnd_5396950 : Nat := 2771229418282764642004885

theorem tailTrace_5396950 : CollatzResearch.WordTrace tailWord_5396950 prefixEnd_5396950 2771229418282764642004885 := by
  unfold tailWord_5396950
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302683612361209407673769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131228625198519567015186869 12302683612361209407673769)
  ·
    refine ⟨9227012709270907055755327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12302683612361209407673769 9227012709270907055755327)
    ·
      refine ⟨13840519063906360583632991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9227012709270907055755327 13840519063906360583632991)
      ·
        refine ⟨20760778595859540875449487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13840519063906360583632991 20760778595859540875449487)
        ·
          refine ⟨31141167893789311313174231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20760778595859540875449487 31141167893789311313174231)
          ·
            refine ⟨46711751840683966969761347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31141167893789311313174231 46711751840683966969761347)
            ·
              refine ⟨70067627761025950454642021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46711751840683966969761347 70067627761025950454642021)
              ·
                refine ⟨13137680205192365710245379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70067627761025950454642021 13137680205192365710245379)
                ·
                  refine ⟨19706520307788548565368069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13137680205192365710245379 19706520307788548565368069)
                  ·
                    refine ⟨3694972557710352856006513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19706520307788548565368069 3694972557710352856006513)
                    ·
                      refine ⟨2771229418282764642004885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3694972557710352856006513 2771229418282764642004885)
                      ·
                        rfl

theorem cell23_5396950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5396950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396950 prefixEnd_5396950 := by exact prefixLift 5396950
  have htrace : WordTrace (prefixWord ++ tailWord_5396950) baseStart_5396950 baseEnd_5396950 := by
    simpa [prefixWord, tailWord_5396950, baseEnd_5396950] using wordTrace_append hprefix tailTrace_5396950
  have hstable : (prefixWord ++ tailWord_5396950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396950).length < 2 ^ (prefixWord ++ tailWord_5396950).sum := by decide
  have hdescent : baseEnd_5396950 < baseStart_5396950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396973 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 7]
def baseStart_5396973 : Nat := 118140960795 + 5396973 * 2 ^ 59
def prefixEnd_5396973 : Nat := 4983230072969 + 3 ^ 40 * 5396973 * 2
def baseEnd_5396973 : Nat := 307915692037535339113031

theorem tailTrace_5396973 : CollatzResearch.WordTrace tailWord_5396973 prefixEnd_5396973 307915692037535339113031 := by
  unfold tailWord_5396973
  simp only [CollatzResearch.WordTrace]
  refine ⟨196843776676696025450867573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131229184451130683633911715 196843776676696025450867573)
  ·
    refine ⟨18454104063440252386018835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196843776676696025450867573 18454104063440252386018835)
    ·
      refine ⟨27681156095160378579028253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18454104063440252386018835 27681156095160378579028253)
      ·
        refine ⟨10380433535685141967135595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27681156095160378579028253 10380433535685141967135595)
        ·
          refine ⟨15570650303527712950703393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10380433535685141967135595 15570650303527712950703393)
          ·
            refine ⟨11677987727645784713027545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15570650303527712950703393 11677987727645784713027545)
            ·
              refine ⟨8758490795734338534770659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11677987727645784713027545 8758490795734338534770659)
              ·
                refine ⟨13137736193601507802155989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758490795734338534770659 13137736193601507802155989)
                ·
                  refine ⟨307915692037535339113031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13137736193601507802155989 307915692037535339113031)
                  ·
                    rfl

theorem cell23_5396973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_5396973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396973 prefixEnd_5396973 := by exact prefixLift 5396973
  have htrace : WordTrace (prefixWord ++ tailWord_5396973) baseStart_5396973 baseEnd_5396973 := by
    simpa [prefixWord, tailWord_5396973, baseEnd_5396973] using wordTrace_append hprefix tailTrace_5396973
  have hstable : (prefixWord ++ tailWord_5396973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396973).length < 2 ^ (prefixWord ++ tailWord_5396973).sum := by decide
  have hdescent : baseEnd_5396973 < baseStart_5396973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5396979 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_5396979 : Nat := 118140960795 + 5396979 * 2 ^ 59
def prefixEnd_5396979 : Nat := 4983230072969 + 3 ^ 40 * 5396979 * 2
def baseEnd_5396979 : Nat := 2771244309221745028542251

theorem tailTrace_5396979 : CollatzResearch.WordTrace tailWord_5396979 prefixEnd_5396979 2771244309221745028542251 := by
  unfold tailWord_5396979
  simp only [CollatzResearch.WordTrace]
  refine ⟨196843995514674288475585991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131229330343116192317057327 196843995514674288475585991)
  ·
    refine ⟨295265993272011432713378987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196843995514674288475585991 295265993272011432713378987)
    ·
      refine ⟨442898989908017149070068481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295265993272011432713378987 442898989908017149070068481)
      ·
        refine ⟨332174242431012861802551361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442898989908017149070068481 332174242431012861802551361)
        ·
          refine ⟨249130681823259646351913521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332174242431012861802551361 249130681823259646351913521)
          ·
            refine ⟨186848011367444734763935141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249130681823259646351913521 186848011367444734763935141)
            ·
              refine ⟨35034002131395887768237839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186848011367444734763935141 35034002131395887768237839)
              ·
                refine ⟨52551003197093831652356759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35034002131395887768237839 52551003197093831652356759)
                ·
                  refine ⟨78826504795640747478535139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52551003197093831652356759 78826504795640747478535139)
                  ·
                    refine ⟨118239757193461121217802709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78826504795640747478535139 118239757193461121217802709)
                    ·
                      refine ⟨2771244309221745028542251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118239757193461121217802709 2771244309221745028542251)
                      ·
                        rfl

theorem cell23_5396979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_5396979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5396979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5396979 prefixEnd_5396979 := by exact prefixLift 5396979
  have htrace : WordTrace (prefixWord ++ tailWord_5396979) baseStart_5396979 baseEnd_5396979 := by
    simpa [prefixWord, tailWord_5396979, baseEnd_5396979] using wordTrace_append hprefix tailTrace_5396979
  have hstable : (prefixWord ++ tailWord_5396979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5396979).length < 2 ^ (prefixWord ++ tailWord_5396979).sum := by decide
  have hdescent : baseEnd_5396979 < baseStart_5396979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5396979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397056 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_5397056 : Nat := 118140960795 + 5397056 * 2 ^ 59
def prefixEnd_5397056 : Nat := 4983230072969 + 3 ^ 40 * 5397056 * 2
def baseEnd_5397056 : Nat := 2771283847232141227279397

theorem tailTrace_5397056 : CollatzResearch.WordTrace tailWord_5397056 prefixEnd_5397056 2771283847232141227279397 := by
  unfold tailWord_5397056
  simp only [CollatzResearch.WordTrace]
  refine ⟨98423401967697665313069511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131231202623596887084092681 98423401967697665313069511)
  ·
    refine ⟨147635102951546497969604267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98423401967697665313069511 147635102951546497969604267)
    ·
      refine ⟨221452654427319746954406401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147635102951546497969604267 221452654427319746954406401)
      ·
        refine ⟨166089490820489810215804801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221452654427319746954406401 166089490820489810215804801)
        ·
          refine ⟨124567118115367357661853601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166089490820489810215804801 124567118115367357661853601)
          ·
            refine ⟨93425338586525518246390201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124567118115367357661853601 93425338586525518246390201)
            ·
              refine ⟨70069003939894138684792651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93425338586525518246390201 70069003939894138684792651)
              ·
                refine ⟨105103505909841208027188977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70069003939894138684792651 105103505909841208027188977)
                ·
                  refine ⟨78827629432380906020391733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105103505909841208027188977 78827629432380906020391733)
                  ·
                    refine ⟨7390090259285709939411725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78827629432380906020391733 7390090259285709939411725)
                    ·
                      refine ⟨2771283847232141227279397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390090259285709939411725 2771283847232141227279397)
                      ·
                        rfl

theorem cell23_5397056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_5397056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397056 prefixEnd_5397056 := by exact prefixLift 5397056
  have htrace : WordTrace (prefixWord ++ tailWord_5397056) baseStart_5397056 baseEnd_5397056 := by
    simpa [prefixWord, tailWord_5397056, baseEnd_5397056] using wordTrace_append hprefix tailTrace_5397056
  have hstable : (prefixWord ++ tailWord_5397056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397056).length < 2 ^ (prefixWord ++ tailWord_5397056).sum := by decide
  have hdescent : baseEnd_5397056 < baseStart_5397056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397113 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5397113 : Nat := 118140960795 + 5397113 * 2 ^ 59
def prefixEnd_5397113 : Nat := 4983230072969 + 3 ^ 40 * 5397113 * 2
def baseEnd_5397113 : Nat := 2771313115629447504266635

theorem tailTrace_5397113 : CollatzResearch.WordTrace tailWord_5397113 prefixEnd_5397113 2771313115629447504266635 := by
  unfold tailWord_5397113
  simp only [CollatzResearch.WordTrace]
  refine ⟨196848882896188829360963993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131232588597459219573975995 196848882896188829360963993)
  ·
    refine ⟨147636662172141622020722995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196848882896188829360963993 147636662172141622020722995)
    ·
      refine ⟨221454993258212433031084493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147636662172141622020722995 221454993258212433031084493)
      ·
        refine ⟨83045622471829662386656685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221454993258212433031084493 83045622471829662386656685)
        ·
          refine ⟨31142108426936123394996257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83045622471829662386656685 31142108426936123394996257)
          ·
            refine ⟨23356581320202092546247193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31142108426936123394996257 23356581320202092546247193)
            ·
              refine ⟨17517435990151569409685395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23356581320202092546247193 17517435990151569409685395)
              ·
                refine ⟨26276153985227354114528093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17517435990151569409685395 26276153985227354114528093)
                ·
                  refine ⟨9853557744460257792948035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26276153985227354114528093 9853557744460257792948035)
                  ·
                    refine ⟨14780336616690386689422053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9853557744460257792948035 14780336616690386689422053)
                    ·
                      refine ⟨2771313115629447504266635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14780336616690386689422053 2771313115629447504266635)
                      ·
                        rfl

theorem cell23_5397113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5397113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397113 prefixEnd_5397113 := by exact prefixLift 5397113
  have htrace : WordTrace (prefixWord ++ tailWord_5397113) baseStart_5397113 baseEnd_5397113 := by
    simpa [prefixWord, tailWord_5397113, baseEnd_5397113] using wordTrace_append hprefix tailTrace_5397113
  have hstable : (prefixWord ++ tailWord_5397113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397113).length < 2 ^ (prefixWord ++ tailWord_5397113).sum := by decide
  have hdescent : baseEnd_5397113 < baseStart_5397113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397124 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_5397124 : Nat := 118140960795 + 5397124 * 2 ^ 59
def prefixEnd_5397124 : Nat := 4983230072969 + 3 ^ 40 * 5397124 * 2
def baseEnd_5397124 : Nat := 2771318763916646961229085

theorem tailTrace_5397124 : CollatzResearch.WordTrace tailWord_5397124 prefixEnd_5397124 2771318763916646961229085 := by
  unfold tailWord_5397124
  simp only [CollatzResearch.WordTrace]
  refine ⟨98424642049574489119807213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131232856066099318826409617 98424642049574489119807213)
  ·
    refine ⟨36909240768590433419927705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98424642049574489119807213 36909240768590433419927705)
    ·
      refine ⟨27681930576442825064945779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36909240768590433419927705 27681930576442825064945779)
      ·
        refine ⟨41522895864664237597418669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27681930576442825064945779 41522895864664237597418669)
        ·
          refine ⟨15571085949249089099032001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41522895864664237597418669 15571085949249089099032001)
          ·
            refine ⟨11678314461936816824274001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15571085949249089099032001 11678314461936816824274001)
            ·
              refine ⟨8758735846452612618205501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678314461936816824274001 8758735846452612618205501)
              ·
                refine ⟨3284525942419729731827063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8758735846452612618205501 3284525942419729731827063)
                ·
                  refine ⟨4926788913629594597740595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284525942419729731827063 4926788913629594597740595)
                  ·
                    refine ⟨7390183370444391896610893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926788913629594597740595 7390183370444391896610893)
                    ·
                      refine ⟨2771318763916646961229085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390183370444391896610893 2771318763916646961229085)
                      ·
                        rfl

theorem cell23_5397124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_5397124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397124 prefixEnd_5397124 := by exact prefixLift 5397124
  have htrace : WordTrace (prefixWord ++ tailWord_5397124) baseStart_5397124 baseEnd_5397124 := by
    simpa [prefixWord, tailWord_5397124, baseEnd_5397124] using wordTrace_append hprefix tailTrace_5397124
  have hstable : (prefixWord ++ tailWord_5397124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397124).length < 2 ^ (prefixWord ++ tailWord_5397124).sum := by decide
  have hdescent : baseEnd_5397124 < baseStart_5397124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397150 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5397150 : Nat := 118140960795 + 5397150 * 2 ^ 59
def prefixEnd_5397150 : Nat := 4983230072969 + 3 ^ 40 * 5397150 * 2
def baseEnd_5397150 : Nat := 2771332114413663859503965

theorem tailTrace_5397150 : CollatzResearch.WordTrace tailWord_5397150 prefixEnd_5397150 2771332114413663859503965 := by
  unfold tailWord_5397150
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606279049631848085007613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131233488264703189786707269 24606279049631848085007613)
  ·
    refine ⟨9227354643611943031877855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24606279049631848085007613 9227354643611943031877855)
    ·
      refine ⟨13841031965417914547816783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9227354643611943031877855 13841031965417914547816783)
      ·
        refine ⟨20761547948126871821725175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13841031965417914547816783 20761547948126871821725175)
        ·
          refine ⟨31142321922190307732587763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20761547948126871821725175 31142321922190307732587763)
          ·
            refine ⟨46713482883285461598881645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31142321922190307732587763 46713482883285461598881645)
            ·
              refine ⟨17517556081232048099580617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46713482883285461598881645 17517556081232048099580617)
              ·
                refine ⟨13138167060924036074685463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17517556081232048099580617 13138167060924036074685463)
                ·
                  refine ⟨19707250591386054112028195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13138167060924036074685463 19707250591386054112028195)
                  ·
                    refine ⟨29560875887079081168042293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19707250591386054112028195 29560875887079081168042293)
                    ·
                      refine ⟨2771332114413663859503965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29560875887079081168042293 2771332114413663859503965)
                      ·
                        rfl

theorem cell23_5397150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5397150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397150 prefixEnd_5397150 := by exact prefixLift 5397150
  have htrace : WordTrace (prefixWord ++ tailWord_5397150) baseStart_5397150 baseEnd_5397150 := by
    simpa [prefixWord, tailWord_5397150, baseEnd_5397150] using wordTrace_append hprefix tailTrace_5397150
  have hstable : (prefixWord ++ tailWord_5397150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397150).length < 2 ^ (prefixWord ++ tailWord_5397150).sum := by decide
  have hdescent : baseEnd_5397150 < baseStart_5397150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397180 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_5397180 : Nat := 118140960795 + 5397180 * 2 ^ 59
def prefixEnd_5397180 : Nat := 4983230072969 + 3 ^ 40 * 5397180 * 2
def baseEnd_5397180 : Nat := 2771347518833298742128827

theorem tailTrace_5397180 : CollatzResearch.WordTrace tailWord_5397180 prefixEnd_5397180 2771347518833298742128827 := by
  unfold tailWord_5397180
  simp only [CollatzResearch.WordTrace]
  refine ⟨98425663293473049901826497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131234217724630733202435329 98425663293473049901826497)
  ·
    refine ⟨73819247470104787426369873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98425663293473049901826497 73819247470104787426369873)
    ·
      refine ⟨55364435602578590569777405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73819247470104787426369873 55364435602578590569777405)
      ·
        refine ⟨20761663350966971463666527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55364435602578590569777405 20761663350966971463666527)
        ·
          refine ⟨31142495026450457195499791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20761663350966971463666527 31142495026450457195499791)
          ·
            refine ⟨46713742539675685793249687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31142495026450457195499791 46713742539675685793249687)
            ·
              refine ⟨70070613809513528689874531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46713742539675685793249687 70070613809513528689874531)
              ·
                refine ⟨105105920714270293034811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70070613809513528689874531 105105920714270293034811797)
                ·
                  refine ⟨4926840033481419986006803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105105920714270293034811797 4926840033481419986006803)
                  ·
                    refine ⟨7390260050222129979010205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926840033481419986006803 7390260050222129979010205)
                    ·
                      refine ⟨2771347518833298742128827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390260050222129979010205 2771347518833298742128827)
                      ·
                        rfl

theorem cell23_5397180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_5397180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397180 prefixEnd_5397180 := by exact prefixLift 5397180
  have htrace : WordTrace (prefixWord ++ tailWord_5397180) baseStart_5397180 baseEnd_5397180 := by
    simpa [prefixWord, tailWord_5397180, baseEnd_5397180] using wordTrace_append hprefix tailTrace_5397180
  have hstable : (prefixWord ++ tailWord_5397180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397180).length < 2 ^ (prefixWord ++ tailWord_5397180).sum := by decide
  have hdescent : baseEnd_5397180 < baseStart_5397180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397181 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_5397181 : Nat := 118140960795 + 5397181 * 2 ^ 59
def prefixEnd_5397181 : Nat := 4983230072969 + 3 ^ 40 * 5397181 * 2
def baseEnd_5397181 : Nat := 2771348032313953238216323

theorem tailTrace_5397181 : CollatzResearch.WordTrace tailWord_5397181 prefixEnd_5397181 2771348032313953238216323 := by
  unfold tailWord_5397181
  simp only [CollatzResearch.WordTrace]
  refine ⟨196851363059942476974439397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131234242039961651316292931 196851363059942476974439397)
  ·
    refine ⟨36909630573739214432707387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196851363059942476974439397 36909630573739214432707387)
    ·
      refine ⟨55364445860608821649061081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36909630573739214432707387 55364445860608821649061081)
      ·
        refine ⟨41523334395456616236795811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55364445860608821649061081 41523334395456616236795811)
        ·
          refine ⟨62285001593184924355193717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41523334395456616236795811 62285001593184924355193717)
          ·
            refine ⟨5839218899361086658299411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62285001593184924355193717 5839218899361086658299411)
            ·
              refine ⟨8758828349041629987449117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839218899361086658299411 8758828349041629987449117)
              ·
                refine ⟨3284560630890611245293419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8758828349041629987449117 3284560630890611245293419)
                ·
                  refine ⟨4926840946335916867940129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284560630890611245293419 4926840946335916867940129)
                  ·
                    refine ⟨3695130709751937650955097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4926840946335916867940129 3695130709751937650955097)
                    ·
                      refine ⟨2771348032313953238216323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695130709751937650955097 2771348032313953238216323)
                      ·
                        rfl

theorem cell23_5397181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_5397181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397181 prefixEnd_5397181 := by exact prefixLift 5397181
  have htrace : WordTrace (prefixWord ++ tailWord_5397181) baseStart_5397181 baseEnd_5397181 := by
    simpa [prefixWord, tailWord_5397181, baseEnd_5397181] using wordTrace_append hprefix tailTrace_5397181
  have hstable : (prefixWord ++ tailWord_5397181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397181).length < 2 ^ (prefixWord ++ tailWord_5397181).sum := by decide
  have hdescent : baseEnd_5397181 < baseStart_5397181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397253 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_5397253 : Nat := 118140960795 + 5397253 * 2 ^ 59
def prefixEnd_5397253 : Nat := 4983230072969 + 3 ^ 40 * 5397253 * 2
def baseEnd_5397253 : Nat := 2771385002921076956515991

theorem tailTrace_5397253 : CollatzResearch.WordTrace tailWord_5397253 prefixEnd_5397253 2771385002921076956515991 := by
  unfold tailWord_5397253
  simp only [CollatzResearch.WordTrace]
  refine ⟨196853989115681633271060413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131235992743787755514040275 196853989115681633271060413)
  ·
    refine ⟨73820245918380612476647655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196853989115681633271060413 73820245918380612476647655)
    ·
      refine ⟨110730368877570918714971483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73820245918380612476647655 110730368877570918714971483)
      ·
        refine ⟨166095553316356378072457225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110730368877570918714971483 166095553316356378072457225)
        ·
          refine ⟨124571664987267283554342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166095553316356378072457225 124571664987267283554342919)
          ·
            refine ⟨186857497480900925331514379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124571664987267283554342919 186857497480900925331514379)
            ·
              refine ⟨280286246221351387997271569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186857497480900925331514379 280286246221351387997271569)
              ·
                refine ⟨210214684666013540997953677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280286246221351387997271569 210214684666013540997953677)
                ·
                  refine ⟨78830506749755077874232629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210214684666013540997953677 78830506749755077874232629)
                  ·
                    refine ⟨7390360007789538550709309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78830506749755077874232629 7390360007789538550709309)
                    ·
                      refine ⟨2771385002921076956515991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390360007789538550709309 2771385002921076956515991)
                      ·
                        rfl

theorem cell23_5397253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_5397253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397253 prefixEnd_5397253 := by exact prefixLift 5397253
  have htrace : WordTrace (prefixWord ++ tailWord_5397253) baseStart_5397253 baseEnd_5397253 := by
    simpa [prefixWord, tailWord_5397253, baseEnd_5397253] using wordTrace_append hprefix tailTrace_5397253
  have hstable : (prefixWord ++ tailWord_5397253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397253).length < 2 ^ (prefixWord ++ tailWord_5397253).sum := by decide
  have hdescent : baseEnd_5397253 < baseStart_5397253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397277 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 7]
def baseStart_5397277 : Nat := 118140960795 + 5397277 * 2 ^ 59
def prefixEnd_5397277 : Nat := 4983230072969 + 3 ^ 40 * 5397277 * 2
def baseEnd_5397277 : Nat := 307933036272976095846209

theorem tailTrace_5397277 : CollatzResearch.WordTrace tailWord_5397277 prefixEnd_5397277 307933036272976095846209 := by
  unfold tailWord_5397277
  simp only [CollatzResearch.WordTrace]
  refine ⟨196854864467594685369934085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131236576311729790246622723 196854864467594685369934085)
  ·
    refine ⟨36910287087674003506862641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196854864467594685369934085 36910287087674003506862641)
    ·
      refine ⟨27682715315755502630146981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36910287087674003506862641 27682715315755502630146981)
      ·
        refine ⟨5190509121704156743152559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27682715315755502630146981 5190509121704156743152559)
        ·
          refine ⟨7785763682556235114728839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190509121704156743152559 7785763682556235114728839)
          ·
            refine ⟨11678645523834352672093259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785763682556235114728839 11678645523834352672093259)
            ·
              refine ⟨17517968285751529008139889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11678645523834352672093259 17517968285751529008139889)
              ·
                refine ⟨13138476214313646756104917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17517968285751529008139889 13138476214313646756104917)
                ·
                  refine ⟨307933036272976095846209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13138476214313646756104917 307933036272976095846209)
                  ·
                    rfl

theorem cell23_5397277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_5397277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397277 prefixEnd_5397277 := by exact prefixLift 5397277
  have htrace : WordTrace (prefixWord ++ tailWord_5397277) baseStart_5397277 baseEnd_5397277 := by
    simpa [prefixWord, tailWord_5397277, baseEnd_5397277] using wordTrace_append hprefix tailTrace_5397277
  have hstable : (prefixWord ++ tailWord_5397277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397277).length < 2 ^ (prefixWord ++ tailWord_5397277).sum := by decide
  have hdescent : baseEnd_5397277 < baseStart_5397277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397294 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_5397294 : Nat := 118140960795 + 5397294 * 2 ^ 59
def prefixEnd_5397294 : Nat := 4983230072969 + 3 ^ 40 * 5397294 * 2
def baseEnd_5397294 : Nat := 307934006180879032900367

theorem tailTrace_5397294 : CollatzResearch.WordTrace tailWord_5397294 prefixEnd_5397294 307934006180879032900367 := by
  unfold tailWord_5397294
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606935563566637159162867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131236989672355398182201957 24606935563566637159162867)
  ·
    refine ⟨36910403345349955738744301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24606935563566637159162867 36910403345349955738744301)
    ·
      refine ⟨13841401254506233402029113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36910403345349955738744301 13841401254506233402029113)
      ·
        refine ⟨10381050940879675051521835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13841401254506233402029113 10381050940879675051521835)
        ·
          refine ⟨15571576411319512577282753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381050940879675051521835 15571576411319512577282753)
          ·
            refine ⟨11678682308489634432962065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15571576411319512577282753 11678682308489634432962065)
            ·
              refine ⟨8759011731367225824721549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678682308489634432962065 8759011731367225824721549)
              ·
                refine ⟨3284629399262709684270581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8759011731367225824721549 3284629399262709684270581)
                ·
                  refine ⟨307934006180879032900367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284629399262709684270581 307934006180879032900367)
                  ·
                    rfl

theorem cell23_5397294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_5397294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397294 prefixEnd_5397294 := by exact prefixLift 5397294
  have htrace : WordTrace (prefixWord ++ tailWord_5397294) baseStart_5397294 baseEnd_5397294 := by
    simpa [prefixWord, tailWord_5397294, baseEnd_5397294] using wordTrace_append hprefix tailTrace_5397294
  have hstable : (prefixWord ++ tailWord_5397294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397294).length < 2 ^ (prefixWord ++ tailWord_5397294).sum := by decide
  have hdescent : baseEnd_5397294 < baseStart_5397294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397330 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_5397330 : Nat := 118140960795 + 5397330 * 2 ^ 59
def prefixEnd_5397330 : Nat := 4983230072969 + 3 ^ 40 * 5397330 * 2
def baseEnd_5397330 : Nat := 2771424540931473155253137

theorem tailTrace_5397330 : CollatzResearch.WordTrace tailWord_5397330 prefixEnd_5397330 2771424540931473155253137 := by
  unfold tailWord_5397330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49214199384100668855403361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131237865024268450281075629 49214199384100668855403361)
  ·
    refine ⟨36910649538075501641552521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49214199384100668855403361 36910649538075501641552521)
    ·
      refine ⟨27682987153556626231164391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36910649538075501641552521 27682987153556626231164391)
      ·
        refine ⟨41524480730334939346746587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27682987153556626231164391 41524480730334939346746587)
        ·
          refine ⟨62286721095502409020119881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41524480730334939346746587 62286721095502409020119881)
          ·
            refine ⟨46715040821626806765089911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62286721095502409020119881 46715040821626806765089911)
            ·
              refine ⟨70072561232440210147634867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46715040821626806765089911 70072561232440210147634867)
              ·
                refine ⟨105108841848660315221452301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70072561232440210147634867 105108841848660315221452301)
                ·
                  refine ⟨39415815693247618208044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105108841848660315221452301 39415815693247618208044613)
                  ·
                    refine ⟨7390465442483928414008365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39415815693247618208044613 7390465442483928414008365)
                    ·
                      refine ⟨2771424540931473155253137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390465442483928414008365 2771424540931473155253137)
                      ·
                        rfl

theorem cell23_5397330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_5397330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397330 prefixEnd_5397330 := by exact prefixLift 5397330
  have htrace : WordTrace (prefixWord ++ tailWord_5397330) baseStart_5397330 baseEnd_5397330 := by
    simpa [prefixWord, tailWord_5397330, baseEnd_5397330] using wordTrace_append hprefix tailTrace_5397330
  have hstable : (prefixWord ++ tailWord_5397330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397330).length < 2 ^ (prefixWord ++ tailWord_5397330).sum := by decide
  have hdescent : baseEnd_5397330 < baseStart_5397330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397380 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5397380 : Nat := 118140960795 + 5397380 * 2 ^ 59
def prefixEnd_5397380 : Nat := 4983230072969 + 3 ^ 40 * 5397380 * 2
def baseEnd_5397380 : Nat := 923816738321399319875969

theorem tailTrace_5397380 : CollatzResearch.WordTrace tailWord_5397380 prefixEnd_5397380 923816738321399319875969 := by
  unfold tailWord_5397380
  simp only [CollatzResearch.WordTrace]
  refine ⟨98429310593110766980466797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131239080790814355973955729 98429310593110766980466797)
  ·
    refine ⟨36910991472416537617675049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98429310593110766980466797 36910991472416537617675049)
    ·
      refine ⟨27683243604312403213256287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36910991472416537617675049 27683243604312403213256287)
      ·
        refine ⟨41524865406468604819884431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27683243604312403213256287 41524865406468604819884431)
        ·
          refine ⟨62287298109702907229826647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41524865406468604819884431 62287298109702907229826647)
          ·
            refine ⟨93430947164554360844739971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62287298109702907229826647 93430947164554360844739971)
            ·
              refine ⟨140146420746831541267109957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93430947164554360844739971 140146420746831541267109957)
              ·
                refine ⟨26277453890030913987583117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140146420746831541267109957 26277453890030913987583117)
                ·
                  refine ⟨9854045208761592745343669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26277453890030913987583117 9854045208761592745343669)
                  ·
                    refine ⟨923816738321399319875969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9854045208761592745343669 923816738321399319875969)
                    ·
                      rfl

theorem cell23_5397380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5397380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397380 prefixEnd_5397380 := by exact prefixLift 5397380
  have htrace : WordTrace (prefixWord ++ tailWord_5397380) baseStart_5397380 baseEnd_5397380 := by
    simpa [prefixWord, tailWord_5397380, baseEnd_5397380] using wordTrace_append hprefix tailTrace_5397380
  have hstable : (prefixWord ++ tailWord_5397380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397380).length < 2 ^ (prefixWord ++ tailWord_5397380).sum := by decide
  have hdescent : baseEnd_5397380 < baseStart_5397380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397384 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 6]
def baseStart_5397384 : Nat := 118140960795 + 5397384 * 2 ^ 59
def prefixEnd_5397384 : Nat := 4983230072969 + 3 ^ 40 * 5397384 * 2
def baseEnd_5397384 : Nat := 307939140987423993775321

theorem tailTrace_5397384 : CollatzResearch.WordTrace tailWord_5397384 prefixEnd_5397384 307939140987423993775321 := by
  unfold tailWord_5397384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98429383539103521322039603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131239178052138028429386137 98429383539103521322039603)
  ·
    refine ⟨147644075308655281983059405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98429383539103521322039603 147644075308655281983059405)
    ·
      refine ⟨55366528240745730743647277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147644075308655281983059405 55366528240745730743647277)
      ·
        refine ⟨20762448090279649028867729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55366528240745730743647277 20762448090279649028867729)
        ·
          refine ⟨15571836067709736771650797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20762448090279649028867729 15571836067709736771650797)
          ·
            refine ⟨5839438525391151289369049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15571836067709736771650797 5839438525391151289369049)
            ·
              refine ⟨4379578894043363467026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5839438525391151289369049 4379578894043363467026787)
              ·
                refine ⟨6569368341065045200540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379578894043363467026787 6569368341065045200540181)
                ·
                  refine ⟨307939140987423993775321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6569368341065045200540181 307939140987423993775321)
                  ·
                    rfl

theorem cell23_5397384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_5397384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397384 prefixEnd_5397384 := by exact prefixLift 5397384
  have htrace : WordTrace (prefixWord ++ tailWord_5397384) baseStart_5397384 baseEnd_5397384 := by
    simpa [prefixWord, tailWord_5397384, baseEnd_5397384] using wordTrace_append hprefix tailTrace_5397384
  have hstable : (prefixWord ++ tailWord_5397384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397384).length < 2 ^ (prefixWord ++ tailWord_5397384).sum := by decide
  have hdescent : baseEnd_5397384 < baseStart_5397384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397397 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_5397397 : Nat := 118140960795 + 5397397 * 2 ^ 59
def prefixEnd_5397397 : Nat := 4983230072969 + 3 ^ 40 * 5397397 * 2
def baseEnd_5397397 : Nat := 923819648045108131038443

theorem tailTrace_5397397 : CollatzResearch.WordTrace tailWord_5397397 prefixEnd_5397397 923819648045108131038443 := by
  unfold tailWord_5397397
  simp only [CollatzResearch.WordTrace]
  refine ⟨196859241227159945864302445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131239494151439963909534963 196859241227159945864302445)
  ·
    refine ⟨73822215460184979699113417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196859241227159945864302445 73822215460184979699113417)
    ·
      refine ⟨55366661595138734774335063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73822215460184979699113417 55366661595138734774335063)
      ·
        refine ⟨83049992392708102161502595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55366661595138734774335063 83049992392708102161502595)
        ·
          refine ⟨124574988589062153242253893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83049992392708102161502595 124574988589062153242253893)
          ·
            refine ⟨23357810360449153732922605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124574988589062153242253893 23357810360449153732922605)
            ·
              refine ⟨8759178885168432649845977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23357810360449153732922605 8759178885168432649845977)
              ·
                refine ⟨6569384163876324487384483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8759178885168432649845977 6569384163876324487384483)
                ·
                  refine ⟨9854076245814486731076725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569384163876324487384483 9854076245814486731076725)
                  ·
                    refine ⟨923819648045108131038443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9854076245814486731076725 923819648045108131038443)
                    ·
                      rfl

theorem cell23_5397397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_5397397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397397 prefixEnd_5397397 := by exact prefixLift 5397397
  have htrace : WordTrace (prefixWord ++ tailWord_5397397) baseStart_5397397 baseEnd_5397397 := by
    simpa [prefixWord, tailWord_5397397, baseEnd_5397397] using wordTrace_append hprefix tailTrace_5397397
  have hstable : (prefixWord ++ tailWord_5397397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397397).length < 2 ^ (prefixWord ++ tailWord_5397397).sum := by decide
  have hdescent : baseEnd_5397397 < baseStart_5397397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397398 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5397398 : Nat := 118140960795 + 5397398 * 2 ^ 59
def prefixEnd_5397398 : Nat := 4983230072969 + 3 ^ 40 * 5397398 * 2
def baseEnd_5397398 : Nat := 2771459457615978889202825

theorem tailTrace_5397398 : CollatzResearch.WordTrace tailWord_5397398 prefixEnd_5397398 2771459457615978889202825 := by
  unfold tailWord_5397398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303704856259770189693053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131239518466770882023392565 12303704856259770189693053)
  ·
    refine ⟨4613889321097413821134895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12303704856259770189693053 4613889321097413821134895)
    ·
      refine ⟨6920833981646120731702343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613889321097413821134895 6920833981646120731702343)
      ·
        refine ⟨10381250972469181097553515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920833981646120731702343 10381250972469181097553515)
        ·
          refine ⟨15571876458703771646330273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381250972469181097553515 15571876458703771646330273)
          ·
            refine ⟨11678907344027828734747705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15571876458703771646330273 11678907344027828734747705)
            ·
              refine ⟨8759180508020871551060779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678907344027828734747705 8759180508020871551060779)
              ·
                refine ⟨13138770762031307326591169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8759180508020871551060779 13138770762031307326591169)
                ·
                  refine ⟨9854078071523480494943377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13138770762031307326591169 9854078071523480494943377)
                  ·
                    refine ⟨7390558553642610371207533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9854078071523480494943377 7390558553642610371207533)
                    ·
                      refine ⟨2771459457615978889202825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390558553642610371207533 2771459457615978889202825)
                      ·
                        rfl

theorem cell23_5397398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5397398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397398 prefixEnd_5397398 := by exact prefixLift 5397398
  have htrace : WordTrace (prefixWord ++ tailWord_5397398) baseStart_5397398 baseEnd_5397398 := by
    simpa [prefixWord, tailWord_5397398, baseEnd_5397398] using wordTrace_append hprefix tailTrace_5397398
  have hstable : (prefixWord ++ tailWord_5397398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397398).length < 2 ^ (prefixWord ++ tailWord_5397398).sum := by decide
  have hdescent : baseEnd_5397398 < baseStart_5397398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397434 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_5397434 : Nat := 118140960795 + 5397434 * 2 ^ 59
def prefixEnd_5397434 : Nat := 4983230072969 + 3 ^ 40 * 5397434 * 2
def baseEnd_5397434 : Nat := 2771477942919540748352659

theorem tailTrace_5397434 : CollatzResearch.WordTrace tailWord_5397434 prefixEnd_5397434 2771477942919540748352659 := by
  unfold tailWord_5397434
  simp only [CollatzResearch.WordTrace]
  refine ⟨49215147682006475295849839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131240393818683934122266237 49215147682006475295849839)
  ·
    refine ⟨73822721523009712943774759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49215147682006475295849839 73822721523009712943774759)
    ·
      refine ⟨110734082284514569415662139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73822721523009712943774759 110734082284514569415662139)
      ·
        refine ⟨166101123426771854123493209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110734082284514569415662139 166101123426771854123493209)
        ·
          refine ⟨124575842570078890592619907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166101123426771854123493209 124575842570078890592619907)
          ·
            refine ⟨186863763855118335888929861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124575842570078890592619907 186863763855118335888929861)
            ·
              refine ⟨35036955722834687979174349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186863763855118335888929861 35036955722834687979174349)
              ·
                refine ⟨13138858396063007992190381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35036955722834687979174349 13138858396063007992190381)
                ·
                  refine ⟨4927071898523627997071393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13138858396063007992190381 4927071898523627997071393)
                  ·
                    refine ⟨3695303923892720997803545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927071898523627997071393 3695303923892720997803545)
                    ·
                      refine ⟨2771477942919540748352659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695303923892720997803545 2771477942919540748352659)
                      ·
                        rfl

theorem cell23_5397434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_5397434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397434 prefixEnd_5397434 := by exact prefixLift 5397434
  have htrace : WordTrace (prefixWord ++ tailWord_5397434) baseStart_5397434 baseEnd_5397434 := by
    simpa [prefixWord, tailWord_5397434, baseEnd_5397434] using wordTrace_append hprefix tailTrace_5397434
  have hstable : (prefixWord ++ tailWord_5397434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397434).length < 2 ^ (prefixWord ++ tailWord_5397434).sum := by decide
  have hdescent : baseEnd_5397434 < baseStart_5397434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397440 : List Nat := [2, 1, 1, 2, 3, 3, 3, 8]
def baseStart_5397440 : Nat := 118140960795 + 5397440 * 2 ^ 59
def prefixEnd_5397440 : Nat := 4983230072969 + 3 ^ 40 * 5397440 * 2
def baseEnd_5397440 : Nat := 102647445326054360180653

theorem tailTrace_5397440 : CollatzResearch.WordTrace tailWord_5397440 prefixEnd_5397440 102647445326054360180653 := by
  unfold tailWord_5397440
  simp only [CollatzResearch.WordTrace]
  refine ⟨98430404783002082104058887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131240539710669442805411849 98430404783002082104058887)
  ·
    refine ⟨147645607174503123156088331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98430404783002082104058887 147645607174503123156088331)
    ·
      refine ⟨221468410761754684734132497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147645607174503123156088331 221468410761754684734132497)
      ·
        refine ⟨166101308071316013550599373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221468410761754684734132497 166101308071316013550599373)
        ·
          refine ⟨62287990526743505081474765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166101308071316013550599373 62287990526743505081474765)
          ·
            refine ⟨23357996447528814405553037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62287990526743505081474765 23357996447528814405553037)
            ·
              refine ⟨8759248667823305402082389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23357996447528814405553037 8759248667823305402082389)
              ·
                refine ⟨102647445326054360180653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8759248667823305402082389 102647445326054360180653)
                ·
                  rfl

theorem cell23_5397440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_5397440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397440 prefixEnd_5397440 := by exact prefixLift 5397440
  have htrace : WordTrace (prefixWord ++ tailWord_5397440) baseStart_5397440 baseEnd_5397440 := by
    simpa [prefixWord, tailWord_5397440, baseEnd_5397440] using wordTrace_append hprefix tailTrace_5397440
  have hstable : (prefixWord ++ tailWord_5397440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397440).length < 2 ^ (prefixWord ++ tailWord_5397440).sum := by decide
  have hdescent : baseEnd_5397440 < baseStart_5397440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397511 : List Nat := [1, 1, 4, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5397511 : Nat := 118140960795 + 5397511 * 2 ^ 59
def prefixEnd_5397511 : Nat := 4983230072969 + 3 ^ 40 * 5397511 * 2
def baseEnd_5397511 : Nat := 2771517480929936947089805

theorem tailTrace_5397511 : CollatzResearch.WordTrace tailWord_5397511 prefixEnd_5397511 2771517480929936947089805 := by
  unfold tailWord_5397511
  simp only [CollatzResearch.WordTrace]
  refine ⟨196863399148746943333952387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131242266099164628889301591 196863399148746943333952387)
  ·
    refine ⟨295295098723120415000928581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196863399148746943333952387 295295098723120415000928581)
    ·
      refine ⟨55367831010585077812674109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295295098723120415000928581 55367831010585077812674109)
      ·
        refine ⟨20762936628969404179752791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55367831010585077812674109 20762936628969404179752791)
        ·
          refine ⟨31144404943454106269629187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20762936628969404179752791 31144404943454106269629187)
          ·
            refine ⟨46716607415181159404443781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31144404943454106269629187 46716607415181159404443781)
            ·
              refine ⟨8759363890346467388333209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46716607415181159404443781 8759363890346467388333209)
              ·
                refine ⟨6569522917759850541249907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8759363890346467388333209 6569522917759850541249907)
                ·
                  refine ⟨9854284376639775811874861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569522917759850541249907 9854284376639775811874861)
                  ·
                    refine ⟨3695356641239915929453073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9854284376639775811874861 3695356641239915929453073)
                    ·
                      refine ⟨2771517480929936947089805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695356641239915929453073 2771517480929936947089805)
                      ·
                        rfl

theorem cell23_5397511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5397511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397511 prefixEnd_5397511 := by exact prefixLift 5397511
  have htrace : WordTrace (prefixWord ++ tailWord_5397511) baseStart_5397511 baseEnd_5397511 := by
    simpa [prefixWord, tailWord_5397511, baseEnd_5397511] using wordTrace_append hprefix tailTrace_5397511
  have hstable : (prefixWord ++ tailWord_5397511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397511).length < 2 ^ (prefixWord ++ tailWord_5397511).sum := by decide
  have hdescent : baseEnd_5397511 < baseStart_5397511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397527 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5397527 : Nat := 118140960795 + 5397527 * 2 ^ 59
def prefixEnd_5397527 : Nat := 4983230072969 + 3 ^ 40 * 5397527 * 2
def baseEnd_5397527 : Nat := 2771525696620408884489731

theorem tailTrace_5397527 : CollatzResearch.WordTrace tailWord_5397527 prefixEnd_5397527 2771525696620408884489731 := by
  unfold tailWord_5397527
  simp only [CollatzResearch.WordTrace]
  refine ⟨196863982716688978066534835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131242655144459318711023223 196863982716688978066534835)
  ·
    refine ⟨295295974075033467099802253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196863982716688978066534835 295295974075033467099802253)
    ·
      refine ⟨110735990278137550162425845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295295974075033467099802253 110735990278137550162425845)
      ·
        refine ⟨10381499088575395327727423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110735990278137550162425845 10381499088575395327727423)
        ·
          refine ⟨15572248632863092991591135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381499088575395327727423 15572248632863092991591135)
          ·
            refine ⟨23358372949294639487386703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15572248632863092991591135 23358372949294639487386703)
            ·
              refine ⟨35037559423941959231080055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23358372949294639487386703 35037559423941959231080055)
              ·
                refine ⟨52556339135912938846620083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35037559423941959231080055 52556339135912938846620083)
                ·
                  refine ⟨78834508703869408269930125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52556339135912938846620083 78834508703869408269930125)
                  ·
                    refine ⟨29562940763951028101223797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78834508703869408269930125 29562940763951028101223797)
                    ·
                      refine ⟨2771525696620408884489731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29562940763951028101223797 2771525696620408884489731)
                      ·
                        rfl

theorem cell23_5397527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5397527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397527 prefixEnd_5397527 := by exact prefixLift 5397527
  have htrace : WordTrace (prefixWord ++ tailWord_5397527) baseStart_5397527 baseEnd_5397527 := by
    simpa [prefixWord, tailWord_5397527, baseEnd_5397527] using wordTrace_append hprefix tailTrace_5397527
  have hstable : (prefixWord ++ tailWord_5397527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397527).length < 2 ^ (prefixWord ++ tailWord_5397527).sum := by decide
  have hdescent : baseEnd_5397527 < baseStart_5397527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397541 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_5397541 : Nat := 118140960795 + 5397541 * 2 ^ 59
def prefixEnd_5397541 : Nat := 4983230072969 + 3 ^ 40 * 5397541 * 2
def baseEnd_5397541 : Nat := 2771532885349571829714667

theorem tailTrace_5397541 : CollatzResearch.WordTrace tailWord_5397541 prefixEnd_5397541 2771532885349571829714667 := by
  unfold tailWord_5397541
  simp only [CollatzResearch.WordTrace]
  refine ⟨196864493338638258457544477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131242995559092172305029651 196864493338638258457544477)
  ·
    refine ⟨73824185001989346921579179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196864493338638258457544477 73824185001989346921579179)
    ·
      refine ⟨110736277502984020382368769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73824185001989346921579179 110736277502984020382368769)
      ·
        refine ⟨83052208127238015286776577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110736277502984020382368769 83052208127238015286776577)
        ·
          refine ⟨62289156095428511465082433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83052208127238015286776577 62289156095428511465082433)
          ·
            refine ⟨46716867071571383598811825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62289156095428511465082433 46716867071571383598811825)
            ·
              refine ⟨35037650303678537699108869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46716867071571383598811825 35037650303678537699108869)
              ·
                refine ⟨6569559431939725818582913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35037650303678537699108869 6569559431939725818582913)
                ·
                  refine ⟨4927169573954794363937185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6569559431939725818582913 4927169573954794363937185)
                  ·
                    refine ⟨3695377180466095772952889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927169573954794363937185 3695377180466095772952889)
                    ·
                      refine ⟨2771532885349571829714667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695377180466095772952889 2771532885349571829714667)
                      ·
                        rfl

theorem cell23_5397541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_5397541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397541 prefixEnd_5397541 := by exact prefixLift 5397541
  have htrace : WordTrace (prefixWord ++ tailWord_5397541) baseStart_5397541 baseEnd_5397541 := by
    simpa [prefixWord, tailWord_5397541, baseEnd_5397541] using wordTrace_append hprefix tailTrace_5397541
  have hstable : (prefixWord ++ tailWord_5397541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397541).length < 2 ^ (prefixWord ++ tailWord_5397541).sum := by decide
  have hdescent : baseEnd_5397541 < baseStart_5397541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397557 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_5397557 : Nat := 118140960795 + 5397557 * 2 ^ 59
def prefixEnd_5397557 : Nat := 4983230072969 + 3 ^ 40 * 5397557 * 2
def baseEnd_5397557 : Nat := 2771541101040043767114593

theorem tailTrace_5397557 : CollatzResearch.WordTrace tailWord_5397557 prefixEnd_5397557 2771541101040043767114593 := by
  unfold tailWord_5397557
  simp only [CollatzResearch.WordTrace]
  refine ⟨196865076906580293190126925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131243384604386862126751283 196865076906580293190126925)
  ·
    refine ⟨73824403839967609946297597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196865076906580293190126925 73824403839967609946297597)
    ·
      refine ⟨27684151439987853729861599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73824403839967609946297597 27684151439987853729861599)
      ·
        refine ⟨41526227159981780594792399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27684151439987853729861599 41526227159981780594792399)
        ·
          refine ⟨62289340739972670892188599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41526227159981780594792399 62289340739972670892188599)
          ·
            refine ⟨93434011109959006338282899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62289340739972670892188599 93434011109959006338282899)
            ·
              refine ⟨140151016664938509507424349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93434011109959006338282899 140151016664938509507424349)
              ·
                refine ⟨52556631249351941065284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140151016664938509507424349 52556631249351941065284131)
                ·
                  refine ⟨78834946874027911597926197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52556631249351941065284131 78834946874027911597926197)
                  ·
                    refine ⟨7390776269440116712305581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78834946874027911597926197 7390776269440116712305581)
                    ·
                      refine ⟨2771541101040043767114593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390776269440116712305581 2771541101040043767114593)
                      ·
                        rfl

theorem cell23_5397557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_5397557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397557 prefixEnd_5397557 := by exact prefixLift 5397557
  have htrace : WordTrace (prefixWord ++ tailWord_5397557) baseStart_5397557 baseEnd_5397557 := by
    simpa [prefixWord, tailWord_5397557, baseEnd_5397557] using wordTrace_append hprefix tailTrace_5397557
  have hstable : (prefixWord ++ tailWord_5397557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397557).length < 2 ^ (prefixWord ++ tailWord_5397557).sum := by decide
  have hdescent : baseEnd_5397557 < baseStart_5397557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397641 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 1, 4]
def baseStart_5397641 : Nat := 118140960795 + 5397641 * 2 ^ 59
def prefixEnd_5397641 : Nat := 4983230072969 + 3 ^ 40 * 5397641 * 2
def baseEnd_5397641 : Nat := 923861411138340479488069

theorem tailTrace_5397641 : CollatzResearch.WordTrace tailWord_5397641 prefixEnd_5397641 923861411138340479488069 := by
  unfold tailWord_5397641
  simp only [CollatzResearch.WordTrace]
  refine ⟨196868140638275975536184777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131245427092183983690789851 196868140638275975536184777)
  ·
    refine ⟨147651105478706981652138583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196868140638275975536184777 147651105478706981652138583)
    ·
      refine ⟨221476658218060472478207875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147651105478706981652138583 221476658218060472478207875)
      ·
        refine ⟨332214987327090708717311813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221476658218060472478207875 332214987327090708717311813)
        ·
          refine ⟨62290310123829507884495965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332214987327090708717311813 62290310123829507884495965)
          ·
            refine ⟨23358866296436065456685987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62290310123829507884495965 23358866296436065456685987)
            ·
              refine ⟨35038299444654098185028981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23358866296436065456685987 35038299444654098185028981)
              ·
                refine ⟨3284840572936321704846467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35038299444654098185028981 3284840572936321704846467)
                ·
                  refine ⟨4927260859404482557269701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284840572936321704846467 4927260859404482557269701)
                  ·
                    refine ⟨923861411138340479488069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927260859404482557269701 923861411138340479488069)
                    ·
                      rfl

theorem cell23_5397641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_5397641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397641 prefixEnd_5397641 := by exact prefixLift 5397641
  have htrace : WordTrace (prefixWord ++ tailWord_5397641) baseStart_5397641 baseEnd_5397641 := by
    simpa [prefixWord, tailWord_5397641, baseEnd_5397641] using wordTrace_append hprefix tailTrace_5397641
  have hstable : (prefixWord ++ tailWord_5397641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397641).length < 2 ^ (prefixWord ++ tailWord_5397641).sum := by decide
  have hdescent : baseEnd_5397641 < baseStart_5397641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397658 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_5397658 : Nat := 118140960795 + 5397658 * 2 ^ 59
def prefixEnd_5397658 : Nat := 4983230072969 + 3 ^ 40 * 5397658 * 2
def baseEnd_5397658 : Nat := 923864320862049290650543

theorem tailTrace_5397658 : CollatzResearch.WordTrace tailWord_5397658 prefixEnd_5397658 923864320862049290650543 := by
  unfold tailWord_5397658
  simp only [CollatzResearch.WordTrace]
  refine ⟨49217190169803596859888407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131245840452809591626369085 49217190169803596859888407)
  ·
    refine ⟨73825785254705395289832611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49217190169803596859888407 73825785254705395289832611)
    ·
      refine ⟨110738677882058092934748917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73825785254705395289832611 110738677882058092934748917)
      ·
        refine ⟨10381751051442946212632711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110738677882058092934748917 10381751051442946212632711)
        ·
          refine ⟨15572626577164419318949067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381751051442946212632711 15572626577164419318949067)
          ·
            refine ⟨23358939865746628978423601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15572626577164419318949067 23358939865746628978423601)
            ·
              refine ⟨17519204899309971733817701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23358939865746628978423601 17519204899309971733817701)
              ·
                refine ⟨3284850918620619700090819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17519204899309971733817701 3284850918620619700090819)
                ·
                  refine ⟨4927276377930929550136229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284850918620619700090819 4927276377930929550136229)
                  ·
                    refine ⟨923864320862049290650543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927276377930929550136229 923864320862049290650543)
                    ·
                      rfl

theorem cell23_5397658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_5397658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397658 prefixEnd_5397658 := by exact prefixLift 5397658
  have htrace : WordTrace (prefixWord ++ tailWord_5397658) baseStart_5397658 baseEnd_5397658 := by
    simpa [prefixWord, tailWord_5397658, baseEnd_5397658] using wordTrace_append hprefix tailTrace_5397658
  have hstable : (prefixWord ++ tailWord_5397658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397658).length < 2 ^ (prefixWord ++ tailWord_5397658).sum := by decide
  have hdescent : baseEnd_5397658 < baseStart_5397658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397667 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 5, 5]
def baseStart_5397667 : Nat := 118140960795 + 5397667 * 2 ^ 59
def prefixEnd_5397667 : Nat := 4983230072969 + 3 ^ 40 * 5397667 * 2
def baseEnd_5397667 : Nat := 923865861304012778913029

theorem tailTrace_5397667 : CollatzResearch.WordTrace tailWord_5397667 prefixEnd_5397667 923865861304012778913029 := by
  unfold tailWord_5397667
  simp only [CollatzResearch.WordTrace]
  refine ⟨196869088936181781976631255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131246059290787854651087503 196869088936181781976631255)
  ·
    refine ⟨295303633404272672964946883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196869088936181781976631255 295303633404272672964946883)
    ·
      refine ⟨442955450106409009447420325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295303633404272672964946883 442955450106409009447420325)
      ·
        refine ⟨83054146894951689271391311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 442955450106409009447420325 83054146894951689271391311)
        ·
          refine ⟨124581220342427533907086967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83054146894951689271391311 124581220342427533907086967)
          ·
            refine ⟨186871830513641300860630451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124581220342427533907086967 186871830513641300860630451)
            ·
              refine ⟨280307745770461951290945677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186871830513641300860630451 280307745770461951290945677)
              ·
                refine ⟨105115404663923231734104629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280307745770461951290945677 105115404663923231734104629)
                ·
                  refine ⟨9854569187242802975072309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105115404663923231734104629 9854569187242802975072309)
                  ·
                    refine ⟨923865861304012778913029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9854569187242802975072309 923865861304012778913029)
                    ·
                      rfl

theorem cell23_5397667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].length) (baseStart_5397667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397667 prefixEnd_5397667 := by exact prefixLift 5397667
  have htrace : WordTrace (prefixWord ++ tailWord_5397667) baseStart_5397667 baseEnd_5397667 := by
    simpa [prefixWord, tailWord_5397667, baseEnd_5397667] using wordTrace_append hprefix tailTrace_5397667
  have hstable : (prefixWord ++ tailWord_5397667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397667).length < 2 ^ (prefixWord ++ tailWord_5397667).sum := by decide
  have hdescent : baseEnd_5397667 < baseStart_5397667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397702 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5397702 : Nat := 118140960795 + 5397702 * 2 ^ 59
def prefixEnd_5397702 : Nat := 4983230072969 + 3 ^ 40 * 5397702 * 2
def baseEnd_5397702 : Nat := 2771615555734945699801427

theorem tailTrace_5397702 : CollatzResearch.WordTrace tailWord_5397702 prefixEnd_5397702 2771615555734945699801427 := by
  unfold tailWord_5397702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152198921595468217317355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131246910327369988636103573 6152198921595468217317355)
  ·
    refine ⟨9228298382393202325976033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6152198921595468217317355 9228298382393202325976033)
    ·
      refine ⟨6921223786794901744482025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9228298382393202325976033 6921223786794901744482025)
      ·
        refine ⟨5190917840096176308361519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921223786794901744482025 5190917840096176308361519)
        ·
          refine ⟨7786376760144264462542279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190917840096176308361519 7786376760144264462542279)
          ·
            refine ⟨11679565140216396693813419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786376760144264462542279 11679565140216396693813419)
            ·
              refine ⟨17519347710324595040720129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11679565140216396693813419 17519347710324595040720129)
              ·
                refine ⟨13139510782743446280540097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17519347710324595040720129 13139510782743446280540097)
                ·
                  refine ⟨9854633087057584710405073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13139510782743446280540097 9854633087057584710405073)
                  ·
                    refine ⟨7390974815293188532803805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9854633087057584710405073 7390974815293188532803805)
                    ·
                      refine ⟨2771615555734945699801427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7390974815293188532803805 2771615555734945699801427)
                      ·
                        rfl

theorem cell23_5397702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5397702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397702 prefixEnd_5397702 := by exact prefixLift 5397702
  have htrace : WordTrace (prefixWord ++ tailWord_5397702) baseStart_5397702 baseEnd_5397702 := by
    simpa [prefixWord, tailWord_5397702, baseEnd_5397702] using wordTrace_append hprefix tailTrace_5397702
  have hstable : (prefixWord ++ tailWord_5397702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397702).length < 2 ^ (prefixWord ++ tailWord_5397702).sum := by decide
  have hdescent : baseEnd_5397702 < baseStart_5397702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397709 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5397709 : Nat := 118140960795 + 5397709 * 2 ^ 59
def prefixEnd_5397709 : Nat := 4983230072969 + 3 ^ 40 * 5397709 * 2
def baseEnd_5397709 : Nat := 923873050033175724137965

theorem tailTrace_5397709 : CollatzResearch.WordTrace tailWord_5397709 prefixEnd_5397709 923873050033175724137965 := by
  unfold tailWord_5397709
  simp only [CollatzResearch.WordTrace]
  refine ⟨196870620802029623149660181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131247080534686415433106787 196870620802029623149660181)
  ·
    refine ⟨9228310350095138585140321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 196870620802029623149660181 9228310350095138585140321)
    ·
      refine ⟨6921232762571353938855241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9228310350095138585140321 6921232762571353938855241)
      ·
        refine ⟨5190924571928515454141431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921232762571353938855241 5190924571928515454141431)
        ·
          refine ⟨7786386857892773181212147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190924571928515454141431 7786386857892773181212147)
          ·
            refine ⟨11679580286839159771818221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786386857892773181212147 11679580286839159771818221)
            ·
              refine ⟨4379842607564684914431833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11679580286839159771818221 4379842607564684914431833)
              ·
                refine ⟨3284881955673513685823875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379842607564684914431833 3284881955673513685823875)
                ·
                  refine ⟨4927322933510270528735813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284881955673513685823875 4927322933510270528735813)
                  ·
                    refine ⟨923873050033175724137965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927322933510270528735813 923873050033175724137965)
                    ·
                      rfl

theorem cell23_5397709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5397709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397709 prefixEnd_5397709 := by exact prefixLift 5397709
  have htrace : WordTrace (prefixWord ++ tailWord_5397709) baseStart_5397709 baseEnd_5397709 := by
    simpa [prefixWord, tailWord_5397709, baseEnd_5397709] using wordTrace_append hprefix tailTrace_5397709
  have hstable : (prefixWord ++ tailWord_5397709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397709).length < 2 ^ (prefixWord ++ tailWord_5397709).sum := by decide
  have hdescent : baseEnd_5397709 < baseStart_5397709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397727 : List Nat := [1, 1, 2, 3, 2, 1, 3, 10]
def baseStart_5397727 : Nat := 118140960795 + 5397727 * 2 ^ 59
def prefixEnd_5397727 : Nat := 4983230072969 + 3 ^ 40 * 5397727 * 2
def baseEnd_5397727 : Nat := 102652903435233633406993

theorem tailTrace_5397727 : CollatzResearch.WordTrace tailWord_5397727 prefixEnd_5397727 102652903435233633406993 := by
  unfold tailWord_5397727
  simp only [CollatzResearch.WordTrace]
  refine ⟨196871277315964412223815435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131247518210642941482543623 196871277315964412223815435)
  ·
    refine ⟨295306915973946618335723153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196871277315964412223815435 295306915973946618335723153)
    ·
      refine ⟨221480186980459963751792365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295306915973946618335723153 221480186980459963751792365)
      ·
        refine ⟨83055070117672486406922137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221480186980459963751792365 83055070117672486406922137)
        ·
          refine ⟨62291302588254364805191603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83055070117672486406922137 62291302588254364805191603)
          ·
            refine ⟨93436953882381547207787405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62291302588254364805191603 93436953882381547207787405)
            ·
              refine ⟨35038857705893080202920277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93436953882381547207787405 35038857705893080202920277)
              ·
                refine ⟨102652903435233633406993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35038857705893080202920277 102652903435233633406993)
                ·
                  rfl

theorem cell23_5397727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 10].length) (baseStart_5397727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397727 prefixEnd_5397727 := by exact prefixLift 5397727
  have htrace : WordTrace (prefixWord ++ tailWord_5397727) baseStart_5397727 baseEnd_5397727 := by
    simpa [prefixWord, tailWord_5397727, baseEnd_5397727] using wordTrace_append hprefix tailTrace_5397727
  have hstable : (prefixWord ++ tailWord_5397727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397727).length < 2 ^ (prefixWord ++ tailWord_5397727).sum := by decide
  have hdescent : baseEnd_5397727 < baseStart_5397727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397735 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 1, 5]
def baseStart_5397735 : Nat := 118140960795 + 5397735 * 2 ^ 59
def prefixEnd_5397735 : Nat := 4983230072969 + 3 ^ 40 * 5397735 * 2
def baseEnd_5397735 : Nat := 923877500198848023562925

theorem tailTrace_5397735 : CollatzResearch.WordTrace tailWord_5397735 prefixEnd_5397735 923877500198848023562925 := by
  unfold tailWord_5397735
  simp only [CollatzResearch.WordTrace]
  refine ⟨196871569099935429590106659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131247712733290286393404439 196871569099935429590106659)
  ·
    refine ⟨295307353649903144385159989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196871569099935429590106659 295307353649903144385159989)
    ·
      refine ⟨27685064404678419786108749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295307353649903144385159989 27685064404678419786108749)
      ·
        refine ⟨10381899151754407419790781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27685064404678419786108749 10381899151754407419790781)
        ·
          refine ⟨3893212181907902782421543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10381899151754407419790781 3893212181907902782421543)
          ·
            refine ⟨5839818272861854173632315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893212181907902782421543 5839818272861854173632315)
            ·
              refine ⟨8759727409292781260448473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839818272861854173632315 8759727409292781260448473)
              ·
                refine ⟨6569795556969585945336355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8759727409292781260448473 6569795556969585945336355)
                ·
                  refine ⟨9854693335454378918004533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569795556969585945336355 9854693335454378918004533)
                  ·
                    refine ⟨923877500198848023562925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9854693335454378918004533 923877500198848023562925)
                    ·
                      rfl

theorem cell23_5397735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_5397735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397735 prefixEnd_5397735 := by exact prefixLift 5397735
  have htrace : WordTrace (prefixWord ++ tailWord_5397735) baseStart_5397735 baseEnd_5397735 := by
    simpa [prefixWord, tailWord_5397735, baseEnd_5397735] using wordTrace_append hprefix tailTrace_5397735
  have hstable : (prefixWord ++ tailWord_5397735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397735).length < 2 ^ (prefixWord ++ tailWord_5397735).sum := by decide
  have hdescent : baseEnd_5397735 < baseStart_5397735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397738 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_5397738 : Nat := 118140960795 + 5397738 * 2 ^ 59
def prefixEnd_5397738 : Nat := 4983230072969 + 3 ^ 40 * 5397738 * 2
def baseEnd_5397738 : Nat := 2771634041038507558951261

theorem tailTrace_5397738 : CollatzResearch.WordTrace tailWord_5397738 prefixEnd_5397738 2771634041038507558951261 := by
  unfold tailWord_5397738
  simp only [CollatzResearch.WordTrace]
  refine ⟨49217919629731140275616467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131247785679283040734977245 49217919629731140275616467)
  ·
    refine ⟨73826879444596710413424701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49217919629731140275616467 73826879444596710413424701)
    ·
      refine ⟨27685079791723766405034263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73826879444596710413424701 27685079791723766405034263)
      ·
        refine ⟨41527619687585649607551395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27685079791723766405034263 41527619687585649607551395)
        ·
          refine ⟨62291429531378474411327093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41527619687585649607551395 62291429531378474411327093)
          ·
            refine ⟨5839821518566731976061915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62291429531378474411327093 5839821518566731976061915)
            ·
              refine ⟨8759732277850097964092873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839821518566731976061915 8759732277850097964092873)
              ·
                refine ⟨6569799208387573473069655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8759732277850097964092873 6569799208387573473069655)
                ·
                  refine ⟨9854698812581360209604483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6569799208387573473069655 9854698812581360209604483)
                  ·
                    refine ⟨14782048218872040314406725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9854698812581360209604483 14782048218872040314406725)
                    ·
                      refine ⟨2771634041038507558951261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14782048218872040314406725 2771634041038507558951261)
                      ·
                        rfl

theorem cell23_5397738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_5397738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397738 prefixEnd_5397738 := by exact prefixLift 5397738
  have htrace : WordTrace (prefixWord ++ tailWord_5397738) baseStart_5397738 baseEnd_5397738 := by
    simpa [prefixWord, tailWord_5397738, baseEnd_5397738] using wordTrace_append hprefix tailTrace_5397738
  have hstable : (prefixWord ++ tailWord_5397738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397738).length < 2 ^ (prefixWord ++ tailWord_5397738).sum := by decide
  have hdescent : baseEnd_5397738 < baseStart_5397738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397758 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_5397758 : Nat := 118140960795 + 5397758 * 2 ^ 59
def prefixEnd_5397758 : Nat := 4983230072969 + 3 ^ 40 * 5397758 * 2
def baseEnd_5397758 : Nat := 2771644310651597480701169

theorem tailTrace_5397758 : CollatzResearch.WordTrace tailWord_5397758 prefixEnd_5397758 2771644310651597480701169 := by
  unfold tailWord_5397758
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609050997356513064774241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131248271985901403012129285 24609050997356513064774241)
  ·
    refine ⟨18456788248017384798580681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24609050997356513064774241 18456788248017384798580681)
    ·
      refine ⟨13842591186013038598935511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18456788248017384798580681 13842591186013038598935511)
      ·
        refine ⟨20763886779019557898403267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13842591186013038598935511 20763886779019557898403267)
        ·
          refine ⟨31145830168529336847604901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20763886779019557898403267 31145830168529336847604901)
          ·
            refine ⟨5839843156599250658925919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31145830168529336847604901 5839843156599250658925919)
            ·
              refine ⟨8759764734898875988388879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839843156599250658925919 8759764734898875988388879)
              ·
                refine ⟨13139647102348313982583319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8759764734898875988388879 13139647102348313982583319)
                ·
                  refine ⟨19709470653522470973874979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13139647102348313982583319 19709470653522470973874979)
                  ·
                    refine ⟨29564205980283706460812469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19709470653522470973874979 29564205980283706460812469)
                    ·
                      refine ⟨2771644310651597480701169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29564205980283706460812469 2771644310651597480701169)
                      ·
                        rfl

theorem cell23_5397758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_5397758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397758 prefixEnd_5397758 := by exact prefixLift 5397758
  have htrace : WordTrace (prefixWord ++ tailWord_5397758) baseStart_5397758 baseEnd_5397758 := by
    simpa [prefixWord, tailWord_5397758, baseEnd_5397758] using wordTrace_append hprefix tailTrace_5397758
  have hstable : (prefixWord ++ tailWord_5397758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397758).length < 2 ^ (prefixWord ++ tailWord_5397758).sum := by decide
  have hdescent : baseEnd_5397758 < baseStart_5397758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397772 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_5397772 : Nat := 118140960795 + 5397772 * 2 ^ 59
def prefixEnd_5397772 : Nat := 4983230072969 + 3 ^ 40 * 5397772 * 2
def baseEnd_5397772 : Nat := 2771651499380760425926105

theorem tailTrace_5397772 : CollatzResearch.WordTrace tailWord_5397772 prefixEnd_5397772 2771651499380760425926105 := by
  unfold tailWord_5397772
  simp only [CollatzResearch.WordTrace]
  refine ⟨98436459300400692454601785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131248612400534256606135713 98436459300400692454601785)
  ·
    refine ⟨73827344475300519340951339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98436459300400692454601785 73827344475300519340951339)
    ·
      refine ⟨110741016712950779011427009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73827344475300519340951339 110741016712950779011427009)
      ·
        refine ⟨83055762534713084258570257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110741016712950779011427009 83055762534713084258570257)
        ·
          refine ⟨62291821901034813193927693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83055762534713084258570257 62291821901034813193927693)
          ·
            refine ⟨23359433212888054947722885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62291821901034813193927693 23359433212888054947722885)
            ·
              refine ⟨4379893727416510302698041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23359433212888054947722885 4379893727416510302698041)
              ·
                refine ⟨3284920295562382727023531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379893727416510302698041 3284920295562382727023531)
                ·
                  refine ⟨4927380443343574090535297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284920295562382727023531 4927380443343574090535297)
                  ·
                    refine ⟨3695535332507680567901473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927380443343574090535297 3695535332507680567901473)
                    ·
                      refine ⟨2771651499380760425926105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695535332507680567901473 2771651499380760425926105)
                      ·
                        rfl

theorem cell23_5397772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_5397772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397772 prefixEnd_5397772 := by exact prefixLift 5397772
  have htrace : WordTrace (prefixWord ++ tailWord_5397772) baseStart_5397772 baseEnd_5397772 := by
    simpa [prefixWord, tailWord_5397772, baseEnd_5397772] using wordTrace_append hprefix tailTrace_5397772
  have hstable : (prefixWord ++ tailWord_5397772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397772).length < 2 ^ (prefixWord ++ tailWord_5397772).sum := by decide
  have hdescent : baseEnd_5397772 < baseStart_5397772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397774 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5397774 : Nat := 118140960795 + 5397774 * 2 ^ 59
def prefixEnd_5397774 : Nat := 4983230072969 + 3 ^ 40 * 5397774 * 2
def baseEnd_5397774 : Nat := 923884175447356472700365

theorem tailTrace_5397774 : CollatzResearch.WordTrace tailWord_5397774 prefixEnd_5397774 923884175447356472700365 := by
  unfold tailWord_5397774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609123943349267406347047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131248661031196092833850917 24609123943349267406347047)
  ·
    refine ⟨36913685915023901109520571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24609123943349267406347047 36913685915023901109520571)
    ·
      refine ⟨55370528872535851664280857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36913685915023901109520571 55370528872535851664280857)
      ·
        refine ⟨41527896654401888748210643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55370528872535851664280857 41527896654401888748210643)
        ·
          refine ⟨62291844981602833122315965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41527896654401888748210643 62291844981602833122315965)
          ·
            refine ⟨23359441868101062420868487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62291844981602833122315965 23359441868101062420868487)
            ·
              refine ⟨35039162802151593631302731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23359441868101062420868487 35039162802151593631302731)
              ·
                refine ⟨52558744203227390446954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35039162802151593631302731 52558744203227390446954097)
                ·
                  refine ⟨39419058152420542835215573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52558744203227390446954097 39419058152420542835215573)
                  ·
                    refine ⟨923884175447356472700365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39419058152420542835215573 923884175447356472700365)
                    ·
                      rfl

theorem cell23_5397774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5397774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397774 prefixEnd_5397774 := by exact prefixLift 5397774
  have htrace : WordTrace (prefixWord ++ tailWord_5397774) baseStart_5397774 baseEnd_5397774 := by
    simpa [prefixWord, tailWord_5397774, baseEnd_5397774] using wordTrace_append hprefix tailTrace_5397774
  have hstable : (prefixWord ++ tailWord_5397774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397774).length < 2 ^ (prefixWord ++ tailWord_5397774).sum := by decide
  have hdescent : baseEnd_5397774 < baseStart_5397774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397788 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5397788 : Nat := 118140960795 + 5397788 * 2 ^ 59
def prefixEnd_5397788 : Nat := 4983230072969 + 3 ^ 40 * 5397788 * 2
def baseEnd_5397788 : Nat := 2771659715071232363326031

theorem tailTrace_5397788 : CollatzResearch.WordTrace tailWord_5397788 prefixEnd_5397788 2771659715071232363326031 := by
  unfold tailWord_5397788
  simp only [CollatzResearch.WordTrace]
  refine ⟨98436751084371709820893009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131249001445828946427857345 98436751084371709820893009)
  ·
    refine ⟨73827563313278782365669757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98436751084371709820893009 73827563313278782365669757)
    ·
      refine ⟨27685336242479543387126159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73827563313278782365669757 27685336242479543387126159)
      ·
        refine ⟨41528004363719315080689239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27685336242479543387126159 41528004363719315080689239)
        ·
          refine ⟨62292006545578972621033859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41528004363719315080689239 62292006545578972621033859)
          ·
            refine ⟨93438009818368458931550789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62292006545578972621033859 93438009818368458931550789)
            ·
              refine ⟨17519626840944086049665773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93438009818368458931550789 17519626840944086049665773)
              ·
                refine ⟨6569860065354032268624665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17519626840944086049665773 6569860065354032268624665)
                ·
                  refine ⟨4927395049015524201468499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6569860065354032268624665 4927395049015524201468499)
                  ·
                    refine ⟨7391092573523286302202749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4927395049015524201468499 7391092573523286302202749)
                    ·
                      refine ⟨2771659715071232363326031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391092573523286302202749 2771659715071232363326031)
                      ·
                        rfl

theorem cell23_5397788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5397788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397788 prefixEnd_5397788 := by exact prefixLift 5397788
  have htrace : WordTrace (prefixWord ++ tailWord_5397788) baseStart_5397788 baseEnd_5397788 := by
    simpa [prefixWord, tailWord_5397788, baseEnd_5397788] using wordTrace_append hprefix tailTrace_5397788
  have hstable : (prefixWord ++ tailWord_5397788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397788).length < 2 ^ (prefixWord ++ tailWord_5397788).sum := by decide
  have hdescent : baseEnd_5397788 < baseStart_5397788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397824 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_5397824 : Nat := 118140960795 + 5397824 * 2 ^ 59
def prefixEnd_5397824 : Nat := 4983230072969 + 3 ^ 40 * 5397824 * 2
def baseEnd_5397824 : Nat := 2771678200374794222475865

theorem tailTrace_5397824 : CollatzResearch.WordTrace tailWord_5397824 prefixEnd_5397824 2771678200374794222475865 := by
  unfold tailWord_5397824
  simp only [CollatzResearch.WordTrace]
  refine ⟨98437407598306498895048263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131249876797741998526731017 98437407598306498895048263)
  ·
    refine ⟨147656111397459748342572395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98437407598306498895048263 147656111397459748342572395)
    ·
      refine ⟨221484167096189622513858593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147656111397459748342572395 221484167096189622513858593)
      ·
        refine ⟨166113125322142216885393945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221484167096189622513858593 166113125322142216885393945)
        ·
          refine ⟨124584843991606662664045459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166113125322142216885393945 124584843991606662664045459)
          ·
            refine ⟨186877265987409993996068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124584843991606662664045459 186877265987409993996068189)
            ·
              refine ⟨70078974745278747748525571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186877265987409993996068189 70078974745278747748525571)
              ·
                refine ⟨105118462117918121622788357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70078974745278747748525571 105118462117918121622788357)
                ·
                  refine ⟨19709711647109647804272817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105118462117918121622788357 19709711647109647804272817)
                  ·
                    refine ⟨14782283735332235853204613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19709711647109647804272817 14782283735332235853204613)
                    ·
                      refine ⟨2771678200374794222475865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14782283735332235853204613 2771678200374794222475865)
                      ·
                        rfl

theorem cell23_5397824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_5397824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397824 prefixEnd_5397824 := by exact prefixLift 5397824
  have htrace : WordTrace (prefixWord ++ tailWord_5397824) baseStart_5397824 baseEnd_5397824 := by
    simpa [prefixWord, tailWord_5397824, baseEnd_5397824] using wordTrace_append hprefix tailTrace_5397824
  have hstable : (prefixWord ++ tailWord_5397824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397824).length < 2 ^ (prefixWord ++ tailWord_5397824).sum := by decide
  have hdescent : baseEnd_5397824 < baseStart_5397824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397845 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5397845 : Nat := 118140960795 + 5397845 * 2 ^ 59
def prefixEnd_5397845 : Nat := 4983230072969 + 3 ^ 40 * 5397845 * 2
def baseEnd_5397845 : Nat := 2771688983468538640313269

theorem tailTrace_5397845 : CollatzResearch.WordTrace tailWord_5397845 prefixEnd_5397845 2771688983468538640313269 := by
  unfold tailWord_5397845
  simp only [CollatzResearch.WordTrace]
  refine ⟨196875581129536918376610989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131250387419691278917740659 196875581129536918376610989)
  ·
    refine ⟨73828342923576344391229121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196875581129536918376610989 73828342923576344391229121)
    ·
      refine ⟨55371257192682258293421841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73828342923576344391229121 55371257192682258293421841)
      ·
        refine ⟨41528442894511693720066381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55371257192682258293421841 41528442894511693720066381)
        ·
          refine ⟨15573166085441885145024893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41528442894511693720066381 15573166085441885145024893)
          ·
            refine ⟨5839937282040706929384335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15573166085441885145024893 5839937282040706929384335)
            ·
              refine ⟨8759905923061060394076503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839937282040706929384335 8759905923061060394076503)
              ·
                refine ⟨13139858884591590591114755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8759905923061060394076503 13139858884591590591114755)
                ·
                  refine ⟨19709788326887385886672133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13139858884591590591114755 19709788326887385886672133)
                  ·
                    refine ⟨3695585311291384853751025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19709788326887385886672133 3695585311291384853751025)
                    ·
                      refine ⟨2771688983468538640313269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695585311291384853751025 2771688983468538640313269)
                      ·
                        rfl

theorem cell23_5397845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5397845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397845 prefixEnd_5397845 := by exact prefixLift 5397845
  have htrace : WordTrace (prefixWord ++ tailWord_5397845) baseStart_5397845 baseEnd_5397845 := by
    simpa [prefixWord, tailWord_5397845, baseEnd_5397845] using wordTrace_append hprefix tailTrace_5397845
  have hstable : (prefixWord ++ tailWord_5397845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397845).length < 2 ^ (prefixWord ++ tailWord_5397845).sum := by decide
  have hdescent : baseEnd_5397845 < baseStart_5397845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397868 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 5]
def baseStart_5397868 : Nat := 118140960795 + 5397868 * 2 ^ 59
def prefixEnd_5397868 : Nat := 4983230072969 + 3 ^ 40 * 5397868 * 2
def baseEnd_5397868 : Nat := 307966754835954672258407

theorem tailTrace_5397868 : CollatzResearch.WordTrace tailWord_5397868 prefixEnd_5397868 307966754835954672258407 := by
  unfold tailWord_5397868
  simp only [CollatzResearch.WordTrace]
  refine ⟨98438210004226796652349129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131250946672302395536465505 98438210004226796652349129)
  ·
    refine ⟨73828657503170097489261847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98438210004226796652349129 73828657503170097489261847)
    ·
      refine ⟨110742986254755146233892771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73828657503170097489261847 110742986254755146233892771)
      ·
        refine ⟨166114479382132719350839157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110742986254755146233892771 166114479382132719350839157)
        ·
          refine ⟨15573232442074942439141171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166114479382132719350839157 15573232442074942439141171)
          ·
            refine ⟨23359848663112413658711757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15573232442074942439141171 23359848663112413658711757)
            ·
              refine ⟨8759943248667155122016909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23359848663112413658711757 8759943248667155122016909)
              ·
                refine ⟨3284978718250183170756341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8759943248667155122016909 3284978718250183170756341)
                ·
                  refine ⟨307966754835954672258407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284978718250183170756341 307966754835954672258407)
                  ·
                    rfl

theorem cell23_5397868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_5397868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397868 prefixEnd_5397868 := by exact prefixLift 5397868
  have htrace : WordTrace (prefixWord ++ tailWord_5397868) baseStart_5397868 baseEnd_5397868 := by
    simpa [prefixWord, tailWord_5397868, baseEnd_5397868] using wordTrace_append hprefix tailTrace_5397868
  have hstable : (prefixWord ++ tailWord_5397868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397868).length < 2 ^ (prefixWord ++ tailWord_5397868).sum := by decide
  have hdescent : baseEnd_5397868 < baseStart_5397868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397891 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_5397891 : Nat := 118140960795 + 5397891 * 2 ^ 59
def prefixEnd_5397891 : Nat := 4983230072969 + 3 ^ 40 * 5397891 * 2
def baseEnd_5397891 : Nat := 2771712603578645460338057

theorem tailTrace_5397891 : CollatzResearch.WordTrace tailWord_5397891 prefixEnd_5397891 2771712603578645460338057 := by
  unfold tailWord_5397891
  simp only [CollatzResearch.WordTrace]
  refine ⟨196877258887370268232785527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131251505924913512155190351 196877258887370268232785527)
  ·
    refine ⟨295315888331055402349178291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196877258887370268232785527 295315888331055402349178291)
    ·
      refine ⟨442973832496583103523767437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295315888331055402349178291 442973832496583103523767437)
      ·
        refine ⟨166115187186218663821412789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 442973832496583103523767437 166115187186218663821412789)
        ·
          refine ⟨15573298798707999733257449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166115187186218663821412789 15573298798707999733257449)
          ·
            refine ⟨11679974099030999799943087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15573298798707999733257449 11679974099030999799943087)
            ·
              refine ⟨17519961148546499699914631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11679974099030999799943087 17519961148546499699914631)
              ·
                refine ⟨26279941722819749549871947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17519961148546499699914631 26279941722819749549871947)
                ·
                  refine ⟨39419912584229624324807921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26279941722819749549871947 39419912584229624324807921)
                  ·
                    refine ⟨29564934438172218243605941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39419912584229624324807921 29564934438172218243605941)
                    ·
                      refine ⟨2771712603578645460338057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29564934438172218243605941 2771712603578645460338057)
                      ·
                        rfl

theorem cell23_5397891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_5397891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397891 prefixEnd_5397891 := by exact prefixLift 5397891
  have htrace : WordTrace (prefixWord ++ tailWord_5397891) baseStart_5397891 baseEnd_5397891 := by
    simpa [prefixWord, tailWord_5397891, baseEnd_5397891] using wordTrace_append hprefix tailTrace_5397891
  have hstable : (prefixWord ++ tailWord_5397891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397891).length < 2 ^ (prefixWord ++ tailWord_5397891).sum := by decide
  have hdescent : baseEnd_5397891 < baseStart_5397891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397911 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 5, 4]
def baseStart_5397911 : Nat := 118140960795 + 5397911 * 2 ^ 59
def prefixEnd_5397911 : Nat := 4983230072969 + 3 ^ 40 * 5397911 * 2
def baseEnd_5397911 : Nat := 923907624397245127362655

theorem tailTrace_5397911 : CollatzResearch.WordTrace tailWord_5397911 prefixEnd_5397911 923907624397245127362655 := by
  unfold tailWord_5397911
  simp only [CollatzResearch.WordTrace]
  refine ⟨196877988347297811648513587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131251992231531874432342391 196877988347297811648513587)
  ·
    refine ⟨295316982520946717472770381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196877988347297811648513587 295316982520946717472770381)
    ·
      refine ⟨110743868445355019052288893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295316982520946717472770381 110743868445355019052288893)
      ·
        refine ⟨41528950667008132144608335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110743868445355019052288893 41528950667008132144608335)
        ·
          refine ⟨62293426000512198216912503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41528950667008132144608335 62293426000512198216912503)
          ·
            refine ⟨93440139000768297325368755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62293426000512198216912503 93440139000768297325368755)
            ·
              refine ⟨140160208501152445988053133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93440139000768297325368755 140160208501152445988053133)
              ·
                refine ⟨52560078187932167245519925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140160208501152445988053133 52560078187932167245519925)
                ·
                  refine ⟨4927507330118640679267493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52560078187932167245519925 4927507330118640679267493)
                  ·
                    refine ⟨923907624397245127362655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927507330118640679267493 923907624397245127362655)
                    ·
                      rfl

theorem cell23_5397911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_5397911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397911 prefixEnd_5397911 := by exact prefixLift 5397911
  have htrace : WordTrace (prefixWord ++ tailWord_5397911) baseStart_5397911 baseEnd_5397911 := by
    simpa [prefixWord, tailWord_5397911, baseEnd_5397911] using wordTrace_append hprefix tailTrace_5397911
  have hstable : (prefixWord ++ tailWord_5397911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397911).length < 2 ^ (prefixWord ++ tailWord_5397911).sum := by decide
  have hdescent : baseEnd_5397911 < baseStart_5397911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397968 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_5397968 : Nat := 118140960795 + 5397968 * 2 ^ 59
def prefixEnd_5397968 : Nat := 4983230072969 + 3 ^ 40 * 5397968 * 2
def baseEnd_5397968 : Nat := 2771752141589041659075203

theorem tailTrace_5397968 : CollatzResearch.WordTrace tailWord_5397968 prefixEnd_5397968 2771752141589041659075203 := by
  unfold tailWord_5397968
  simp only [CollatzResearch.WordTrace]
  refine ⟨98440033654045655191669279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131253378205394206922225705 98440033654045655191669279)
  ·
    refine ⟨147660050481068482787503919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98440033654045655191669279 147660050481068482787503919)
    ·
      refine ⟨221490075721602724181255879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147660050481068482787503919 221490075721602724181255879)
      ·
        refine ⟨332235113582404086271883819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221490075721602724181255879 332235113582404086271883819)
        ·
          refine ⟨498352670373606129407825729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332235113582404086271883819 498352670373606129407825729)
          ·
            refine ⟨373764502780204597055869297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498352670373606129407825729 373764502780204597055869297)
            ·
              refine ⟨280323377085153447791901973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373764502780204597055869297 280323377085153447791901973)
              ·
                refine ⟨13140158300866567865245405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280323377085153447791901973 13140158300866567865245405)
                ·
                  refine ⟨4927559362824962949467027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13140158300866567865245405 4927559362824962949467027)
                  ·
                    refine ⟨7391339044237444424200541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4927559362824962949467027 7391339044237444424200541)
                    ·
                      refine ⟨2771752141589041659075203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391339044237444424200541 2771752141589041659075203)
                      ·
                        rfl

theorem cell23_5397968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_5397968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397968 prefixEnd_5397968 := by exact prefixLift 5397968
  have htrace : WordTrace (prefixWord ++ tailWord_5397968) baseStart_5397968 baseEnd_5397968 := by
    simpa [prefixWord, tailWord_5397968, baseEnd_5397968] using wordTrace_append hprefix tailTrace_5397968
  have hstable : (prefixWord ++ tailWord_5397968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397968).length < 2 ^ (prefixWord ++ tailWord_5397968).sum := by decide
  have hdescent : baseEnd_5397968 < baseStart_5397968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5397972 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5397972 : Nat := 118140960795 + 5397972 * 2 ^ 59
def prefixEnd_5397972 : Nat := 4983230072969 + 3 ^ 40 * 5397972 * 2
def baseEnd_5397972 : Nat := 2771754195511659643425185

theorem tailTrace_5397972 : CollatzResearch.WordTrace tailWord_5397972 prefixEnd_5397972 2771754195511659643425185 := by
  unfold tailWord_5397972
  simp only [CollatzResearch.WordTrace]
  refine ⟨98440106600038409533242085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131253475466717879377656113 98440106600038409533242085)
  ·
    refine ⟨18457519987507201787482891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98440106600038409533242085 18457519987507201787482891)
    ·
      refine ⟨27686279981260802681224337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18457519987507201787482891 27686279981260802681224337)
      ·
        refine ⟨20764709985945602010918253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27686279981260802681224337 20764709985945602010918253)
        ·
          refine ⟨7786766244729600754094345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20764709985945602010918253 7786766244729600754094345)
          ·
            refine ⟨5840074683547200565570759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7786766244729600754094345 5840074683547200565570759)
            ·
              refine ⟨8760112025320800848356139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840074683547200565570759 8760112025320800848356139)
              ·
                refine ⟨13140168037981201272534209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760112025320800848356139 13140168037981201272534209)
                ·
                  refine ⟨9855126028485900954400657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13140168037981201272534209 9855126028485900954400657)
                  ·
                    refine ⟨7391344521364425715800493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9855126028485900954400657 7391344521364425715800493)
                    ·
                      refine ⟨2771754195511659643425185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391344521364425715800493 2771754195511659643425185)
                      ·
                        rfl

theorem cell23_5397972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5397972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5397972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5397972 prefixEnd_5397972 := by exact prefixLift 5397972
  have htrace : WordTrace (prefixWord ++ tailWord_5397972) baseStart_5397972 baseEnd_5397972 := by
    simpa [prefixWord, tailWord_5397972, baseEnd_5397972] using wordTrace_append hprefix tailTrace_5397972
  have hstable : (prefixWord ++ tailWord_5397972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5397972).length < 2 ^ (prefixWord ++ tailWord_5397972).sum := by decide
  have hdescent : baseEnd_5397972 < baseStart_5397972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5397972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398002 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5398002 : Nat := 118140960795 + 5398002 * 2 ^ 59
def prefixEnd_5398002 : Nat := 4983230072969 + 3 ^ 40 * 5398002 * 2
def baseEnd_5398002 : Nat := 2771769599931294526050047

theorem tailTrace_5398002 : CollatzResearch.WordTrace tailWord_5398002 prefixEnd_5398002 2771769599931294526050047 := by
  unfold tailWord_5398002
  simp only [CollatzResearch.WordTrace]
  refine ⟨49220326847492033547519065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131254204926645422793384173 49220326847492033547519065)
  ·
    refine ⟨36915245135619025160639299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49220326847492033547519065 36915245135619025160639299)
    ·
      refine ⟨55372867703428537740958949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36915245135619025160639299 55372867703428537740958949)
      ·
        refine ⟨10382412694392850826429803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55372867703428537740958949 10382412694392850826429803)
        ·
          refine ⟨15573619041589276239644705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10382412694392850826429803 15573619041589276239644705)
          ·
            refine ⟨11680214281191957179733529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15573619041589276239644705 11680214281191957179733529)
            ·
              refine ⟨8760160710893967884800147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11680214281191957179733529 8760160710893967884800147)
              ·
                refine ⟨13140241066340951827200221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760160710893967884800147 13140241066340951827200221)
                ·
                  refine ⟨4927590399877856935200083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13140241066340951827200221 4927590399877856935200083)
                  ·
                    refine ⟨7391385599816785402800125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4927590399877856935200083 7391385599816785402800125)
                    ·
                      refine ⟨2771769599931294526050047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391385599816785402800125 2771769599931294526050047)
                      ·
                        rfl

theorem cell23_5398002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5398002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398002 prefixEnd_5398002 := by exact prefixLift 5398002
  have htrace : WordTrace (prefixWord ++ tailWord_5398002) baseStart_5398002 baseEnd_5398002 := by
    simpa [prefixWord, tailWord_5398002, baseEnd_5398002] using wordTrace_append hprefix tailTrace_5398002
  have hstable : (prefixWord ++ tailWord_5398002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398002).length < 2 ^ (prefixWord ++ tailWord_5398002).sum := by decide
  have hdescent : baseEnd_5398002 < baseStart_5398002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_5398011 : Nat := 118140960795 + 5398011 * 2 ^ 59
def prefixEnd_5398011 : Nat := 4983230072969 + 3 ^ 40 * 5398011 * 2
def baseEnd_5398011 : Nat := 2771774221257184990837505

theorem tailTrace_5398011 : CollatzResearch.WordTrace tailWord_5398011 prefixEnd_5398011 2771774221257184990837505 := by
  unfold tailWord_5398011
  simp only [CollatzResearch.WordTrace]
  refine ⟨196881635646935528727153887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131254423764623685818102591 196881635646935528727153887)
  ·
    refine ⟨295322453470403293090730831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196881635646935528727153887 295322453470403293090730831)
    ·
      refine ⟨442983680205604939636096247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295322453470403293090730831 442983680205604939636096247)
      ·
        refine ⟨664475520308407409454144371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442983680205604939636096247 664475520308407409454144371)
        ·
          refine ⟨996713280462611114181216557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664475520308407409454144371 996713280462611114181216557)
          ·
            refine ⟨373767480173479167817956209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996713280462611114181216557 373767480173479167817956209)
            ·
              refine ⟨280325610130109375863467157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373767480173479167817956209 280325610130109375863467157)
              ·
                refine ⟨13140262974848876993600023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280325610130109375863467157 13140262974848876993600023)
                ·
                  refine ⟨19710394462273315490400035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13140262974848876993600023 19710394462273315490400035)
                  ·
                    refine ⟨29565591693409973235600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19710394462273315490400035 29565591693409973235600053)
                    ·
                      refine ⟨2771774221257184990837505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29565591693409973235600053 2771774221257184990837505)
                      ·
                        rfl

theorem cell23_5398011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_5398011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398011 prefixEnd_5398011 := by exact prefixLift 5398011
  have htrace : WordTrace (prefixWord ++ tailWord_5398011) baseStart_5398011 baseEnd_5398011 := by
    simpa [prefixWord, tailWord_5398011, baseEnd_5398011] using wordTrace_append hprefix tailTrace_5398011
  have hstable : (prefixWord ++ tailWord_5398011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398011).length < 2 ^ (prefixWord ++ tailWord_5398011).sum := by decide
  have hdescent : baseEnd_5398011 < baseStart_5398011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398025 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 3, 2, 2]
def baseStart_5398025 : Nat := 118140960795 + 5398025 * 2 ^ 59
def prefixEnd_5398025 : Nat := 4983230072969 + 3 ^ 40 * 5398025 * 2
def baseEnd_5398025 : Nat := 2771781409986347936062441

theorem tailTrace_5398025 : CollatzResearch.WordTrace tailWord_5398025 prefixEnd_5398025 2771781409986347936062441 := by
  unfold tailWord_5398025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196882146268884809118163529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131254764179256539412109019 196882146268884809118163529)
  ·
    refine ⟨147661609701663606838622647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196882146268884809118163529 147661609701663606838622647)
    ·
      refine ⟨221492414552495410257933971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147661609701663606838622647 221492414552495410257933971)
      ·
        refine ⟨332238621828743115386900957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221492414552495410257933971 332238621828743115386900957)
        ·
          refine ⟨124589483185778668270087859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332238621828743115386900957 124589483185778668270087859)
          ·
            refine ⟨186884224778668002405131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124589483185778668270087859 186884224778668002405131789)
            ·
              refine ⟨70081584292000500901924421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186884224778668002405131789 70081584292000500901924421)
              ·
                refine ⟨13140297054750093919110829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70081584292000500901924421 13140297054750093919110829)
                ·
                  refine ⟨4927611395531285219666561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13140297054750093919110829 4927611395531285219666561)
                  ·
                    refine ⟨3695708546648463914749921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4927611395531285219666561 3695708546648463914749921)
                    ·
                      refine ⟨2771781409986347936062441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695708546648463914749921 2771781409986347936062441)
                      ·
                        rfl

theorem cell23_5398025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2, 2].length) (baseStart_5398025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398025 prefixEnd_5398025 := by exact prefixLift 5398025
  have htrace : WordTrace (prefixWord ++ tailWord_5398025) baseStart_5398025 baseEnd_5398025 := by
    simpa [prefixWord, tailWord_5398025, baseEnd_5398025] using wordTrace_append hprefix tailTrace_5398025
  have hstable : (prefixWord ++ tailWord_5398025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398025).length < 2 ^ (prefixWord ++ tailWord_5398025).sum := by decide
  have hdescent : baseEnd_5398025 < baseStart_5398025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398045 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_5398045 : Nat := 118140960795 + 5398045 * 2 ^ 59
def prefixEnd_5398045 : Nat := 4983230072969 + 3 ^ 40 * 5398045 * 2
def baseEnd_5398045 : Nat := 2771791679599437857812349

theorem tailTrace_5398045 : CollatzResearch.WordTrace tailWord_5398045 prefixEnd_5398045 2771791679599437857812349 := by
  unfold tailWord_5398045
  simp only [CollatzResearch.WordTrace]
  refine ⟨196882875728812352533891589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131255250485874901689261059 196882875728812352533891589)
  ·
    refine ⟨36915539199152316100104673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196882875728812352533891589 36915539199152316100104673)
    ·
      refine ⟨27686654399364237075078505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36915539199152316100104673 27686654399364237075078505)
      ·
        refine ⟨20764990799523177806308879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27686654399364237075078505 20764990799523177806308879)
        ·
          refine ⟨31147486199284766709463319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20764990799523177806308879 31147486199284766709463319)
          ·
            refine ⟨46721229298927150064194979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31147486199284766709463319 46721229298927150064194979)
            ·
              refine ⟨70081843948390725096292469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46721229298927150064194979 70081843948390725096292469)
              ·
                refine ⟨6570172870161630477777419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70081843948390725096292469 6570172870161630477777419)
                ·
                  refine ⟨9855259305242445716666129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6570172870161630477777419 9855259305242445716666129)
                  ·
                    refine ⟨7391444478931834287499597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9855259305242445716666129 7391444478931834287499597)
                    ·
                      refine ⟨2771791679599437857812349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391444478931834287499597 2771791679599437857812349)
                      ·
                        rfl

theorem cell23_5398045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_5398045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398045 prefixEnd_5398045 := by exact prefixLift 5398045
  have htrace : WordTrace (prefixWord ++ tailWord_5398045) baseStart_5398045 baseEnd_5398045 := by
    simpa [prefixWord, tailWord_5398045, baseEnd_5398045] using wordTrace_append hprefix tailTrace_5398045
  have hstable : (prefixWord ++ tailWord_5398045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398045).length < 2 ^ (prefixWord ++ tailWord_5398045).sum := by decide
  have hdescent : baseEnd_5398045 < baseStart_5398045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398048 : List Nat := [2, 1, 1, 6, 1, 3, 9]
def baseStart_5398048 : Nat := 118140960795 + 5398048 * 2 ^ 59
def prefixEnd_5398048 : Nat := 4983230072969 + 3 ^ 40 * 5398048 * 2
def baseEnd_5398048 : Nat := 34219669383227177112035

theorem tailTrace_5398048 : CollatzResearch.WordTrace tailWord_5398048 prefixEnd_5398048 34219669383227177112035 := by
  unfold tailWord_5398048
  simp only [CollatzResearch.WordTrace]
  refine ⟨98441492573900742023125399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131255323431867656030833865 98441492573900742023125399)
  ·
    refine ⟨147662238860851113034688099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98441492573900742023125399 147662238860851113034688099)
    ·
      refine ⟨221493358291276669552032149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147662238860851113034688099 221493358291276669552032149)
      ·
        refine ⟨10382501169903593885251507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221493358291276669552032149 10382501169903593885251507)
        ·
          refine ⟨15573751754855390827877261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10382501169903593885251507 15573751754855390827877261)
          ·
            refine ⟨5840156908070771560453973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15573751754855390827877261 5840156908070771560453973)
            ·
              refine ⟨34219669383227177112035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5840156908070771560453973 34219669383227177112035)
              ·
                rfl

theorem cell23_5398048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 9].length) (baseStart_5398048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398048 prefixEnd_5398048 := by exact prefixLift 5398048
  have htrace : WordTrace (prefixWord ++ tailWord_5398048) baseStart_5398048 baseEnd_5398048 := by
    simpa [prefixWord, tailWord_5398048, baseEnd_5398048] using wordTrace_append hprefix tailTrace_5398048
  have hstable : (prefixWord ++ tailWord_5398048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398048).length < 2 ^ (prefixWord ++ tailWord_5398048).sum := by decide
  have hdescent : baseEnd_5398048 < baseStart_5398048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398085 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 3, 3, 2]
def baseStart_5398085 : Nat := 118140960795 + 5398085 * 2 ^ 59
def prefixEnd_5398085 : Nat := 4983230072969 + 3 ^ 40 * 5398085 * 2
def baseEnd_5398085 : Nat := 2771812218825617701312165

theorem tailTrace_5398085 : CollatzResearch.WordTrace tailWord_5398085 prefixEnd_5398085 2771812218825617701312165 := by
  unfold tailWord_5398085
  simp only [CollatzResearch.WordTrace]
  refine ⟨196884334648667439365347709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131256223099111626243565139 196884334648667439365347709)
  ·
    refine ⟨73831625493250289762005391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196884334648667439365347709 73831625493250289762005391)
    ·
      refine ⟨110747438239875434643008087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73831625493250289762005391 110747438239875434643008087)
      ·
        refine ⟨166121157359813151964512131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110747438239875434643008087 166121157359813151964512131)
        ·
          refine ⟨249181736039719727946768197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166121157359813151964512131 249181736039719727946768197)
          ·
            refine ⟨46721575507447448990019037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249181736039719727946768197 46721575507447448990019037)
            ·
              refine ⟨17520590815292793371257139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46721575507447448990019037 17520590815292793371257139)
              ·
                refine ⟨26280886222939190056885709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17520590815292793371257139 26280886222939190056885709)
                ·
                  refine ⟨9855332333602196271332141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26280886222939190056885709 9855332333602196271332141)
                  ·
                    refine ⟨3695749625100823601749553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9855332333602196271332141 3695749625100823601749553)
                    ·
                      refine ⟨2771812218825617701312165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3695749625100823601749553 2771812218825617701312165)
                      ·
                        rfl

theorem cell23_5398085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_5398085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398085 prefixEnd_5398085 := by exact prefixLift 5398085
  have htrace : WordTrace (prefixWord ++ tailWord_5398085) baseStart_5398085 baseEnd_5398085 := by
    simpa [prefixWord, tailWord_5398085, baseEnd_5398085] using wordTrace_append hprefix tailTrace_5398085
  have hstable : (prefixWord ++ tailWord_5398085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398085).length < 2 ^ (prefixWord ++ tailWord_5398085).sum := by decide
  have hdescent : baseEnd_5398085 < baseStart_5398085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398091 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 6]
def baseStart_5398091 : Nat := 118140960795 + 5398091 * 2 ^ 59
def prefixEnd_5398091 : Nat := 4983230072969 + 3 ^ 40 * 5398091 * 2
def baseEnd_5398091 : Nat := 923938433236514892612379

theorem tailTrace_5398091 : CollatzResearch.WordTrace tailWord_5398091 prefixEnd_5398091 923938433236514892612379 := by
  unfold tailWord_5398091
  simp only [CollatzResearch.WordTrace]
  refine ⟨196884553486645702390066127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131256368991097134926710751 196884553486645702390066127)
  ·
    refine ⟨295326830229968553585099191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196884553486645702390066127 295326830229968553585099191)
    ·
      refine ⟨442990245344952830377648787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295326830229968553585099191 442990245344952830377648787)
      ·
        refine ⟨664485368017429245566473181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442990245344952830377648787 664485368017429245566473181)
        ·
          refine ⟨249182013006535967087427443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664485368017429245566473181 249182013006535967087427443)
          ·
            refine ⟨373773019509803950631141165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249182013006535967087427443 373773019509803950631141165)
            ·
              refine ⟨140164882316176481486677937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373773019509803950631141165 140164882316176481486677937)
              ·
                refine ⟨105123661737132361115008453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140164882316176481486677937 105123661737132361115008453)
                ·
                  refine ⟨19710686575712317709064085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105123661737132361115008453 19710686575712317709064085)
                  ·
                    refine ⟨923938433236514892612379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19710686575712317709064085 923938433236514892612379)
                    ·
                      rfl

theorem cell23_5398091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_5398091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398091 prefixEnd_5398091 := by exact prefixLift 5398091
  have htrace : WordTrace (prefixWord ++ tailWord_5398091) baseStart_5398091 baseEnd_5398091 := by
    simpa [prefixWord, tailWord_5398091, baseEnd_5398091] using wordTrace_append hprefix tailTrace_5398091
  have hstable : (prefixWord ++ tailWord_5398091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398091).length < 2 ^ (prefixWord ++ tailWord_5398091).sum := by decide
  have hdescent : baseEnd_5398091 < baseStart_5398091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398111 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_5398111 : Nat := 118140960795 + 5398111 * 2 ^ 59
def prefixEnd_5398111 : Nat := 4983230072969 + 3 ^ 40 * 5398111 * 2
def baseEnd_5398111 : Nat := 2771825569322634599587045

theorem tailTrace_5398111 : CollatzResearch.WordTrace tailWord_5398111 prefixEnd_5398111 2771825569322634599587045 := by
  unfold tailWord_5398111
  simp only [CollatzResearch.WordTrace]
  refine ⟨196885282946573245805794187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131256855297715497203862791 196885282946573245805794187)
  ·
    refine ⟨295327924419859868708691281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196885282946573245805794187 295327924419859868708691281)
    ·
      refine ⟨221495943314894901531518461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295327924419859868708691281 221495943314894901531518461)
      ·
        refine ⟨83060978743085588074319423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221495943314894901531518461 83060978743085588074319423)
        ·
          refine ⟨124591468114628382111479135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83060978743085588074319423 124591468114628382111479135)
          ·
            refine ⟨186887202171942573167218703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124591468114628382111479135 186887202171942573167218703)
            ·
              refine ⟨280330803257913859750828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186887202171942573167218703 280330803257913859750828055)
              ·
                refine ⟨420496204886870789626242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280330803257913859750828055 420496204886870789626242083)
                ·
                  refine ⟨630744307330306184439363125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420496204886870789626242083 630744307330306184439363125)
                  ·
                    refine ⟨59132278812216204791190293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 630744307330306184439363125 59132278812216204791190293)
                    ·
                      refine ⟨2771825569322634599587045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59132278812216204791190293 2771825569322634599587045)
                      ·
                        rfl

theorem cell23_5398111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_5398111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398111 prefixEnd_5398111 := by exact prefixLift 5398111
  have htrace : WordTrace (prefixWord ++ tailWord_5398111) baseStart_5398111 baseEnd_5398111 := by
    simpa [prefixWord, tailWord_5398111, baseEnd_5398111] using wordTrace_append hprefix tailTrace_5398111
  have hstable : (prefixWord ++ tailWord_5398111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398111).length < 2 ^ (prefixWord ++ tailWord_5398111).sum := by decide
  have hdescent : baseEnd_5398111 < baseStart_5398111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398125 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_5398125 : Nat := 118140960795 + 5398125 * 2 ^ 59
def prefixEnd_5398125 : Nat := 4983230072969 + 3 ^ 40 * 5398125 * 2
def baseEnd_5398125 : Nat := 923944252683932514937327

theorem tailTrace_5398125 : CollatzResearch.WordTrace tailWord_5398125 prefixEnd_5398125 923944252683932514937327 := by
  unfold tailWord_5398125
  simp only [CollatzResearch.WordTrace]
  refine ⟨196885793568522526196803829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131257195712348350797869219 196885793568522526196803829)
  ·
    refine ⟨18458043147048986830950359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196885793568522526196803829 18458043147048986830950359)
    ·
      refine ⟨27687064720573480246425539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458043147048986830950359 27687064720573480246425539)
      ·
        refine ⟨41530597080860220369638309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27687064720573480246425539 41530597080860220369638309)
        ·
          refine ⟨7786986952661291319307183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41530597080860220369638309 7786986952661291319307183)
          ·
            refine ⟨11680480428991936978960775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786986952661291319307183 11680480428991936978960775)
            ·
              refine ⟨17520720643487905468441163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11680480428991936978960775 17520720643487905468441163)
              ·
                refine ⟨26281080965231858202661745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17520720643487905468441163 26281080965231858202661745)
                ·
                  refine ⟨19710810723923893651996309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26281080965231858202661745 19710810723923893651996309)
                  ·
                    refine ⟨923944252683932514937327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19710810723923893651996309 923944252683932514937327)
                    ·
                      rfl

theorem cell23_5398125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_5398125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398125 prefixEnd_5398125 := by exact prefixLift 5398125
  have htrace : WordTrace (prefixWord ++ tailWord_5398125) baseStart_5398125 baseEnd_5398125 := by
    simpa [prefixWord, tailWord_5398125, baseEnd_5398125] using wordTrace_append hprefix tailTrace_5398125
  have hstable : (prefixWord ++ tailWord_5398125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398125).length < 2 ^ (prefixWord ++ tailWord_5398125).sum := by decide
  have hdescent : baseEnd_5398125 < baseStart_5398125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398128 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_5398128 : Nat := 118140960795 + 5398128 * 2 ^ 59
def prefixEnd_5398128 : Nat := 4983230072969 + 3 ^ 40 * 5398128 * 2
def baseEnd_5398128 : Nat := 2771834298493761033074467

theorem tailTrace_5398128 : CollatzResearch.WordTrace tailWord_5398128 prefixEnd_5398128 2771834298493761033074467 := by
  unfold tailWord_5398128
  simp only [CollatzResearch.WordTrace]
  refine ⟨98442951493755828854581519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131257268658341105139442025 98442951493755828854581519)
  ·
    refine ⟨147664427240633743281872279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98442951493755828854581519 147664427240633743281872279)
    ·
      refine ⟨221496640860950614922808419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147664427240633743281872279 221496640860950614922808419)
      ·
        refine ⟨332244961291425922384212629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221496640860950614922808419 332244961291425922384212629)
        ·
          refine ⟨15573982560535590111759967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 332244961291425922384212629 15573982560535590111759967)
          ·
            refine ⟨23360973840803385167639951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15573982560535590111759967 23360973840803385167639951)
            ·
              refine ⟨35041460761205077751459927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23360973840803385167639951 35041460761205077751459927)
              ·
                refine ⟨52562191141807616627189891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35041460761205077751459927 52562191141807616627189891)
                ·
                  refine ⟨78843286712711424940784837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52562191141807616627189891 78843286712711424940784837)
                  ·
                    refine ⟨14783116258633392176397157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78843286712711424940784837 14783116258633392176397157)
                    ·
                      refine ⟨2771834298493761033074467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14783116258633392176397157 2771834298493761033074467)
                      ·
                        rfl

theorem cell23_5398128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_5398128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398128 prefixEnd_5398128 := by exact prefixLift 5398128
  have htrace : WordTrace (prefixWord ++ tailWord_5398128) baseStart_5398128 baseEnd_5398128 := by
    simpa [prefixWord, tailWord_5398128, baseEnd_5398128] using wordTrace_append hprefix tailTrace_5398128
  have hstable : (prefixWord ++ tailWord_5398128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398128).length < 2 ^ (prefixWord ++ tailWord_5398128).sum := by decide
  have hdescent : baseEnd_5398128 < baseStart_5398128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398131 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_5398131 : Nat := 118140960795 + 5398131 * 2 ^ 59
def prefixEnd_5398131 : Nat := 4983230072969 + 3 ^ 40 * 5398131 * 2
def baseEnd_5398131 : Nat := 2771835838935724521336953

theorem tailTrace_5398131 : CollatzResearch.WordTrace tailWord_5398131 prefixEnd_5398131 2771835838935724521336953 := by
  unfold tailWord_5398131
  simp only [CollatzResearch.WordTrace]
  refine ⟨196886012406500789221522247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131257341604333859481014831 196886012406500789221522247)
  ·
    refine ⟨295329018609751183832283371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196886012406500789221522247 295329018609751183832283371)
    ·
      refine ⟨442993527914626775748425057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295329018609751183832283371 442993527914626775748425057)
      ·
        refine ⟨332245145935970081811318793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442993527914626775748425057 332245145935970081811318793)
        ·
          refine ⟨249183859451977561358489095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332245145935970081811318793 249183859451977561358489095)
          ·
            refine ⟨373775789177966342037733643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249183859451977561358489095 373775789177966342037733643)
            ·
              refine ⟨560663683766949513056600465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373775789177966342037733643 560663683766949513056600465)
              ·
                refine ⟨420497762825212134792450349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560663683766949513056600465 420497762825212134792450349)
                ·
                  refine ⟨157686661059454550547168881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420497762825212134792450349 157686661059454550547168881)
                  ·
                    refine ⟨118264995794590912910376661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157686661059454550547168881 118264995794590912910376661)
                    ·
                      refine ⟨2771835838935724521336953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118264995794590912910376661 2771835838935724521336953)
                      ·
                        rfl

theorem cell23_5398131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_5398131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398131 prefixEnd_5398131 := by exact prefixLift 5398131
  have htrace : WordTrace (prefixWord ++ tailWord_5398131) baseStart_5398131 baseEnd_5398131 := by
    simpa [prefixWord, tailWord_5398131, baseEnd_5398131] using wordTrace_append hprefix tailTrace_5398131
  have hstable : (prefixWord ++ tailWord_5398131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398131).length < 2 ^ (prefixWord ++ tailWord_5398131).sum := by decide
  have hdescent : baseEnd_5398131 < baseStart_5398131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398155 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 5]
def baseStart_5398155 : Nat := 118140960795 + 5398155 * 2 ^ 59
def prefixEnd_5398155 : Nat := 4983230072969 + 3 ^ 40 * 5398155 * 2
def baseEnd_5398155 : Nat := 307983129163492491937427

theorem tailTrace_5398155 : CollatzResearch.WordTrace tailWord_5398155 prefixEnd_5398155 307983129163492491937427 := by
  unfold tailWord_5398155
  simp only [CollatzResearch.WordTrace]
  refine ⟨196886887758413841320395919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131257925172275894213597279 196886887758413841320395919)
  ·
    refine ⟨295330331637620761980593879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196886887758413841320395919 295330331637620761980593879)
    ·
      refine ⟨442995497456431142970890819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295330331637620761980593879 442995497456431142970890819)
      ·
        refine ⟨664493246184646714456336229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442995497456431142970890819 664493246184646714456336229)
        ·
          refine ⟨124592483659621258960563043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 664493246184646714456336229 124592483659621258960563043)
          ·
            refine ⟨186888725489431888440844565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124592483659621258960563043 186888725489431888440844565)
            ·
              refine ⟨8760409007317119770664589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186888725489431888440844565 8760409007317119770664589)
              ·
                refine ⟨3285153377743919913999221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8760409007317119770664589 3285153377743919913999221)
                ·
                  refine ⟨307983129163492491937427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285153377743919913999221 307983129163492491937427)
                  ·
                    rfl

theorem cell23_5398155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 5].length) (baseStart_5398155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398155 prefixEnd_5398155 := by exact prefixLift 5398155
  have htrace : WordTrace (prefixWord ++ tailWord_5398155) baseStart_5398155 baseEnd_5398155 := by
    simpa [prefixWord, tailWord_5398155, baseEnd_5398155] using wordTrace_append hprefix tailTrace_5398155
  have hstable : (prefixWord ++ tailWord_5398155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398155).length < 2 ^ (prefixWord ++ tailWord_5398155).sum := by decide
  have hdescent : baseEnd_5398155 < baseStart_5398155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398205 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_5398205 : Nat := 118140960795 + 5398205 * 2 ^ 59
def prefixEnd_5398205 : Nat := 4983230072969 + 3 ^ 40 * 5398205 * 2
def baseEnd_5398205 : Nat := 2771873836504157231811613

theorem tailTrace_5398205 : CollatzResearch.WordTrace tailWord_5398205 prefixEnd_5398205 2771873836504157231811613 := by
  unfold tailWord_5398205
  simp only [CollatzResearch.WordTrace]
  refine ⟨196888711408232699859716069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131259140938821799906477379 196888711408232699859716069)
  ·
    refine ⟨36916633389043631223696763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196888711408232699859716069 36916633389043631223696763)
    ·
      refine ⟨55374950083565446835545145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36916633389043631223696763 55374950083565446835545145)
      ·
        refine ⟨41531212562674085126658859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55374950083565446835545145 41531212562674085126658859)
        ·
          refine ⟨62296818844011127689988289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41531212562674085126658859 62296818844011127689988289)
          ·
            refine ⟨46722614133008345767491217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62296818844011127689988289 46722614133008345767491217)
            ·
              refine ⟨35041960599756259325618413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46722614133008345767491217 35041960599756259325618413)
              ·
                refine ⟨13140735224908597247106905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35041960599756259325618413 13140735224908597247106905)
                ·
                  refine ⟨9855551418681447935330179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13140735224908597247106905 9855551418681447935330179)
                  ·
                    refine ⟨14783327128022171902995269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9855551418681447935330179 14783327128022171902995269)
                    ·
                      refine ⟨2771873836504157231811613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14783327128022171902995269 2771873836504157231811613)
                      ·
                        rfl

theorem cell23_5398205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_5398205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398205 prefixEnd_5398205 := by exact prefixLift 5398205
  have htrace : WordTrace (prefixWord ++ tailWord_5398205) baseStart_5398205 baseEnd_5398205 := by
    simpa [prefixWord, tailWord_5398205, baseEnd_5398205] using wordTrace_append hprefix tailTrace_5398205
  have hstable : (prefixWord ++ tailWord_5398205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398205).length < 2 ^ (prefixWord ++ tailWord_5398205).sum := by decide
  have hdescent : baseEnd_5398205 < baseStart_5398205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398225 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_5398225 : Nat := 118140960795 + 5398225 * 2 ^ 59
def prefixEnd_5398225 : Nat := 4983230072969 + 3 ^ 40 * 5398225 * 2
def baseEnd_5398225 : Nat := 2771884106117247153561521

theorem tailTrace_5398225 : CollatzResearch.WordTrace tailWord_5398225 prefixEnd_5398225 2771884106117247153561521 := by
  unfold tailWord_5398225
  simp only [CollatzResearch.WordTrace]
  refine ⟨196889440868160243275444129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131259627245440162183629419 196889440868160243275444129)
  ·
    refine ⟨147667080651120182456583097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196889440868160243275444129 147667080651120182456583097)
    ·
      refine ⟨110750310488340136842437323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147667080651120182456583097 110750310488340136842437323)
      ·
        refine ⟨166125465732510205263655985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110750310488340136842437323 166125465732510205263655985)
        ·
          refine ⟨124594099299382653947741989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166125465732510205263655985 124594099299382653947741989)
          ·
            refine ⟨23361393618634247615201623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124594099299382653947741989 23361393618634247615201623)
            ·
              refine ⟨35042090427951371422802435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23361393618634247615201623 35042090427951371422802435)
              ·
                refine ⟨52563135641927057134203653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35042090427951371422802435 52563135641927057134203653)
                ·
                  refine ⟨9855587932861323212663185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52563135641927057134203653 9855587932861323212663185)
                  ·
                    refine ⟨7391690949645992409497389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9855587932861323212663185 7391690949645992409497389)
                    ·
                      refine ⟨2771884106117247153561521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391690949645992409497389 2771884106117247153561521)
                      ·
                        rfl

theorem cell23_5398225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_5398225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398225 prefixEnd_5398225 := by exact prefixLift 5398225
  have htrace : WordTrace (prefixWord ++ tailWord_5398225) baseStart_5398225 baseEnd_5398225 := by
    simpa [prefixWord, tailWord_5398225, baseEnd_5398225] using wordTrace_append hprefix tailTrace_5398225
  have hstable : (prefixWord ++ tailWord_5398225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398225).length < 2 ^ (prefixWord ++ tailWord_5398225).sum := by decide
  have hdescent : baseEnd_5398225 < baseStart_5398225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398245 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 6]
def baseStart_5398245 : Nat := 118140960795 + 5398245 * 2 ^ 59
def prefixEnd_5398245 : Nat := 4983230072969 + 3 ^ 40 * 5398245 * 2
def baseEnd_5398245 : Nat := 307988263970037452812381

theorem tailTrace_5398245 : CollatzResearch.WordTrace tailWord_5398245 prefixEnd_5398245 307988263970037452812381 := by
  unfold tailWord_5398245
  simp only [CollatzResearch.WordTrace]
  refine ⟨196890170328087786691172189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131260113552058524460781459 196890170328087786691172189)
  ·
    refine ⟨73833813873032920009189571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196890170328087786691172189 73833813873032920009189571)
    ·
      refine ⟨110750720809549380013784357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73833813873032920009189571 110750720809549380013784357)
      ·
        refine ⟨20765760151790508752584567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110750720809549380013784357 20765760151790508752584567)
        ·
          refine ⟨31148640227685763128876851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20765760151790508752584567 31148640227685763128876851)
          ·
            refine ⟨46722960341528644693315277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31148640227685763128876851 46722960341528644693315277)
            ·
              refine ⟨17521110128073241759993229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46722960341528644693315277 17521110128073241759993229)
              ·
                refine ⟨6570416298027465659997461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17521110128073241759993229 6570416298027465659997461)
                ·
                  refine ⟨307988263970037452812381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6570416298027465659997461 307988263970037452812381)
                  ·
                    rfl

theorem cell23_5398245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_5398245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398245 prefixEnd_5398245 := by exact prefixLift 5398245
  have htrace : WordTrace (prefixWord ++ tailWord_5398245) baseStart_5398245 baseEnd_5398245 := by
    simpa [prefixWord, tailWord_5398245, baseEnd_5398245] using wordTrace_append hprefix tailTrace_5398245
  have hstable : (prefixWord ++ tailWord_5398245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398245).length < 2 ^ (prefixWord ++ tailWord_5398245).sum := by decide
  have hdescent : baseEnd_5398245 < baseStart_5398245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398275 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 1, 5]
def baseStart_5398275 : Nat := 118140960795 + 5398275 * 2 ^ 59
def prefixEnd_5398275 : Nat := 4983230072969 + 3 ^ 40 * 5398275 * 2
def baseEnd_5398275 : Nat := 923969926716657319312097

theorem tailTrace_5398275 : CollatzResearch.WordTrace tailWord_5398275 prefixEnd_5398275 923969926716657319312097 := by
  unfold tailWord_5398275
  simp only [CollatzResearch.WordTrace]
  refine ⟨196891264517979101814764279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131260843011986067876509519 196891264517979101814764279)
  ·
    refine ⟨295336896776968652722146419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196891264517979101814764279 295336896776968652722146419)
    ·
      refine ⟨443005345165452979083219629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295336896776968652722146419 443005345165452979083219629)
      ·
        refine ⟨166127004437044867156207361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443005345165452979083219629 166127004437044867156207361)
        ·
          refine ⟨124595253327783650367155521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166127004437044867156207361 124595253327783650367155521)
          ·
            refine ⟨93446439995837737775366641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124595253327783650367155521 93446439995837737775366641)
            ·
              refine ⟨70084829996878303331524981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93446439995837737775366641 70084829996878303331524981)
              ·
                refine ⟨6570452812207340937330467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70084829996878303331524981 6570452812207340937330467)
                ·
                  refine ⟨9855679218311011405995701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6570452812207340937330467 9855679218311011405995701)
                  ·
                    refine ⟨923969926716657319312097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9855679218311011405995701 923969926716657319312097)
                    ·
                      rfl

theorem cell23_5398275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 5].length) (baseStart_5398275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398275 prefixEnd_5398275 := by exact prefixLift 5398275
  have htrace : WordTrace (prefixWord ++ tailWord_5398275) baseStart_5398275 baseEnd_5398275 := by
    simpa [prefixWord, tailWord_5398275, baseEnd_5398275] using wordTrace_append hprefix tailTrace_5398275
  have hstable : (prefixWord ++ tailWord_5398275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398275).length < 2 ^ (prefixWord ++ tailWord_5398275).sum := by decide
  have hdescent : baseEnd_5398275 < baseStart_5398275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398305 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_5398305 : Nat := 118140960795 + 5398305 * 2 ^ 59
def prefixEnd_5398305 : Nat := 4983230072969 + 3 ^ 40 * 5398305 * 2
def baseEnd_5398305 : Nat := 923975061523202280187051

theorem tailTrace_5398305 : CollatzResearch.WordTrace tailWord_5398305 prefixEnd_5398305 923975061523202280187051 := by
  unfold tailWord_5398305
  simp only [CollatzResearch.WordTrace]
  refine ⟨196892358707870416938356369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131261572471913611292237579 196892358707870416938356369)
  ·
    refine ⟨147669269030902812703767277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196892358707870416938356369 147669269030902812703767277)
    ·
      refine ⟨55375975886588554763912729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147669269030902812703767277 55375975886588554763912729)
      ·
        refine ⟨41531981914941416072934547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55375975886588554763912729 41531981914941416072934547)
        ·
          refine ⟨62297972872412124109401821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41531981914941416072934547 62297972872412124109401821)
          ·
            refine ⟨23361739827154546541025683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62297972872412124109401821 23361739827154546541025683)
            ·
              refine ⟨35042609740731819811538525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23361739827154546541025683 35042609740731819811538525)
              ·
                refine ⟨13140978652774432429326947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35042609740731819811538525 13140978652774432429326947)
                ·
                  refine ⟨19711467979161648643990421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13140978652774432429326947 19711467979161648643990421)
                  ·
                    refine ⟨923975061523202280187051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19711467979161648643990421 923975061523202280187051)
                    ·
                      rfl

theorem cell23_5398305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_5398305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398305 prefixEnd_5398305 := by exact prefixLift 5398305
  have htrace : WordTrace (prefixWord ++ tailWord_5398305) baseStart_5398305 baseEnd_5398305 := by
    simpa [prefixWord, tailWord_5398305, baseEnd_5398305] using wordTrace_append hprefix tailTrace_5398305
  have hstable : (prefixWord ++ tailWord_5398305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398305).length < 2 ^ (prefixWord ++ tailWord_5398305).sum := by decide
  have hdescent : baseEnd_5398305 < baseStart_5398305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398312 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5398312 : Nat := 118140960795 + 5398312 * 2 ^ 59
def prefixEnd_5398312 : Nat := 4983230072969 + 3 ^ 40 * 5398312 * 2
def baseEnd_5398312 : Nat := 2771928778934188313173621

theorem tailTrace_5398312 : CollatzResearch.WordTrace tailWord_5398312 prefixEnd_5398312 2771928778934188313173621 := by
  unfold tailWord_5398312
  simp only [CollatzResearch.WordTrace]
  refine ⟨98446307009422528566930595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131261742679230038089240793 98446307009422528566930595)
  ·
    refine ⟨147669460514133792850395893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98446307009422528566930595 147669460514133792850395893)
    ·
      refine ⟨13844011923200043079724615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147669460514133792850395893 13844011923200043079724615)
      ·
        refine ⟨20766017884800064619586923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13844011923200043079724615 20766017884800064619586923)
        ·
          refine ⟨31149026827200096929380385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20766017884800064619586923 31149026827200096929380385)
          ·
            refine ⟨23361770120400072697035289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31149026827200096929380385 23361770120400072697035289)
            ·
              refine ⟨17521327590300054522776467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23361770120400072697035289 17521327590300054522776467)
              ·
                refine ⟨26281991385450081784164701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17521327590300054522776467 26281991385450081784164701)
                ·
                  refine ⟨9855746769543780669061763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26281991385450081784164701 9855746769543780669061763)
                  ·
                    refine ⟨14783620154315671003592645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9855746769543780669061763 14783620154315671003592645)
                    ·
                      refine ⟨2771928778934188313173621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14783620154315671003592645 2771928778934188313173621)
                      ·
                        rfl

theorem cell23_5398312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5398312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398312 prefixEnd_5398312 := by exact prefixLift 5398312
  have htrace : WordTrace (prefixWord ++ tailWord_5398312) baseStart_5398312 baseEnd_5398312 := by
    simpa [prefixWord, tailWord_5398312, baseEnd_5398312] using wordTrace_append hprefix tailTrace_5398312
  have hstable : (prefixWord ++ tailWord_5398312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398312).length < 2 ^ (prefixWord ++ tailWord_5398312).sum := by decide
  have hdescent : baseEnd_5398312 < baseStart_5398312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398315 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3]
def baseStart_5398315 : Nat := 118140960795 + 5398315 * 2 ^ 59
def prefixEnd_5398315 : Nat := 4983230072969 + 3 ^ 40 * 5398315 * 2
def baseEnd_5398315 : Nat := 2771930319376151801436107

theorem tailTrace_5398315 : CollatzResearch.WordTrace tailWord_5398315 prefixEnd_5398315 2771930319376151801436107 := by
  unfold tailWord_5398315
  simp only [CollatzResearch.WordTrace]
  refine ⟨196892723437834188646220399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131261815625222792430813599 196892723437834188646220399)
  ·
    refine ⟨295339085156751282969330599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196892723437834188646220399 295339085156751282969330599)
    ·
      refine ⟨443008627735126924453995899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295339085156751282969330599 443008627735126924453995899)
      ·
        refine ⟨664512941602690386680993849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443008627735126924453995899 664512941602690386680993849)
        ·
          refine ⟨498384706202017790010745387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664512941602690386680993849 498384706202017790010745387)
          ·
            refine ⟨747577059303026685016118081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498384706202017790010745387 747577059303026685016118081)
            ·
              refine ⟨560682794477270013762088561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747577059303026685016118081 560682794477270013762088561)
              ·
                refine ⟨420512095857952510321566421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560682794477270013762088561 420512095857952510321566421)
                ·
                  refine ⟨9855752246670761960661713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 420512095857952510321566421 9855752246670761960661713)
                  ·
                    refine ⟨7391814185003071470496285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9855752246670761960661713 7391814185003071470496285)
                    ·
                      refine ⟨2771930319376151801436107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7391814185003071470496285 2771930319376151801436107)
                      ·
                        rfl

theorem cell23_5398315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].length) (baseStart_5398315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398315 prefixEnd_5398315 := by exact prefixLift 5398315
  have htrace : WordTrace (prefixWord ++ tailWord_5398315) baseStart_5398315 baseEnd_5398315 := by
    simpa [prefixWord, tailWord_5398315, baseEnd_5398315] using wordTrace_append hprefix tailTrace_5398315
  have hstable : (prefixWord ++ tailWord_5398315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398315).length < 2 ^ (prefixWord ++ tailWord_5398315).sum := by decide
  have hdescent : baseEnd_5398315 < baseStart_5398315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5398326 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5398326 : Nat := 118140960795 + 5398326 * 2 ^ 59
def prefixEnd_5398326 : Nat := 4983230072969 + 3 ^ 40 * 5398326 * 2
def baseEnd_5398326 : Nat := 923978655887783752799519

theorem tailTrace_5398326 : CollatzResearch.WordTrace tailWord_5398326 prefixEnd_5398326 923978655887783752799519 := by
  unfold tailWord_5398326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305820290049646095304427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131262083093862891683247221 12305820290049646095304427)
  ·
    refine ⟨18458730435074469142956641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12305820290049646095304427 18458730435074469142956641)
    ·
      refine ⟨13844047826305851857217481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18458730435074469142956641 13844047826305851857217481)
      ·
        refine ⟨10383035869729388892913111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13844047826305851857217481 10383035869729388892913111)
        ·
          refine ⟨15574553804594083339369667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10383035869729388892913111 15574553804594083339369667)
          ·
            refine ⟨23361830706891125009054501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15574553804594083339369667 23361830706891125009054501)
            ·
              refine ⟨4380343257542085939197719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23361830706891125009054501 4380343257542085939197719)
              ·
                refine ⟨6570514886313128908796579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380343257542085939197719 6570514886313128908796579)
                ·
                  refine ⟨9855772329469693363194869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6570514886313128908796579 9855772329469693363194869)
                  ·
                    refine ⟨923978655887783752799519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9855772329469693363194869 923978655887783752799519)
                    ·
                      rfl

theorem cell23_5398326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5398326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5398326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5398326 prefixEnd_5398326 := by exact prefixLift 5398326
  have htrace : WordTrace (prefixWord ++ tailWord_5398326) baseStart_5398326 baseEnd_5398326 := by
    simpa [prefixWord, tailWord_5398326, baseEnd_5398326] using wordTrace_append hprefix tailTrace_5398326
  have hstable : (prefixWord ++ tailWord_5398326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5398326).length < 2 ^ (prefixWord ++ tailWord_5398326).sum := by decide
  have hdescent : baseEnd_5398326 < baseStart_5398326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5398326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
