import V185TrunkScan23Chunk0768

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4547776 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4]
def baseStart_4547776 : Nat := 118140960795 + 4547776 * 2 ^ 59
def prefixEnd_4547776 : Nat := 4983230072969 + 3 ^ 40 * 4547776 * 2
def baseEnd_4547776 : Nat := 2335194996981704039185165

theorem tailTrace_4547776 : CollatzResearch.WordTrace tailWord_4547776 prefixEnd_4547776 2335194996981704039185165 := by
  unfold tailWord_4547776
  simp only [CollatzResearch.WordTrace]
  refine ⟨82935508786095862574899591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110580678381461150099866121 82935508786095862574899591)
  ·
    refine ⟨124403263179143793862349387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82935508786095862574899591 124403263179143793862349387)
    ·
      refine ⟨186604894768715690793524081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124403263179143793862349387 186604894768715690793524081)
      ·
        refine ⟨139953671076536768095143061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186604894768715690793524081 139953671076536768095143061)
        ·
          refine ⟨6560328331712661004459831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139953671076536768095143061 6560328331712661004459831)
          ·
            refine ⟨9840492497568991506689747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560328331712661004459831 9840492497568991506689747)
            ·
              refine ⟨14760738746353487260034621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9840492497568991506689747 14760738746353487260034621)
              ·
                refine ⟨5535277029882557722512983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14760738746353487260034621 5535277029882557722512983)
                ·
                  refine ⟨8302915544823836583769475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535277029882557722512983 8302915544823836583769475)
                  ·
                    refine ⟨12454373317235754875654213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8302915544823836583769475 12454373317235754875654213)
                    ·
                      refine ⟨2335194996981704039185165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12454373317235754875654213 2335194996981704039185165)
                      ·
                        rfl

theorem cell23_4547776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_4547776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547776 prefixEnd_4547776 := by exact prefixLift 4547776
  have htrace : WordTrace (prefixWord ++ tailWord_4547776) baseStart_4547776 baseEnd_4547776 := by
    simpa [prefixWord, tailWord_4547776, baseEnd_4547776] using wordTrace_append hprefix tailTrace_4547776
  have hstable : (prefixWord ++ tailWord_4547776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547776).length < 2 ^ (prefixWord ++ tailWord_4547776).sum := by decide
  have hdescent : baseEnd_4547776 < baseStart_4547776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547786 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_4547786 : Nat := 118140960795 + 4547786 * 2 ^ 59
def prefixEnd_4547786 : Nat := 4983230072969 + 3 ^ 40 * 4547786 * 2
def baseEnd_4547786 : Nat := 778400043929416333353373

theorem tailTrace_4547786 : CollatzResearch.WordTrace tailWord_4547786 prefixEnd_4547786 778400043929416333353373 := by
  unfold tailWord_4547786
  simp only [CollatzResearch.WordTrace]
  refine ⟨41467845575538874214415803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110580921534770331238442141 41467845575538874214415803)
  ·
    refine ⟨62201768363308311321623705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41467845575538874214415803 62201768363308311321623705)
    ·
      refine ⟨46651326272481233491217779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62201768363308311321623705 46651326272481233491217779)
      ·
        refine ⟨69976989408721850236826669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46651326272481233491217779 69976989408721850236826669)
        ·
          refine ⟨26241371028270693838810001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69976989408721850236826669 26241371028270693838810001)
          ·
            refine ⟨19681028271203020379107501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26241371028270693838810001 19681028271203020379107501)
            ·
              refine ⟨7380385601701132642165313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19681028271203020379107501 7380385601701132642165313)
              ·
                refine ⟨5535289201275849481623985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380385601701132642165313 5535289201275849481623985)
                ·
                  refine ⟨4151466900956887111217989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535289201275849481623985 4151466900956887111217989)
                  ·
                    refine ⟨778400043929416333353373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151466900956887111217989 778400043929416333353373)
                    ·
                      rfl

theorem cell23_4547786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_4547786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547786 prefixEnd_4547786 := by exact prefixLift 4547786
  have htrace : WordTrace (prefixWord ++ tailWord_4547786) baseStart_4547786 baseEnd_4547786 := by
    simpa [prefixWord, tailWord_4547786, baseEnd_4547786] using wordTrace_append hprefix tailTrace_4547786
  have hstable : (prefixWord ++ tailWord_4547786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547786).length < 2 ^ (prefixWord ++ tailWord_4547786).sum := by decide
  have hdescent : baseEnd_4547786 < baseStart_4547786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547792 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_4547792 : Nat := 118140960795 + 4547792 * 2 ^ 59
def prefixEnd_4547792 : Nat := 4983230072969 + 3 ^ 40 * 4547792 * 2
def baseEnd_4547792 : Nat := 2335203212672175976585091

theorem tailTrace_4547792 : CollatzResearch.WordTrace tailWord_4547792 prefixEnd_4547792 2335203212672175976585091 := by
  unfold tailWord_4547792
  simp only [CollatzResearch.WordTrace]
  refine ⟨82935800570066879941190815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110581067426755839921587753 82935800570066879941190815)
  ·
    refine ⟨124403700855100319911786223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82935800570066879941190815 124403700855100319911786223)
    ·
      refine ⟨186605551282650479867679335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124403700855100319911786223 186605551282650479867679335)
      ·
        refine ⟨279908326923975719801519003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186605551282650479867679335 279908326923975719801519003)
        ·
          refine ⟨419862490385963579702278505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279908326923975719801519003 419862490385963579702278505)
          ·
            refine ⟨314896867789472684776708879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419862490385963579702278505 314896867789472684776708879)
            ·
              refine ⟨472345301684209027165063319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314896867789472684776708879 472345301684209027165063319)
              ·
                refine ⟨708517952526313540747594979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472345301684209027165063319 708517952526313540747594979)
                ·
                  refine ⟨1062776928789470311121392469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708517952526313540747594979 1062776928789470311121392469)
                  ·
                    refine ⟨6227208567125802604226909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1062776928789470311121392469 6227208567125802604226909)
                    ·
                      refine ⟨2335203212672175976585091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227208567125802604226909 2335203212672175976585091)
                      ·
                        rfl

theorem cell23_4547792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_4547792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547792 prefixEnd_4547792 := by exact prefixLift 4547792
  have htrace : WordTrace (prefixWord ++ tailWord_4547792) baseStart_4547792 baseEnd_4547792 := by
    simpa [prefixWord, tailWord_4547792, baseEnd_4547792] using wordTrace_append hprefix tailTrace_4547792
  have hstable : (prefixWord ++ tailWord_4547792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547792).length < 2 ^ (prefixWord ++ tailWord_4547792).sum := by decide
  have hdescent : baseEnd_4547792 < baseStart_4547792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547812 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_4547812 : Nat := 118140960795 + 4547812 * 2 ^ 59
def prefixEnd_4547812 : Nat := 4983230072969 + 3 ^ 40 * 4547812 * 2
def baseEnd_4547812 : Nat := 778404494095088632778333

theorem tailTrace_4547812 : CollatzResearch.WordTrace tailWord_4547812 prefixEnd_4547812 778404494095088632778333 := by
  unfold tailWord_4547812
  simp only [CollatzResearch.WordTrace]
  refine ⟨82936165300030651649054845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110581553733374202198739793 82936165300030651649054845)
  ·
    refine ⟨31101061987511494368395567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82936165300030651649054845 31101061987511494368395567)
    ·
      refine ⟨46651592981267241552593351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31101061987511494368395567 46651592981267241552593351)
      ·
        refine ⟨69977389471900862328890027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46651592981267241552593351 69977389471900862328890027)
        ·
          refine ⟨104966084207851293493335041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69977389471900862328890027 104966084207851293493335041)
          ·
            refine ⟨78724563155888470120001281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104966084207851293493335041 78724563155888470120001281)
            ·
              refine ⟨59043422366916352590000961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78724563155888470120001281 59043422366916352590000961)
              ·
                refine ⟨44282566775187264442500721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59043422366916352590000961 44282566775187264442500721)
                ·
                  refine ⟨33211925081390448331875541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44282566775187264442500721 33211925081390448331875541)
                  ·
                    refine ⟨778404494095088632778333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33211925081390448331875541 778404494095088632778333)
                    ·
                      rfl

theorem cell23_4547812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_4547812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547812 prefixEnd_4547812 := by exact prefixLift 4547812
  have htrace : WordTrace (prefixWord ++ tailWord_4547812) baseStart_4547812 baseEnd_4547812 := by
    simpa [prefixWord, tailWord_4547812, baseEnd_4547812] using wordTrace_append hprefix tailTrace_4547812
  have hstable : (prefixWord ++ tailWord_4547812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547812).length < 2 ^ (prefixWord ++ tailWord_4547812).sum := by decide
  have hdescent : baseEnd_4547812 < baseStart_4547812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547813 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4547813 : Nat := 118140960795 + 4547813 * 2 ^ 59
def prefixEnd_4547813 : Nat := 4983230072969 + 3 ^ 40 * 4547813 * 2
def baseEnd_4547813 : Nat := 2335213995765920394422495

theorem tailTrace_4547813 : CollatzResearch.WordTrace tailWord_4547813 prefixEnd_4547813 2335213995765920394422495 := by
  unfold tailWord_4547813
  simp only [CollatzResearch.WordTrace]
  refine ⟨165872367073057680468896093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110581578048705120312597395 165872367073057680468896093)
  ·
    refine ⟨62202137652396630175836035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165872367073057680468896093 62202137652396630175836035)
    ·
      refine ⟨93303206478594945263754053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62202137652396630175836035 93303206478594945263754053)
      ·
        refine ⟨17494351214736552236953885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93303206478594945263754053 17494351214736552236953885)
        ·
          refine ⟨6560381705526207088857707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17494351214736552236953885 6560381705526207088857707)
          ·
            refine ⟨9840572558289310633286561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560381705526207088857707 9840572558289310633286561)
            ·
              refine ⟨7380429418716982974964921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840572558289310633286561 7380429418716982974964921)
              ·
                refine ⟨5535322064037737231223691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380429418716982974964921 5535322064037737231223691)
                ·
                  refine ⟨8302983096056605846835537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535322064037737231223691 8302983096056605846835537)
                  ·
                    refine ⟨6227237322042454385126653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8302983096056605846835537 6227237322042454385126653)
                    ·
                      refine ⟨2335213995765920394422495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227237322042454385126653 2335213995765920394422495)
                      ·
                        rfl

theorem cell23_4547813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4547813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547813 prefixEnd_4547813 := by exact prefixLift 4547813
  have htrace : WordTrace (prefixWord ++ tailWord_4547813) baseStart_4547813 baseEnd_4547813 := by
    simpa [prefixWord, tailWord_4547813, baseEnd_4547813] using wordTrace_append hprefix tailTrace_4547813
  have hstable : (prefixWord ++ tailWord_4547813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547813).length < 2 ^ (prefixWord ++ tailWord_4547813).sum := by decide
  have hdescent : baseEnd_4547813 < baseStart_4547813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547832 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_4547832 : Nat := 118140960795 + 4547832 * 2 ^ 59
def prefixEnd_4547832 : Nat := 4983230072969 + 3 ^ 40 * 4547832 * 2
def baseEnd_4547832 : Nat := 2335223751898355820084907

theorem tailTrace_4547832 : CollatzResearch.WordTrace tailWord_4547832 prefixEnd_4547832 2335223751898355820084907 := by
  unfold tailWord_4547832
  simp only [CollatzResearch.WordTrace]
  refine ⟨82936530029994423356918875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110582040039992564475891833 82936530029994423356918875)
  ·
    refine ⟨124404795044991635035378313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82936530029994423356918875 124404795044991635035378313)
    ·
      refine ⟨93303596283743726276533735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124404795044991635035378313 93303596283743726276533735)
      ·
        refine ⟨139955394425615589414800603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93303596283743726276533735 139955394425615589414800603)
        ·
          refine ⟨209933091638423384122200905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139955394425615589414800603 209933091638423384122200905)
          ·
            refine ⟨157449818728817538091650679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209933091638423384122200905 157449818728817538091650679)
            ·
              refine ⟨236174728093226307137476019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157449818728817538091650679 236174728093226307137476019)
              ·
                refine ⟨354262092139839460706214029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236174728093226307137476019 354262092139839460706214029)
                ·
                  refine ⟨132848284552439797764830261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 354262092139839460706214029 132848284552439797764830261)
                  ·
                    refine ⟨12454526676791231040452837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132848284552439797764830261 12454526676791231040452837)
                    ·
                      refine ⟨2335223751898355820084907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12454526676791231040452837 2335223751898355820084907)
                      ·
                        rfl

theorem cell23_4547832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_4547832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547832 prefixEnd_4547832 := by exact prefixLift 4547832
  have htrace : WordTrace (prefixWord ++ tailWord_4547832) baseStart_4547832 baseEnd_4547832 := by
    simpa [prefixWord, tailWord_4547832, baseEnd_4547832] using wordTrace_append hprefix tailTrace_4547832
  have hstable : (prefixWord ++ tailWord_4547832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547832).length < 2 ^ (prefixWord ++ tailWord_4547832).sum := by decide
  have hdescent : baseEnd_4547832 < baseStart_4547832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547900 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_4547900 : Nat := 118140960795 + 4547900 * 2 ^ 59
def prefixEnd_4547900 : Nat := 4983230072969 + 3 ^ 40 * 4547900 * 2
def baseEnd_4547900 : Nat := 2335258668582861554034595

theorem tailTrace_4547900 : CollatzResearch.WordTrace tailWord_4547900 prefixEnd_4547900 2335258668582861554034595 := by
  unfold tailWord_4547900
  simp only [CollatzResearch.WordTrace]
  refine ⟨82937770111871247163656577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110583693482494996218208769 82937770111871247163656577)
  ·
    refine ⟨62203327583903435372742433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82937770111871247163656577 62203327583903435372742433)
    ·
      refine ⟨46652495687927576529556825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62203327583903435372742433 46652495687927576529556825)
      ·
        refine ⟨34989371765945682397167619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46652495687927576529556825 34989371765945682397167619)
        ·
          refine ⟨52484057648918523595751429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34989371765945682397167619 52484057648918523595751429)
          ·
            refine ⟨9840760809172223174203393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52484057648918523595751429 9840760809172223174203393)
            ·
              refine ⟨7380570606879167380652545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840760809172223174203393 7380570606879167380652545)
              ·
                refine ⟨5535427955159375535489409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7380570606879167380652545 5535427955159375535489409)
                ·
                  refine ⟨4151570966369531651617057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535427955159375535489409 4151570966369531651617057)
                  ·
                    refine ⟨3113678224777148738712793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151570966369531651617057 3113678224777148738712793)
                    ·
                      refine ⟨2335258668582861554034595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113678224777148738712793 2335258668582861554034595)
                      ·
                        rfl

theorem cell23_4547900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_4547900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547900 prefixEnd_4547900 := by exact prefixLift 4547900
  have htrace : WordTrace (prefixWord ++ tailWord_4547900) baseStart_4547900 baseEnd_4547900 := by
    simpa [prefixWord, tailWord_4547900, baseEnd_4547900] using wordTrace_append hprefix tailTrace_4547900
  have hstable : (prefixWord ++ tailWord_4547900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547900).length < 2 ^ (prefixWord ++ tailWord_4547900).sum := by decide
  have hdescent : baseEnd_4547900 < baseStart_4547900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547910 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_4547910 : Nat := 118140960795 + 4547910 * 2 ^ 59
def prefixEnd_4547910 : Nat := 4983230072969 + 3 ^ 40 * 4547910 * 2
def baseEnd_4547910 : Nat := 778421267796468838303183

theorem tailTrace_4547910 : CollatzResearch.WordTrace tailWord_4547910 prefixEnd_4547910 778421267796468838303183 := by
  unfold tailWord_4547910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183622029803320813599287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110583936635804177356784789 5183622029803320813599287)
  ·
    refine ⟨7775433044704981220398931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5183622029803320813599287 7775433044704981220398931)
    ·
      refine ⟨11663149567057471830598397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775433044704981220398931 11663149567057471830598397)
      ·
        refine ⟨4373681087646551936474399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11663149567057471830598397 4373681087646551936474399)
        ·
          refine ⟨6560521631469827904711599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373681087646551936474399 6560521631469827904711599)
          ·
            refine ⟨9840782447204741857067399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560521631469827904711599 9840782447204741857067399)
            ·
              refine ⟨14761173670807112785601099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9840782447204741857067399 14761173670807112785601099)
              ·
                refine ⟨22141760506210669178401649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14761173670807112785601099 22141760506210669178401649)
                ·
                  refine ⟨16606320379658001883801237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22141760506210669178401649 16606320379658001883801237)
                  ·
                    refine ⟨778421267796468838303183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16606320379658001883801237 778421267796468838303183)
                    ·
                      rfl

theorem cell23_4547910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_4547910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547910 prefixEnd_4547910 := by exact prefixLift 4547910
  have htrace : WordTrace (prefixWord ++ tailWord_4547910) baseStart_4547910 baseEnd_4547910 := by
    simpa [prefixWord, tailWord_4547910, baseEnd_4547910] using wordTrace_append hprefix tailTrace_4547910
  have hstable : (prefixWord ++ tailWord_4547910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547910).length < 2 ^ (prefixWord ++ tailWord_4547910).sum := by decide
  have hdescent : baseEnd_4547910 < baseStart_4547910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547916 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4547916 : Nat := 118140960795 + 4547916 * 2 ^ 59
def prefixEnd_4547916 : Nat := 4983230072969 + 3 ^ 40 * 4547916 * 2
def baseEnd_4547916 : Nat := 2335266884273333491434521

theorem tailTrace_4547916 : CollatzResearch.WordTrace tailWord_4547916 prefixEnd_4547916 2335266884273333491434521 := by
  unfold tailWord_4547916
  simp only [CollatzResearch.WordTrace]
  refine ⟨82938061895842264529947801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110584082527789686039930401 82938061895842264529947801)
  ·
    refine ⟨62203546421881698397460851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82938061895842264529947801 62203546421881698397460851)
    ·
      refine ⟨93305319632822547596191277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62203546421881698397460851 93305319632822547596191277)
      ·
        refine ⟨34989494862308455348571729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93305319632822547596191277 34989494862308455348571729)
        ·
          refine ⟨26242121146731341511428797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34989494862308455348571729 26242121146731341511428797)
          ·
            refine ⟨9840795430024253066785799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26242121146731341511428797 9840795430024253066785799)
            ·
              refine ⟨14761193145036379600178699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9840795430024253066785799 14761193145036379600178699)
              ·
                refine ⟨22141789717554569400268049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14761193145036379600178699 22141789717554569400268049)
                ·
                  refine ⟨16606342288165927050201037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22141789717554569400268049 16606342288165927050201037)
                  ·
                    refine ⟨6227378358062222643825389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16606342288165927050201037 6227378358062222643825389)
                    ·
                      refine ⟨2335266884273333491434521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227378358062222643825389 2335266884273333491434521)
                      ·
                        rfl

theorem cell23_4547916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4547916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547916 prefixEnd_4547916 := by exact prefixLift 4547916
  have htrace : WordTrace (prefixWord ++ tailWord_4547916) baseStart_4547916 baseEnd_4547916 := by
    simpa [prefixWord, tailWord_4547916, baseEnd_4547916] using wordTrace_append hprefix tailTrace_4547916
  have hstable : (prefixWord ++ tailWord_4547916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547916).length < 2 ^ (prefixWord ++ tailWord_4547916).sum := by decide
  have hdescent : baseEnd_4547916 < baseStart_4547916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547917 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4547917 : Nat := 118140960795 + 4547917 * 2 ^ 59
def prefixEnd_4547917 : Nat := 4983230072969 + 3 ^ 40 * 4547917 * 2
def baseEnd_4547917 : Nat := 2335267397753987987522017

theorem tailTrace_4547917 : CollatzResearch.WordTrace tailWord_4547917 prefixEnd_4547917 2335267397753987987522017 := by
  unfold tailWord_4547917
  simp only [CollatzResearch.WordTrace]
  refine ⟨165876160264680906230682005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110584106843120604153788003 165876160264680906230682005)
  ·
    refine ⟨7775445012406917479563219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165876160264680906230682005 7775445012406917479563219)
    ·
      refine ⟨11663167518610376219344829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775445012406917479563219 11663167518610376219344829)
      ·
        refine ⟨4373687819478891082254311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11663167518610376219344829 4373687819478891082254311)
        ·
          refine ⟨6560531729218336623381467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373687819478891082254311 6560531729218336623381467)
          ·
            refine ⟨9840797593827504935072201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560531729218336623381467 9840797593827504935072201)
            ·
              refine ⟨7380598195370628701304151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840797593827504935072201 7380598195370628701304151)
              ·
                refine ⟨11070897293055943051956227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7380598195370628701304151 11070897293055943051956227)
                ·
                  refine ⟨16606345939583914577934341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11070897293055943051956227 16606345939583914577934341)
                  ·
                    refine ⟨3113689863671983983362689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16606345939583914577934341 3113689863671983983362689)
                    ·
                      refine ⟨2335267397753987987522017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113689863671983983362689 2335267397753987987522017)
                      ·
                        rfl

theorem cell23_4547917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4547917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547917 prefixEnd_4547917 := by exact prefixLift 4547917
  have htrace : WordTrace (prefixWord ++ tailWord_4547917) baseStart_4547917 baseEnd_4547917 := by
    simpa [prefixWord, tailWord_4547917, baseEnd_4547917] using wordTrace_append hprefix tailTrace_4547917
  have hstable : (prefixWord ++ tailWord_4547917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547917).length < 2 ^ (prefixWord ++ tailWord_4547917).sum := by decide
  have hdescent : baseEnd_4547917 < baseStart_4547917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547936 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_4547936 : Nat := 118140960795 + 4547936 * 2 ^ 59
def prefixEnd_4547936 : Nat := 4983230072969 + 3 ^ 40 * 4547936 * 2
def baseEnd_4547936 : Nat := 778425717962141137728143

theorem tailTrace_4547936 : CollatzResearch.WordTrace tailWord_4547936 prefixEnd_4547936 778425717962141137728143 := by
  unfold tailWord_4547936
  simp only [CollatzResearch.WordTrace]
  refine ⟨82938426625806036237811831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110584568834408048317082441 82938426625806036237811831)
  ·
    refine ⟨124407639938709054356717747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82938426625806036237811831 124407639938709054356717747)
    ·
      refine ⟨186611459908063581535076621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124407639938709054356717747 186611459908063581535076621)
      ·
        refine ⟨69979297465523843075653733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186611459908063581535076621 69979297465523843075653733)
        ·
          refine ⟨13121118274785720576685075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69979297465523843075653733 13121118274785720576685075)
          ·
            refine ⟨19681677412178580865027613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13121118274785720576685075 19681677412178580865027613)
            ·
              refine ⟨7380629029566967824385355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19681677412178580865027613 7380629029566967824385355)
              ·
                refine ⟨11070943544350451736578033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7380629029566967824385355 11070943544350451736578033)
                ·
                  refine ⟨8303207658262838802433525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11070943544350451736578033 8303207658262838802433525)
                  ·
                    refine ⟨778425717962141137728143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8303207658262838802433525 778425717962141137728143)
                    ·
                      rfl

theorem cell23_4547936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_4547936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547936 prefixEnd_4547936 := by exact prefixLift 4547936
  have htrace : WordTrace (prefixWord ++ tailWord_4547936) baseStart_4547936 baseEnd_4547936 := by
    simpa [prefixWord, tailWord_4547936, baseEnd_4547936] using wordTrace_append hprefix tailTrace_4547936
  have hstable : (prefixWord ++ tailWord_4547936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547936).length < 2 ^ (prefixWord ++ tailWord_4547936).sum := by decide
  have hdescent : baseEnd_4547936 < baseStart_4547936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547976 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4547976 : Nat := 118140960795 + 4547976 * 2 ^ 59
def prefixEnd_4547976 : Nat := 4983230072969 + 3 ^ 40 * 4547976 * 2
def baseEnd_4547976 : Nat := 2335297693112603256684245

theorem tailTrace_4547976 : CollatzResearch.WordTrace tailWord_4547976 prefixEnd_4547976 2335297693112603256684245 := by
  unfold tailWord_4547976
  simp only [CollatzResearch.WordTrace]
  refine ⟨82939156085733579653539891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110585541447644772871386521 82939156085733579653539891)
  ·
    refine ⟨124408734128600369480309837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82939156085733579653539891 124408734128600369480309837)
    ·
      refine ⟨46653275298225138555116189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124408734128600369480309837 46653275298225138555116189)
      ·
        refine ⟨17494978236834426958168571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46653275298225138555116189 17494978236834426958168571)
        ·
          refine ⟨26242467355251640437252857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17494978236834426958168571 26242467355251640437252857)
          ·
            refine ⟨19681850516438730327939643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26242467355251640437252857 19681850516438730327939643)
            ·
              refine ⟨29522775774658095491909465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19681850516438730327939643 29522775774658095491909465)
              ·
                refine ⟨22142081830993571618932099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29522775774658095491909465 22142081830993571618932099)
                ·
                  refine ⟨33213122746490357428398149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22142081830993571618932099 33213122746490357428398149)
                  ·
                    refine ⟨6227460514966942017824653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33213122746490357428398149 6227460514966942017824653)
                    ·
                      refine ⟨2335297693112603256684245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227460514966942017824653 2335297693112603256684245)
                      ·
                        rfl

theorem cell23_4547976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4547976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547976 prefixEnd_4547976 := by exact prefixLift 4547976
  have htrace : WordTrace (prefixWord ++ tailWord_4547976) baseStart_4547976 baseEnd_4547976 := by
    simpa [prefixWord, tailWord_4547976, baseEnd_4547976] using wordTrace_append hprefix tailTrace_4547976
  have hstable : (prefixWord ++ tailWord_4547976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547976).length < 2 ^ (prefixWord ++ tailWord_4547976).sum := by decide
  have hdescent : baseEnd_4547976 < baseStart_4547976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548009 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_4548009 : Nat := 118140960795 + 4548009 * 2 ^ 59
def prefixEnd_4548009 : Nat := 4983230072969 + 3 ^ 40 * 4548009 * 2
def baseEnd_4548009 : Nat := 778438212658067209190531

theorem tailTrace_4548009 : CollatzResearch.WordTrace tailWord_4548009 prefixEnd_4548009 778438212658067209190531 := by
  unfold tailWord_4548009
  simp only [CollatzResearch.WordTrace]
  refine ⟨165879515780347605943031081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110586343853565070628687387 165879515780347605943031081)
  ·
    refine ⟨124409636835260704457273311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165879515780347605943031081 124409636835260704457273311)
    ·
      refine ⟨186614455252891056685909967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124409636835260704457273311 186614455252891056685909967)
      ·
        refine ⟨279921682879336585028864951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186614455252891056685909967 279921682879336585028864951)
        ·
          refine ⟨419882524319004877543297427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279921682879336585028864951 419882524319004877543297427)
          ·
            refine ⟨629823786478507316314946141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419882524319004877543297427 629823786478507316314946141)
            ·
              refine ⟨236183919929440243618104803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 629823786478507316314946141 236183919929440243618104803)
              ·
                refine ⟨354275879894160365427157205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236183919929440243618104803 354275879894160365427157205)
                ·
                  refine ⟨8303340935019383564698997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 354275879894160365427157205 8303340935019383564698997)
                  ·
                    refine ⟨778438212658067209190531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8303340935019383564698997 778438212658067209190531)
                    ·
                      rfl

theorem cell23_4548009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_4548009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548009 prefixEnd_4548009 := by exact prefixLift 4548009
  have htrace : WordTrace (prefixWord ++ tailWord_4548009) baseStart_4548009 baseEnd_4548009 := by
    simpa [prefixWord, tailWord_4548009, baseEnd_4548009] using wordTrace_append hprefix tailTrace_4548009
  have hstable : (prefixWord ++ tailWord_4548009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548009).length < 2 ^ (prefixWord ++ tailWord_4548009).sum := by decide
  have hdescent : baseEnd_4548009 < baseStart_4548009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548016 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2]
def baseStart_4548016 : Nat := 118140960795 + 4548016 * 2 ^ 59
def prefixEnd_4548016 : Nat := 4983230072969 + 3 ^ 40 * 4548016 * 2
def baseEnd_4548016 : Nat := 2335318232338783100184061

theorem tailTrace_4548016 : CollatzResearch.WordTrace tailWord_4548016 prefixEnd_4548016 2335318232338783100184061 := by
  unfold tailWord_4548016
  simp only [CollatzResearch.WordTrace]
  refine ⟨82939885545661123069267951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110586514060881497425690601 82939885545661123069267951)
  ·
    refine ⟨124409828318491684603901927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82939885545661123069267951 124409828318491684603901927)
    ·
      refine ⟨186614742477737526905852891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124409828318491684603901927 186614742477737526905852891)
      ·
        refine ⟨279922113716606290358779337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186614742477737526905852891 279922113716606290358779337)
        ·
          refine ⟨209941585287454717769084503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279922113716606290358779337 209941585287454717769084503)
          ·
            refine ⟨314912377931182076653626755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209941585287454717769084503 314912377931182076653626755)
            ·
              refine ⟨472368566896773114980440133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314912377931182076653626755 472368566896773114980440133)
              ·
                refine ⟨88569106293144959058832525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472368566896773114980440133 88569106293144959058832525)
                ·
                  refine ⟨33213414859929359647062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88569106293144959058832525 33213414859929359647062197)
                  ·
                    refine ⟨3113757643118377466912081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33213414859929359647062197 3113757643118377466912081)
                    ·
                      refine ⟨2335318232338783100184061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113757643118377466912081 2335318232338783100184061)
                      ·
                        rfl

theorem cell23_4548016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 5, 2].length) (baseStart_4548016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548016 prefixEnd_4548016 := by exact prefixLift 4548016
  have htrace : WordTrace (prefixWord ++ tailWord_4548016) baseStart_4548016 baseEnd_4548016 := by
    simpa [prefixWord, tailWord_4548016, baseEnd_4548016] using wordTrace_append hprefix tailTrace_4548016
  have hstable : (prefixWord ++ tailWord_4548016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548016).length < 2 ^ (prefixWord ++ tailWord_4548016).sum := by decide
  have hdescent : baseEnd_4548016 < baseStart_4548016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548049 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_4548049 : Nat := 118140960795 + 4548049 * 2 ^ 59
def prefixEnd_4548049 : Nat := 4983230072969 + 3 ^ 40 * 4548049 * 2
def baseEnd_4548049 : Nat := 2335335177200381471071409

theorem tailTrace_4548049 : CollatzResearch.WordTrace tailWord_4548049 prefixEnd_4548049 2335335177200381471071409 := by
  unfold tailWord_4548049
  simp only [CollatzResearch.WordTrace]
  refine ⟨165880974700202692774487201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110587316466801795182991467 165880974700202692774487201)
  ·
    refine ⟨124410731025152019580865401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165880974700202692774487201 124410731025152019580865401)
    ·
      refine ⟨93308048268864014685649051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124410731025152019580865401 93308048268864014685649051)
      ·
        refine ⟨139962072403296022028473577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93308048268864014685649051 139962072403296022028473577)
        ·
          refine ⟨104971554302472016521355183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139962072403296022028473577 104971554302472016521355183)
          ·
            refine ⟨157457331453708024782032775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104971554302472016521355183 157457331453708024782032775)
            ·
              refine ⟨236185997180562037173049163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157457331453708024782032775 236185997180562037173049163)
              ·
                refine ⟨354278995770843055759573745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236185997180562037173049163 354278995770843055759573745)
                ·
                  refine ⟨265709246828132291819680309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 354278995770843055759573745 265709246828132291819680309)
                  ·
                    refine ⟨24910241890137402358095029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 265709246828132291819680309 24910241890137402358095029)
                    ·
                      refine ⟨2335335177200381471071409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24910241890137402358095029 2335335177200381471071409)
                      ·
                        rfl

theorem cell23_4548049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_4548049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548049 prefixEnd_4548049 := by exact prefixLift 4548049
  have htrace : WordTrace (prefixWord ++ tailWord_4548049) baseStart_4548049 baseEnd_4548049 := by
    simpa [prefixWord, tailWord_4548049, baseEnd_4548049] using wordTrace_append hprefix tailTrace_4548049
  have hstable : (prefixWord ++ tailWord_4548049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548049).length < 2 ^ (prefixWord ++ tailWord_4548049).sum := by decide
  have hdescent : baseEnd_4548049 < baseStart_4548049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548056 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_4548056 : Nat := 118140960795 + 4548056 * 2 ^ 59
def prefixEnd_4548056 : Nat := 4983230072969 + 3 ^ 40 * 4548056 * 2
def baseEnd_4548056 : Nat := 778446257188320981227959

theorem tailTrace_4548056 : CollatzResearch.WordTrace tailWord_4548056 prefixEnd_4548056 778446257188320981227959 := by
  unfold tailWord_4548056
  simp only [CollatzResearch.WordTrace]
  refine ⟨82940615005588666484996011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110587486674118221979994681 82940615005588666484996011)
  ·
    refine ⟨124410922508382999727494017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82940615005588666484996011 124410922508382999727494017)
    ·
      refine ⟨93308191881287249795620513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124410922508382999727494017 93308191881287249795620513)
      ·
        refine ⟨69981143910965437346715385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93308191881287249795620513 69981143910965437346715385)
        ·
          refine ⟨52485857933224078010036539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69981143910965437346715385 52485857933224078010036539)
          ·
            refine ⟨78728786899836117015054809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52485857933224078010036539 78728786899836117015054809)
            ·
              refine ⟨59046590174877087761291107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78728786899836117015054809 59046590174877087761291107)
              ·
                refine ⟨88569885262315631641936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59046590174877087761291107 88569885262315631641936661)
                ·
                  refine ⟨4151713371671045233215781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88569885262315631641936661 4151713371671045233215781)
                  ·
                    refine ⟨778446257188320981227959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151713371671045233215781 778446257188320981227959)
                    ·
                      rfl

theorem cell23_4548056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_4548056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548056 prefixEnd_4548056 := by exact prefixLift 4548056
  have htrace : WordTrace (prefixWord ++ tailWord_4548056) baseStart_4548056 baseEnd_4548056 := by
    simpa [prefixWord, tailWord_4548056, baseEnd_4548056] using wordTrace_append hprefix tailTrace_4548056
  have hstable : (prefixWord ++ tailWord_4548056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548056).length < 2 ^ (prefixWord ++ tailWord_4548056).sum := by decide
  have hdescent : baseEnd_4548056 < baseStart_4548056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548093 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_4548093 : Nat := 118140960795 + 4548093 * 2 ^ 59
def prefixEnd_4548093 : Nat := 4983230072969 + 3 ^ 40 * 4548093 * 2
def baseEnd_4548093 : Nat := 2335357770349179298921207

theorem tailTrace_4548093 : CollatzResearch.WordTrace tailWord_4548093 prefixEnd_4548093 2335357770349179298921207 := by
  unfold tailWord_4548093
  simp only [CollatzResearch.WordTrace]
  refine ⟨165882579512043288289088933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110588386341362192192725955 165882579512043288289088933)
  ·
    refine ⟨31102983658508116554204175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165882579512043288289088933 31102983658508116554204175)
    ·
      refine ⟨46654475487762174831306263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31102983658508116554204175 46654475487762174831306263)
      ·
        refine ⟨69981713231643262246959395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46654475487762174831306263 69981713231643262246959395)
        ·
          refine ⟨104972569847464893370439093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69981713231643262246959395 104972569847464893370439093)
          ·
            refine ⟨9841178423199833753478665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104972569847464893370439093 9841178423199833753478665)
            ·
              refine ⟨7380883817399875315108999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9841178423199833753478665 7380883817399875315108999)
              ·
                refine ⟨11071325726099812972663499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7380883817399875315108999 11071325726099812972663499)
                ·
                  refine ⟨16606988589149719458995249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11071325726099812972663499 16606988589149719458995249)
                  ·
                    refine ⟨12455241441862289594246437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16606988589149719458995249 12455241441862289594246437)
                    ·
                      refine ⟨2335357770349179298921207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12455241441862289594246437 2335357770349179298921207)
                      ·
                        rfl

theorem cell23_4548093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_4548093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548093 prefixEnd_4548093 := by exact prefixLift 4548093
  have htrace : WordTrace (prefixWord ++ tailWord_4548093) baseStart_4548093 baseEnd_4548093 := by
    simpa [prefixWord, tailWord_4548093, baseEnd_4548093] using wordTrace_append hprefix tailTrace_4548093
  have hstable : (prefixWord ++ tailWord_4548093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548093).length < 2 ^ (prefixWord ++ tailWord_4548093).sum := by decide
  have hdescent : baseEnd_4548093 < baseStart_4548093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548097 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_4548097 : Nat := 118140960795 + 4548097 * 2 ^ 59
def prefixEnd_4548097 : Nat := 4983230072969 + 3 ^ 40 * 4548097 * 2
def baseEnd_4548097 : Nat := 2335359824271797283271189

theorem tailTrace_4548097 : CollatzResearch.WordTrace tailWord_4548097 prefixEnd_4548097 2335359824271797283271189 := by
  unfold tailWord_4548097
  simp only [CollatzResearch.WordTrace]
  refine ⟨165882725404028796972234545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110588483602685864648156363 165882725404028796972234545)
  ·
    refine ⟨124412044053021597729175909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165882725404028796972234545 124412044053021597729175909)
    ·
      refine ⟨23327258259941549574220483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124412044053021597729175909 23327258259941549574220483)
      ·
        refine ⟨34990887389912324361330725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23327258259941549574220483 34990887389912324361330725)
        ·
          refine ⟨6560791385608560817749511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34990887389912324361330725 6560791385608560817749511)
          ·
            refine ⟨9841187078412841226624267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560791385608560817749511 9841187078412841226624267)
            ·
              refine ⟨14761780617619261839936401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841187078412841226624267 14761780617619261839936401)
              ·
                refine ⟨11071335463214446379952301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14761780617619261839936401 11071335463214446379952301)
                ·
                  refine ⟨4151750798705417392482113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11071335463214446379952301 4151750798705417392482113)
                  ·
                    refine ⟨3113813099029063044361585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151750798705417392482113 3113813099029063044361585)
                    ·
                      refine ⟨2335359824271797283271189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113813099029063044361585 2335359824271797283271189)
                      ·
                        rfl

theorem cell23_4548097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_4548097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548097 prefixEnd_4548097 := by exact prefixLift 4548097
  have htrace : WordTrace (prefixWord ++ tailWord_4548097) baseStart_4548097 baseEnd_4548097 := by
    simpa [prefixWord, tailWord_4548097, baseEnd_4548097] using wordTrace_append hprefix tailTrace_4548097
  have hstable : (prefixWord ++ tailWord_4548097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548097).length < 2 ^ (prefixWord ++ tailWord_4548097).sum := by decide
  have hdescent : baseEnd_4548097 < baseStart_4548097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548103 : List Nat := [1, 1, 4, 3, 2, 2, 3, 7]
def baseStart_4548103 : Nat := 118140960795 + 4548103 * 2 ^ 59
def prefixEnd_4548103 : Nat := 4983230072969 + 3 ^ 40 * 4548103 * 2
def baseEnd_4548103 : Nat := 86494922413174972585043

theorem tailTrace_4548103 : CollatzResearch.WordTrace tailWord_4548103 prefixEnd_4548103 86494922413174972585043 := by
  unfold tailWord_4548103
  simp only [CollatzResearch.WordTrace]
  refine ⟨165882944242007059996952963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110588629494671373331301975 165882944242007059996952963)
  ·
    refine ⟨248824416363010589995429445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165882944242007059996952963 248824416363010589995429445)
    ·
      refine ⟨46654578068064485624143021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248824416363010589995429445 46654578068064485624143021)
      ·
        refine ⟨17495466775524182109053633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46654578068064485624143021 17495466775524182109053633)
        ·
          refine ⟨13121600081643136581790225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17495466775524182109053633 13121600081643136581790225)
          ·
            refine ⟨9841200061232352436342669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13121600081643136581790225 9841200061232352436342669)
            ·
              refine ⟨3690450022962132163628501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9841200061232352436342669 3690450022962132163628501)
              ·
                refine ⟨86494922413174972585043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3690450022962132163628501 86494922413174972585043)
                ·
                  rfl

theorem cell23_4548103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 7].length) (baseStart_4548103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548103 prefixEnd_4548103 := by exact prefixLift 4548103
  have htrace : WordTrace (prefixWord ++ tailWord_4548103) baseStart_4548103 baseEnd_4548103 := by
    simpa [prefixWord, tailWord_4548103, baseEnd_4548103] using wordTrace_append hprefix tailTrace_4548103
  have hstable : (prefixWord ++ tailWord_4548103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548103).length < 2 ^ (prefixWord ++ tailWord_4548103).sum := by decide
  have hdescent : baseEnd_4548103 < baseStart_4548103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548113 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_4548113 : Nat := 118140960795 + 4548113 * 2 ^ 59
def prefixEnd_4548113 : Nat := 4983230072969 + 3 ^ 40 * 4548113 * 2
def baseEnd_4548113 : Nat := 2335368039962269220671115

theorem tailTrace_4548113 : CollatzResearch.WordTrace tailWord_4548113 prefixEnd_4548113 2335368039962269220671115 := by
  unfold tailWord_4548113
  simp only [CollatzResearch.WordTrace]
  refine ⟨165883308971970831704816993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110588872647980554469877995 165883308971970831704816993)
  ·
    refine ⟨124412481728978123778612745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165883308971970831704816993 124412481728978123778612745)
    ·
      refine ⟨93309361296733592833959559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124412481728978123778612745 93309361296733592833959559)
      ·
        refine ⟨139964041945100389250939339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93309361296733592833959559 139964041945100389250939339)
        ·
          refine ⟨209946062917650583876409009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139964041945100389250939339 209946062917650583876409009)
          ·
            refine ⟨157459547188237937907306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209946062917650583876409009 157459547188237937907306757)
            ·
              refine ⟨29523665097794613357620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157459547188237937907306757 29523665097794613357620017)
              ·
                refine ⟨22142748823345960018215013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29523665097794613357620017 22142748823345960018215013)
                ·
                  refine ⟨4151765404377367503415315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22142748823345960018215013 4151765404377367503415315)
                  ·
                    refine ⟨6227648106566051255122973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4151765404377367503415315 6227648106566051255122973)
                    ·
                      refine ⟨2335368039962269220671115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227648106566051255122973 2335368039962269220671115)
                      ·
                        rfl

theorem cell23_4548113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_4548113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548113 prefixEnd_4548113 := by exact prefixLift 4548113
  have htrace : WordTrace (prefixWord ++ tailWord_4548113) baseStart_4548113 baseEnd_4548113 := by
    simpa [prefixWord, tailWord_4548113, baseEnd_4548113] using wordTrace_append hprefix tailTrace_4548113
  have hstable : (prefixWord ++ tailWord_4548113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548113).length < 2 ^ (prefixWord ++ tailWord_4548113).sum := by decide
  have hdescent : baseEnd_4548113 < baseStart_4548113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548117 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_4548117 : Nat := 118140960795 + 4548117 * 2 ^ 59
def prefixEnd_4548117 : Nat := 4983230072969 + 3 ^ 40 * 4548117 * 2
def baseEnd_4548117 : Nat := 2335370093884887205021097

theorem tailTrace_4548117 : CollatzResearch.WordTrace tailWord_4548117 prefixEnd_4548117 2335370093884887205021097 := by
  unfold tailWord_4548117
  simp only [CollatzResearch.WordTrace]
  refine ⟨165883454863956340387962605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110588969909304226925308403 165883454863956340387962605)
  ·
    refine ⟨62206295573983627645485977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165883454863956340387962605 62206295573983627645485977)
    ·
      refine ⟨46654721680487720734114483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62206295573983627645485977 46654721680487720734114483)
      ·
        refine ⟨69982082520731581101171725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46654721680487720734114483 69982082520731581101171725)
        ·
          refine ⟨26243280945274342912939397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69982082520731581101171725 26243280945274342912939397)
          ·
            refine ⟨4920615177238939296176137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26243280945274342912939397 4920615177238939296176137)
            ·
              refine ⟨3690461382929204472132103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920615177238939296176137 3690461382929204472132103)
              ·
                refine ⟨5535692074393806708198155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690461382929204472132103 5535692074393806708198155)
                ·
                  refine ⟨8303538111590710062297233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535692074393806708198155 8303538111590710062297233)
                  ·
                    refine ⟨6227653583693032546722925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8303538111590710062297233 6227653583693032546722925)
                    ·
                      refine ⟨2335370093884887205021097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227653583693032546722925 2335370093884887205021097)
                      ·
                        rfl

theorem cell23_4548117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_4548117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548117 prefixEnd_4548117 := by exact prefixLift 4548117
  have htrace : WordTrace (prefixWord ++ tailWord_4548117) baseStart_4548117 baseEnd_4548117 := by
    simpa [prefixWord, tailWord_4548117, baseEnd_4548117] using wordTrace_append hprefix tailTrace_4548117
  have hstable : (prefixWord ++ tailWord_4548117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548117).length < 2 ^ (prefixWord ++ tailWord_4548117).sum := by decide
  have hdescent : baseEnd_4548117 < baseStart_4548117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548147 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 2, 1, 3]
def baseStart_4548147 : Nat := 118140960795 + 4548147 * 2 ^ 59
def prefixEnd_4548147 : Nat := 4983230072969 + 3 ^ 40 * 4548147 * 2
def baseEnd_4548147 : Nat := 2335385498304522087645959

theorem tailTrace_4548147 : CollatzResearch.WordTrace tailWord_4548147 prefixEnd_4548147 2335385498304522087645959 := by
  unfold tailWord_4548147
  simp only [CollatzResearch.WordTrace]
  refine ⟨165884549053847655511554695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110589699369231770341036463 165884549053847655511554695)
  ·
    refine ⟨248826823580771483267332043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165884549053847655511554695 248826823580771483267332043)
    ·
      refine ⟨373240235371157224900998065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248826823580771483267332043 373240235371157224900998065)
      ·
        refine ⟨279930176528367918675748549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373240235371157224900998065 279930176528367918675748549)
        ·
          refine ⟨52486908099068984751702853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279930176528367918675748549 52486908099068984751702853)
          ·
            refine ⟨9841295268575434640944285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52486908099068984751702853 9841295268575434640944285)
            ·
              refine ⟨3690485725715787990354107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9841295268575434640944285 3690485725715787990354107)
              ·
                refine ⟨5535728588573681985531161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690485725715787990354107 5535728588573681985531161)
                ·
                  refine ⟨4151796441430261489148371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5535728588573681985531161 4151796441430261489148371)
                  ·
                    refine ⟨6227694662145392233722557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4151796441430261489148371 6227694662145392233722557)
                    ·
                      refine ⟨2335385498304522087645959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6227694662145392233722557 2335385498304522087645959)
                      ·
                        rfl

theorem cell23_4548147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 2, 1, 3].length) (baseStart_4548147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548147 prefixEnd_4548147 := by exact prefixLift 4548147
  have htrace : WordTrace (prefixWord ++ tailWord_4548147) baseStart_4548147 baseEnd_4548147 := by
    simpa [prefixWord, tailWord_4548147, baseEnd_4548147] using wordTrace_append hprefix tailTrace_4548147
  have hstable : (prefixWord ++ tailWord_4548147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548147).length < 2 ^ (prefixWord ++ tailWord_4548147).sum := by decide
  have hdescent : baseEnd_4548147 < baseStart_4548147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548170 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_4548170 : Nat := 118140960795 + 4548170 * 2 ^ 59
def prefixEnd_4548170 : Nat := 4983230072969 + 3 ^ 40 * 4548170 * 2
def baseEnd_4548170 : Nat := 2335397308359575497658353

theorem tailTrace_4548170 : CollatzResearch.WordTrace tailWord_4548170 prefixEnd_4548170 2335397308359575497658353 := by
  unfold tailWord_4548170
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471346983191082609910491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110590258621842886959761309 41471346983191082609910491)
  ·
    refine ⟨62207020474786623914865737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41471346983191082609910491 62207020474786623914865737)
    ·
      refine ⟨46655265356089967936149303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62207020474786623914865737 46655265356089967936149303)
      ·
        refine ⟨69982898034134951904223955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46655265356089967936149303 69982898034134951904223955)
        ·
          refine ⟨104974347051202427856335933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69982898034134951904223955 104974347051202427856335933)
          ·
            refine ⟨39365380144200910446125975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104974347051202427856335933 39365380144200910446125975)
            ·
              refine ⟨59048070216301365669188963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39365380144200910446125975 59048070216301365669188963)
              ·
                refine ⟨88572105324452048503783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59048070216301365669188963 88572105324452048503783445)
                ·
                  refine ⟨4151817437083689773614849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88572105324452048503783445 4151817437083689773614849)
                  ·
                    refine ⟨3113863077812767330211137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151817437083689773614849 3113863077812767330211137)
                    ·
                      refine ⟨2335397308359575497658353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113863077812767330211137 2335397308359575497658353)
                      ·
                        rfl

theorem cell23_4548170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_4548170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548170 prefixEnd_4548170 := by exact prefixLift 4548170
  have htrace : WordTrace (prefixWord ++ tailWord_4548170) baseStart_4548170 baseEnd_4548170 := by
    simpa [prefixWord, tailWord_4548170, baseEnd_4548170] using wordTrace_append hprefix tailTrace_4548170
  have hstable : (prefixWord ++ tailWord_4548170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548170).length < 2 ^ (prefixWord ++ tailWord_4548170).sum := by decide
  have hdescent : baseEnd_4548170 < baseStart_4548170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548216 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_4548216 : Nat := 118140960795 + 4548216 * 2 ^ 59
def prefixEnd_4548216 : Nat := 4983230072969 + 3 ^ 40 * 4548216 * 2
def baseEnd_4548216 : Nat := 2335420928469682317683141

theorem tailTrace_4548216 : CollatzResearch.WordTrace tailWord_4548216 prefixEnd_4548216 2335420928469682317683141 := by
  unfold tailWord_4548216
  simp only [CollatzResearch.WordTrace]
  refine ⟨82943532845298840147908251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110591377127065120197211001 82943532845298840147908251)
  ·
    refine ⟨124415299267948260221862377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82943532845298840147908251 124415299267948260221862377)
    ·
      refine ⟨93311474450961195166396783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124415299267948260221862377 93311474450961195166396783)
      ·
        refine ⟨139967211676441792749595175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93311474450961195166396783 139967211676441792749595175)
        ·
          refine ⟨209950817514662689124392763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139967211676441792749595175 209950817514662689124392763)
          ·
            refine ⟨314926226271994033686589145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209950817514662689124392763 314926226271994033686589145)
            ·
              refine ⟨236194669703995525264941859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314926226271994033686589145 236194669703995525264941859)
              ·
                refine ⟨354292004555993287897412789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236194669703995525264941859 354292004555993287897412789)
                ·
                  refine ⟨33214875427124370740382449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354292004555993287897412789 33214875427124370740382449)
                  ·
                    refine ⟨24911156570343278055286837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33214875427124370740382449 24911156570343278055286837)
                    ·
                      refine ⟨2335420928469682317683141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24911156570343278055286837 2335420928469682317683141)
                      ·
                        rfl

theorem cell23_4548216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_4548216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548216 prefixEnd_4548216 := by exact prefixLift 4548216
  have htrace : WordTrace (prefixWord ++ tailWord_4548216) baseStart_4548216 baseEnd_4548216 := by
    simpa [prefixWord, tailWord_4548216, baseEnd_4548216] using wordTrace_append hprefix tailTrace_4548216
  have hstable : (prefixWord ++ tailWord_4548216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548216).length < 2 ^ (prefixWord ++ tailWord_4548216).sum := by decide
  have hdescent : baseEnd_4548216 < baseStart_4548216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548260 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_4548260 : Nat := 118140960795 + 4548260 * 2 ^ 59
def prefixEnd_4548260 : Nat := 4983230072969 + 3 ^ 40 * 4548260 * 2
def baseEnd_4548260 : Nat := 2335443521618480145532939

theorem tailTrace_4548260 : CollatzResearch.WordTrace tailWord_4548260 prefixEnd_4548260 2335443521618480145532939 := by
  unfold tailWord_4548260
  simp only [CollatzResearch.WordTrace]
  refine ⟨82944335251219137905209117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110592447001625517206945489 82944335251219137905209117)
  ·
    refine ⟨31104125719207176714453419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82944335251219137905209117 31104125719207176714453419)
    ·
      refine ⟨46656188578810765071680129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31104125719207176714453419 46656188578810765071680129)
      ·
        refine ⟨34992141434108073803760097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46656188578810765071680129 34992141434108073803760097)
        ·
          refine ⟨26244106075581055352820073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34992141434108073803760097 26244106075581055352820073)
          ·
            refine ⟨19683079556685791514615055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26244106075581055352820073 19683079556685791514615055)
            ·
              refine ⟨29524619335028687271922583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19683079556685791514615055 29524619335028687271922583)
              ·
                refine ⟨44286929002543030907883875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29524619335028687271922583 44286929002543030907883875)
                ·
                  refine ⟨66430393503814546361825813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44286929002543030907883875 66430393503814546361825813)
                  ·
                    refine ⟨3113924695491306860710585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66430393503814546361825813 3113924695491306860710585)
                    ·
                      refine ⟨2335443521618480145532939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113924695491306860710585 2335443521618480145532939)
                      ·
                        rfl

theorem cell23_4548260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_4548260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548260 prefixEnd_4548260 := by exact prefixLift 4548260
  have htrace : WordTrace (prefixWord ++ tailWord_4548260) baseStart_4548260 baseEnd_4548260 := by
    simpa [prefixWord, tailWord_4548260, baseEnd_4548260] using wordTrace_append hprefix tailTrace_4548260
  have hstable : (prefixWord ++ tailWord_4548260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548260).length < 2 ^ (prefixWord ++ tailWord_4548260).sum := by decide
  have hdescent : baseEnd_4548260 < baseStart_4548260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548287 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 1, 4]
def baseStart_4548287 : Nat := 118140960795 + 4548287 * 2 ^ 59
def prefixEnd_4548287 : Nat := 4983230072969 + 3 ^ 40 * 4548287 * 2
def baseEnd_4548287 : Nat := 778485795198717179965105

theorem tailTrace_4548287 : CollatzResearch.WordTrace tailWord_4548287 prefixEnd_4548287 778485795198717179965105 := by
  unfold tailWord_4548287
  simp only [CollatzResearch.WordTrace]
  refine ⟨165889655273340459421651115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110593103515560306281100743 165889655273340459421651115)
  ·
    refine ⟨248834482910010689132476673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165889655273340459421651115 248834482910010689132476673)
    ·
      refine ⟨186625862182508016849357505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248834482910010689132476673 186625862182508016849357505)
      ·
        refine ⟨139969396636881012637018129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186625862182508016849357505 139969396636881012637018129)
        ·
          refine ⟨104977047477660759477763597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139969396636881012637018129 104977047477660759477763597)
          ·
            refine ⟨39366392804122784804161349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104977047477660759477763597 39366392804122784804161349)
            ·
              refine ⟨7381198650773022150780253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39366392804122784804161349 7381198650773022150780253)
              ·
                refine ⟨2767949494039883306542595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7381198650773022150780253 2767949494039883306542595)
                ·
                  refine ⟨4151924241059824959813893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767949494039883306542595 4151924241059824959813893)
                  ·
                    refine ⟨778485795198717179965105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151924241059824959813893 778485795198717179965105)
                    ·
                      rfl

theorem cell23_4548287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_4548287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548287 prefixEnd_4548287 := by exact prefixLift 4548287
  have htrace : WordTrace (prefixWord ++ tailWord_4548287) baseStart_4548287 baseEnd_4548287 := by
    simpa [prefixWord, tailWord_4548287, baseEnd_4548287] using wordTrace_append hprefix tailTrace_4548287
  have hstable : (prefixWord ++ tailWord_4548287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548287).length < 2 ^ (prefixWord ++ tailWord_4548287).sum := by decide
  have hdescent : baseEnd_4548287 < baseStart_4548287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548300 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 8]
def baseStart_4548300 : Nat := 118140960795 + 4548300 * 2 ^ 59
def prefixEnd_4548300 : Nat := 4983230072969 + 3 ^ 40 * 4548300 * 2
def baseEnd_4548300 : Nat := 259496006760517776559195

theorem tailTrace_4548300 : CollatzResearch.WordTrace tailWord_4548300 prefixEnd_4548300 259496006760517776559195 := by
  unfold tailWord_4548300
  simp only [CollatzResearch.WordTrace]
  refine ⟨82945064711146681320937177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110593419614862241761249569 82945064711146681320937177)
  ·
    refine ⟨62208798533360010990702883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82945064711146681320937177 62208798533360010990702883)
    ·
      refine ⟨93313197800040016486054325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62208798533360010990702883 93313197800040016486054325)
      ·
        refine ⟨8748112293753751545567593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93313197800040016486054325 8748112293753751545567593)
        ·
          refine ⟨6561084220315313659175695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8748112293753751545567593 6561084220315313659175695)
          ·
            refine ⟨9841626330472970488763543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561084220315313659175695 9841626330472970488763543)
            ·
              refine ⟨14762439495709455733145315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841626330472970488763543 14762439495709455733145315)
              ·
                refine ⟨22143659243564183599717973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14762439495709455733145315 22143659243564183599717973)
                ·
                  refine ⟨259496006760517776559195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22143659243564183599717973 259496006760517776559195)
                  ·
                    rfl

theorem cell23_4548300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_4548300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548300 prefixEnd_4548300 := by exact prefixLift 4548300
  have htrace : WordTrace (prefixWord ++ tailWord_4548300) baseStart_4548300 baseEnd_4548300 := by
    simpa [prefixWord, tailWord_4548300, baseEnd_4548300] using wordTrace_append hprefix tailTrace_4548300
  have hstable : (prefixWord ++ tailWord_4548300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548300).length < 2 ^ (prefixWord ++ tailWord_4548300).sum := by decide
  have hdescent : baseEnd_4548300 < baseStart_4548300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548320 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2]
def baseStart_4548320 : Nat := 118140960795 + 4548320 * 2 ^ 59
def prefixEnd_4548320 : Nat := 4983230072969 + 3 ^ 40 * 4548320 * 2
def baseEnd_4548320 : Nat := 2335474330457749910782663

theorem tailTrace_4548320 : CollatzResearch.WordTrace tailWord_4548320 prefixEnd_4548320 2335474330457749910782663 := by
  unfold tailWord_4548320
  simp only [CollatzResearch.WordTrace]
  refine ⟨82945429441110453028801207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110593905921480604038401609 82945429441110453028801207)
  ·
    refine ⟨124418144161665679543201811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82945429441110453028801207 124418144161665679543201811)
    ·
      refine ⟨186627216242498519314802717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124418144161665679543201811 186627216242498519314802717)
      ·
        refine ⟨69985206090936944743051019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186627216242498519314802717 69985206090936944743051019)
        ·
          refine ⟨104977809136405417114576529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69985206090936944743051019 104977809136405417114576529)
          ·
            refine ⟨78733356852304062835932397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104977809136405417114576529 78733356852304062835932397)
            ·
              refine ⟨29525008819614023563474649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78733356852304062835932397 29525008819614023563474649)
              ·
                refine ⟨22143756614710517672605987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29525008819614023563474649 22143756614710517672605987)
                ·
                  refine ⟨33215634922065776508908981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22143756614710517672605987 33215634922065776508908981)
                  ·
                    refine ⟨3113965773943666547710217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33215634922065776508908981 3113965773943666547710217)
                    ·
                      refine ⟨2335474330457749910782663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113965773943666547710217 2335474330457749910782663)
                      ·
                        rfl

theorem cell23_4548320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_4548320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548320 prefixEnd_4548320 := by exact prefixLift 4548320
  have htrace : WordTrace (prefixWord ++ tailWord_4548320) baseStart_4548320 baseEnd_4548320 := by
    simpa [prefixWord, tailWord_4548320, baseEnd_4548320] using wordTrace_append hprefix tailTrace_4548320
  have hstable : (prefixWord ++ tailWord_4548320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548320).length < 2 ^ (prefixWord ++ tailWord_4548320).sum := by decide
  have hdescent : baseEnd_4548320 < baseStart_4548320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548330 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_4548330 : Nat := 118140960795 + 4548330 * 2 ^ 59
def prefixEnd_4548330 : Nat := 4983230072969 + 3 ^ 40 * 4548330 * 2
def baseEnd_4548330 : Nat := 778493155088098290552539

theorem tailTrace_4548330 : CollatzResearch.WordTrace tailWord_4548330 prefixEnd_4548330 778493155088098290552539 := by
  unfold tailWord_4548330
  simp only [CollatzResearch.WordTrace]
  refine ⟨41472805903046169441366611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110594149074789785176977629 41472805903046169441366611)
  ·
    refine ⟨62209208854569254162049917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41472805903046169441366611 62209208854569254162049917)
    ·
      refine ⟨23328453320463470310768719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62209208854569254162049917 23328453320463470310768719)
      ·
        refine ⟨34992679980695205466153079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23328453320463470310768719 34992679980695205466153079)
        ·
          refine ⟨52489019971042808199229619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34992679980695205466153079 52489019971042808199229619)
          ·
            refine ⟨78733529956564212298844429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52489019971042808199229619 78733529956564212298844429)
            ·
              refine ⟨29525073733711579612066661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78733529956564212298844429 29525073733711579612066661)
              ·
                refine ⟨5535951325070921177262499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29525073733711579612066661 5535951325070921177262499)
                ·
                  refine ⟨8303926987606381765893749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5535951325070921177262499 8303926987606381765893749)
                  ·
                    refine ⟨778493155088098290552539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8303926987606381765893749 778493155088098290552539)
                    ·
                      rfl

theorem cell23_4548330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_4548330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548330 prefixEnd_4548330 := by exact prefixLift 4548330
  have htrace : WordTrace (prefixWord ++ tailWord_4548330) baseStart_4548330 baseEnd_4548330 := by
    simpa [prefixWord, tailWord_4548330, baseEnd_4548330] using wordTrace_append hprefix tailTrace_4548330
  have hstable : (prefixWord ++ tailWord_4548330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548330).length < 2 ^ (prefixWord ++ tailWord_4548330).sum := by decide
  have hdescent : baseEnd_4548330 < baseStart_4548330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548343 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 6]
def baseStart_4548343 : Nat := 118140960795 + 4548343 * 2 ^ 59
def prefixEnd_4548343 : Nat := 4983230072969 + 3 ^ 40 * 4548343 * 2
def baseEnd_4548343 : Nat := 778495380170934440265019

theorem tailTrace_4548343 : CollatzResearch.WordTrace tailWord_4548343 prefixEnd_4548343 778495380170934440265019 := by
  unfold tailWord_4548343
  simp only [CollatzResearch.WordTrace]
  refine ⟨165891697761137580985689683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110594465174091720657126455 165891697761137580985689683)
  ·
    refine ⟨248837546641706371478534525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165891697761137580985689683 248837546641706371478534525)
    ·
      refine ⟨93314079990639889304450447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248837546641706371478534525 93314079990639889304450447)
      ·
        refine ⟨139971119985959833956675671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93314079990639889304450447 139971119985959833956675671)
        ·
          refine ⟨209956679978939750935013507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139971119985959833956675671 209956679978939750935013507)
          ·
            refine ⟨314935019968409626402520261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209956679978939750935013507 314935019968409626402520261)
            ·
              refine ⟨59050316244076804950472549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314935019968409626402520261 59050316244076804950472549)
              ·
                refine ⟨11071934295764400928213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59050316244076804950472549 11071934295764400928213603)
                ·
                  refine ⟨16607901443646601392320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11071934295764400928213603 16607901443646601392320405)
                  ·
                    refine ⟨778495380170934440265019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16607901443646601392320405 778495380170934440265019)
                    ·
                      rfl

theorem cell23_4548343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_4548343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548343 prefixEnd_4548343 := by exact prefixLift 4548343
  have htrace : WordTrace (prefixWord ++ tailWord_4548343) baseStart_4548343 baseEnd_4548343 := by
    simpa [prefixWord, tailWord_4548343, baseEnd_4548343] using wordTrace_append hprefix tailTrace_4548343
  have hstable : (prefixWord ++ tailWord_4548343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548343).length < 2 ^ (prefixWord ++ tailWord_4548343).sum := by decide
  have hdescent : baseEnd_4548343 < baseStart_4548343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548354 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_4548354 : Nat := 118140960795 + 4548354 * 2 ^ 59
def prefixEnd_4548354 : Nat := 4983230072969 + 3 ^ 40 * 4548354 * 2
def baseEnd_4548354 : Nat := 2335491788800002777757507

theorem tailTrace_4548354 : CollatzResearch.WordTrace tailWord_4548354 prefixEnd_4548354 2335491788800002777757507 := by
  unfold tailWord_4548354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41473024741024432466085029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110594732642731819909560077 41473024741024432466085029)
  ·
    refine ⟨7776192138942081087390943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41473024741024432466085029 7776192138942081087390943)
    ·
      refine ⟨11664288208413121631086415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776192138942081087390943 11664288208413121631086415)
      ·
        refine ⟨17496432312619682446629623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11664288208413121631086415 17496432312619682446629623)
        ·
          refine ⟨26244648468929523669944435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17496432312619682446629623 26244648468929523669944435)
          ·
            refine ⟨39366972703394285504916653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26244648468929523669944435 39366972703394285504916653)
            ·
              refine ⟨14762614763772857064343745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39366972703394285504916653 14762614763772857064343745)
              ·
                refine ⟨11071961072829642798257809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14762614763772857064343745 11071961072829642798257809)
                ·
                  refine ⟨8303970804622232098693357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11071961072829642798257809 8303970804622232098693357)
                  ·
                    refine ⟨3113989051733337037010009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8303970804622232098693357 3113989051733337037010009)
                    ·
                      refine ⟨2335491788800002777757507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113989051733337037010009 2335491788800002777757507)
                      ·
                        rfl

theorem cell23_4548354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_4548354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548354 prefixEnd_4548354 := by exact prefixLift 4548354
  have htrace : WordTrace (prefixWord ++ tailWord_4548354) baseStart_4548354 baseEnd_4548354 := by
    simpa [prefixWord, tailWord_4548354, baseEnd_4548354] using wordTrace_append hprefix tailTrace_4548354
  have hstable : (prefixWord ++ tailWord_4548354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548354).length < 2 ^ (prefixWord ++ tailWord_4548354).sum := by decide
  have hdescent : baseEnd_4548354 < baseStart_4548354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548360 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_4548360 : Nat := 118140960795 + 4548360 * 2 ^ 59
def prefixEnd_4548360 : Nat := 4983230072969 + 3 ^ 40 * 4548360 * 2
def baseEnd_4548360 : Nat := 778498289894643251427493

theorem tailTrace_4548360 : CollatzResearch.WordTrace tailWord_4548360 prefixEnd_4548360 778498289894643251427493 := by
  unfold tailWord_4548360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946158901037996444529267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110594878534717328592705689 82946158901037996444529267)
  ·
    refine ⟨124419238351556994666793901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82946158901037996444529267 124419238351556994666793901)
    ·
      refine ⟨46657214381833873000047713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124419238351556994666793901 46657214381833873000047713)
      ·
        refine ⟨34992910786375404750035785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46657214381833873000047713 34992910786375404750035785)
        ·
          refine ⟨26244683089781553562526839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34992910786375404750035785 26244683089781553562526839)
          ·
            refine ⟨39367024634672330343790259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26244683089781553562526839 39367024634672330343790259)
            ·
              refine ⟨59050536952008495515685389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39367024634672330343790259 59050536952008495515685389)
              ·
                refine ⟨22143951357003185818382021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59050536952008495515685389 22143951357003185818382021)
                ·
                  refine ⟨4151990879438097340946629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22143951357003185818382021 4151990879438097340946629)
                  ·
                    refine ⟨778498289894643251427493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151990879438097340946629 778498289894643251427493)
                    ·
                      rfl

theorem cell23_4548360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_4548360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548360 prefixEnd_4548360 := by exact prefixLift 4548360
  have htrace : WordTrace (prefixWord ++ tailWord_4548360) baseStart_4548360 baseEnd_4548360 := by
    simpa [prefixWord, tailWord_4548360, baseEnd_4548360] using wordTrace_append hprefix tailTrace_4548360
  have hstable : (prefixWord ++ tailWord_4548360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548360).length < 2 ^ (prefixWord ++ tailWord_4548360).sum := by decide
  have hdescent : baseEnd_4548360 < baseStart_4548360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548363 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_4548363 : Nat := 118140960795 + 4548363 * 2 ^ 59
def prefixEnd_4548363 : Nat := 4983230072969 + 3 ^ 40 * 4548363 * 2
def baseEnd_4548363 : Nat := 2335496410125893242544965

theorem tailTrace_4548363 : CollatzResearch.WordTrace tailWord_4548363 prefixEnd_4548363 2335496410125893242544965 := by
  unfold tailWord_4548363
  simp only [CollatzResearch.WordTrace]
  refine ⟨165892427221065124401417743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110594951480710082934278495 165892427221065124401417743)
  ·
    refine ⟨248838640831597686602126615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165892427221065124401417743 248838640831597686602126615)
    ·
      refine ⟨373257961247396529903189923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248838640831597686602126615 373257961247396529903189923)
      ·
        refine ⟨559886941871094794854784885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373257961247396529903189923 559886941871094794854784885)
        ·
          refine ⟨52489400800415137017636083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 559886941871094794854784885 52489400800415137017636083)
          ·
            refine ⟨78734101200622705526454125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52489400800415137017636083 78734101200622705526454125)
            ·
              refine ⟨29525287950233514572420297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78734101200622705526454125 29525287950233514572420297)
              ·
                refine ⟨22143965962675135929315223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29525287950233514572420297 22143965962675135929315223)
                ·
                  refine ⟨33215948944012703893972835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22143965962675135929315223 33215948944012703893972835)
                  ·
                    refine ⟨49823923416019055840959253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33215948944012703893972835 49823923416019055840959253)
                    ·
                      refine ⟨2335496410125893242544965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49823923416019055840959253 2335496410125893242544965)
                      ·
                        rfl

theorem cell23_4548363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_4548363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548363 prefixEnd_4548363 := by exact prefixLift 4548363
  have htrace : WordTrace (prefixWord ++ tailWord_4548363) baseStart_4548363 baseEnd_4548363 := by
    simpa [prefixWord, tailWord_4548363, baseEnd_4548363] using wordTrace_append hprefix tailTrace_4548363
  have hstable : (prefixWord ++ tailWord_4548363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548363).length < 2 ^ (prefixWord ++ tailWord_4548363).sum := by decide
  have hdescent : baseEnd_4548363 < baseStart_4548363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548367 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 3, 2, 2]
def baseStart_4548367 : Nat := 118140960795 + 4548367 * 2 ^ 59
def prefixEnd_4548367 : Nat := 4983230072969 + 3 ^ 40 * 4548367 * 2
def baseEnd_4548367 : Nat := 2335498464048511226894947

theorem tailTrace_4548367 : CollatzResearch.WordTrace tailWord_4548367 prefixEnd_4548367 2335498464048511226894947 := by
  unfold tailWord_4548367
  simp only [CollatzResearch.WordTrace]
  refine ⟨165892573113050633084563355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110595048742033755389708903 165892573113050633084563355)
  ·
    refine ⟨248838859669575949626845033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165892573113050633084563355 248838859669575949626845033)
    ·
      refine ⟨186629144752181962220133775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248838859669575949626845033 186629144752181962220133775)
      ·
        refine ⟨279943717128272943330200663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186629144752181962220133775 279943717128272943330200663)
        ·
          refine ⟨419915575692409414995300995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279943717128272943330200663 419915575692409414995300995)
          ·
            refine ⟨629873363538614122492951493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419915575692409414995300995 629873363538614122492951493)
            ·
              refine ⟨118101255663490147967428405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 629873363538614122492951493 118101255663490147967428405)
              ·
                refine ⟨11071992718452201371946413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118101255663490147967428405 11071992718452201371946413)
                ·
                  refine ⟨4151997269419575514479905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11071992718452201371946413 4151997269419575514479905)
                  ·
                    refine ⟨3113997952064681635859929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151997269419575514479905 3113997952064681635859929)
                    ·
                      refine ⟨2335498464048511226894947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113997952064681635859929 2335498464048511226894947)
                      ·
                        rfl

theorem cell23_4548367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2, 2].length) (baseStart_4548367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548367 prefixEnd_4548367 := by exact prefixLift 4548367
  have htrace : WordTrace (prefixWord ++ tailWord_4548367) baseStart_4548367 baseEnd_4548367 := by
    simpa [prefixWord, tailWord_4548367, baseEnd_4548367] using wordTrace_append hprefix tailTrace_4548367
  have hstable : (prefixWord ++ tailWord_4548367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548367).length < 2 ^ (prefixWord ++ tailWord_4548367).sum := by decide
  have hdescent : baseEnd_4548367 < baseStart_4548367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548373 : List Nat := [1, 3, 2, 1, 2, 3, 1, 10]
def baseStart_4548373 : Nat := 118140960795 + 4548373 * 2 ^ 59
def prefixEnd_4548373 : Nat := 4983230072969 + 3 ^ 40 * 4548373 * 2
def baseEnd_4548373 : Nat := 86500057219719933459997

theorem tailTrace_4548373 : CollatzResearch.WordTrace tailWord_4548373 prefixEnd_4548373 86500057219719933459997 := by
  unfold tailWord_4548373
  simp only [CollatzResearch.WordTrace]
  refine ⟨165892791951028896109281773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110595194634019264072854515 165892791951028896109281773)
  ·
    refine ⟨62209796981635836040980665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165892791951028896109281773 62209796981635836040980665)
    ·
      refine ⟨46657347736226877030735499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62209796981635836040980665 46657347736226877030735499)
      ·
        refine ⟨69986021604340315546103249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46657347736226877030735499 69986021604340315546103249)
        ·
          refine ⟨52489516203255236659577437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69986021604340315546103249 52489516203255236659577437)
          ·
            refine ⟨19683568576220713747341539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52489516203255236659577437 19683568576220713747341539)
            ·
              refine ⟨29525352864331070621012309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19683568576220713747341539 29525352864331070621012309)
              ·
                refine ⟨86500057219719933459997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29525352864331070621012309 86500057219719933459997)
                ·
                  rfl

theorem cell23_4548373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 10].length) (baseStart_4548373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548373 prefixEnd_4548373 := by exact prefixLift 4548373
  have htrace : WordTrace (prefixWord ++ tailWord_4548373) baseStart_4548373 baseEnd_4548373 := by
    simpa [prefixWord, tailWord_4548373, baseEnd_4548373] using wordTrace_append hprefix tailTrace_4548373
  have hstable : (prefixWord ++ tailWord_4548373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548373).length < 2 ^ (prefixWord ++ tailWord_4548373).sum := by decide
  have hdescent : baseEnd_4548373 < baseStart_4548373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548380 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4548380 : Nat := 118140960795 + 4548380 * 2 ^ 59
def prefixEnd_4548380 : Nat := 4983230072969 + 3 ^ 40 * 4548380 * 2
def baseEnd_4548380 : Nat := 2335505139297019676032387

theorem tailTrace_4548380 : CollatzResearch.WordTrace tailWord_4548380 prefixEnd_4548380 2335505139297019676032387 := by
  unfold tailWord_4548380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946523631001768152393297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110595364841335690869857729 82946523631001768152393297)
  ·
    refine ⟨62209892723251326114294973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82946523631001768152393297 62209892723251326114294973)
    ·
      refine ⟨23328709771219247292860615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62209892723251326114294973 23328709771219247292860615)
      ·
        refine ⟨34993064656828870939290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23328709771219247292860615 34993064656828870939290923)
        ·
          refine ⟨52489596985243306408936385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34993064656828870939290923 52489596985243306408936385)
          ·
            refine ⟨39367197738932479806702289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52489596985243306408936385 39367197738932479806702289)
            ·
              refine ⟨29525398304199359855026717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39367197738932479806702289 29525398304199359855026717)
              ·
                refine ⟨11072024364074759945635019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29525398304199359855026717 11072024364074759945635019)
                ·
                  refine ⟨16608036546112139918452529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11072024364074759945635019 16608036546112139918452529)
                  ·
                    refine ⟨12456027409584104938839397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16608036546112139918452529 12456027409584104938839397)
                    ·
                      refine ⟨2335505139297019676032387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12456027409584104938839397 2335505139297019676032387)
                      ·
                        rfl

theorem cell23_4548380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4548380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548380 prefixEnd_4548380 := by exact prefixLift 4548380
  have htrace : WordTrace (prefixWord ++ tailWord_4548380) baseStart_4548380 baseEnd_4548380 := by
    simpa [prefixWord, tailWord_4548380, baseEnd_4548380] using wordTrace_append hprefix tailTrace_4548380
  have hstable : (prefixWord ++ tailWord_4548380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548380).length < 2 ^ (prefixWord ++ tailWord_4548380).sum := by decide
  have hdescent : baseEnd_4548380 < baseStart_4548380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548387 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 3]
def baseStart_4548387 : Nat := 118140960795 + 4548387 * 2 ^ 59
def prefixEnd_4548387 : Nat := 4983230072969 + 3 ^ 40 * 4548387 * 2
def baseEnd_4548387 : Nat := 2335508733661601148644855

theorem tailTrace_4548387 : CollatzResearch.WordTrace tailWord_4548387 prefixEnd_4548387 2335508733661601148644855 := by
  unfold tailWord_4548387
  simp only [CollatzResearch.WordTrace]
  refine ⟨165893302572978176500291415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110595535048652117666860943 165893302572978176500291415)
  ·
    refine ⟨248839953859467264750437123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165893302572978176500291415 248839953859467264750437123)
    ·
      refine ⟨373259930789200897125655685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248839953859467264750437123 373259930789200897125655685)
      ·
        refine ⟨69986237022975168211060441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373259930789200897125655685 69986237022975168211060441)
        ·
          refine ⟨52489677767231376158295331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69986237022975168211060441 52489677767231376158295331)
          ·
            refine ⟨78734516650847064237442997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52489677767231376158295331 78734516650847064237442997)
            ·
              refine ⟨7381360936016912272260281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78734516650847064237442997 7381360936016912272260281)
              ·
                refine ⟨5536020702012684204195211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7381360936016912272260281 5536020702012684204195211)
                ·
                  refine ⟨8304031053019026306292817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536020702012684204195211 8304031053019026306292817)
                  ·
                    refine ⟨6228023289764269729719613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8304031053019026306292817 6228023289764269729719613)
                    ·
                      refine ⟨2335508733661601148644855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228023289764269729719613 2335508733661601148644855)
                      ·
                        rfl

theorem cell23_4548387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_4548387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548387 prefixEnd_4548387 := by exact prefixLift 4548387
  have htrace : WordTrace (prefixWord ++ tailWord_4548387) baseStart_4548387 baseEnd_4548387 := by
    simpa [prefixWord, tailWord_4548387, baseEnd_4548387] using wordTrace_append hprefix tailTrace_4548387
  have hstable : (prefixWord ++ tailWord_4548387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548387).length < 2 ^ (prefixWord ++ tailWord_4548387).sum := by decide
  have hdescent : baseEnd_4548387 < baseStart_4548387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548404 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4548404 : Nat := 118140960795 + 4548404 * 2 ^ 59
def prefixEnd_4548404 : Nat := 4983230072969 + 3 ^ 40 * 4548404 * 2
def baseEnd_4548404 : Nat := 2335517462832727582132277

theorem tailTrace_4548404 : CollatzResearch.WordTrace tailWord_4548404 prefixEnd_4548404 2335517462832727582132277 := by
  unfold tailWord_4548404
  simp only [CollatzResearch.WordTrace]
  refine ⟨82946961306958294201830133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110595948409277725602440177 82946961306958294201830133)
  ·
    refine ⟨7776277622527340081421575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82946961306958294201830133 7776277622527340081421575)
    ·
      refine ⟨11664416433791010122132363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776277622527340081421575 11664416433791010122132363)
      ·
        refine ⟨17496624650686515183198545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11664416433791010122132363 17496624650686515183198545)
        ·
          refine ⟨13122468488014886387398909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17496624650686515183198545 13122468488014886387398909)
          ·
            refine ⟨4920925683005582395274591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13122468488014886387398909 4920925683005582395274591)
            ·
              refine ⟨7381388524508373592911887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4920925683005582395274591 7381388524508373592911887)
              ·
                refine ⟨11072082786762560389367831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381388524508373592911887 11072082786762560389367831)
                ·
                  refine ⟨16608124180143840584051747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11072082786762560389367831 16608124180143840584051747)
                  ·
                    refine ⟨24912186270215760876077621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16608124180143840584051747 24912186270215760876077621)
                    ·
                      refine ⟨2335517462832727582132277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24912186270215760876077621 2335517462832727582132277)
                      ·
                        rfl

theorem cell23_4548404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4548404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548404 prefixEnd_4548404 := by exact prefixLift 4548404
  have htrace : WordTrace (prefixWord ++ tailWord_4548404) baseStart_4548404 baseEnd_4548404 := by
    simpa [prefixWord, tailWord_4548404, baseEnd_4548404] using wordTrace_append hprefix tailTrace_4548404
  have hstable : (prefixWord ++ tailWord_4548404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548404).length < 2 ^ (prefixWord ++ tailWord_4548404).sum := by decide
  have hdescent : baseEnd_4548404 < baseStart_4548404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548434 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_4548434 : Nat := 118140960795 + 4548434 * 2 ^ 59
def prefixEnd_4548434 : Nat := 4983230072969 + 3 ^ 40 * 4548434 * 2
def baseEnd_4548434 : Nat := 2335532867252362464757139

theorem tailTrace_4548434 : CollatzResearch.WordTrace tailWord_4548434 prefixEnd_4548434 2335532867252362464757139 := by
  unfold tailWord_4548434
  simp only [CollatzResearch.WordTrace]
  refine ⟨41473754200951975881813089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110596677869205269018168237 41473754200951975881813089)
  ·
    refine ⟨31105315650713981911359817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41473754200951975881813089 31105315650713981911359817)
    ·
      refine ⟨23328986738035486433519863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31105315650713981911359817 23328986738035486433519863)
      ·
        refine ⟨34993480107053229650279795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23328986738035486433519863 34993480107053229650279795)
        ·
          refine ⟨52490220160579844475419693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34993480107053229650279795 52490220160579844475419693)
          ·
            refine ⟨19683832560217441678282385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52490220160579844475419693 19683832560217441678282385)
            ·
              refine ⟨14762874420163081258711789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19683832560217441678282385 14762874420163081258711789)
              ·
                refine ⟨5536077907561155472016921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14762874420163081258711789 5536077907561155472016921)
                ·
                  refine ⟨4152058430670866604012691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5536077907561155472016921 4152058430670866604012691)
                  ·
                    refine ⟨6228087646006299906019037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4152058430670866604012691 6228087646006299906019037)
                    ·
                      refine ⟨2335532867252362464757139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228087646006299906019037 2335532867252362464757139)
                      ·
                        rfl

theorem cell23_4548434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_4548434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548434 prefixEnd_4548434 := by exact prefixLift 4548434
  have htrace : WordTrace (prefixWord ++ tailWord_4548434) baseStart_4548434 baseEnd_4548434 := by
    simpa [prefixWord, tailWord_4548434, baseEnd_4548434] using wordTrace_append hprefix tailTrace_4548434
  have hstable : (prefixWord ++ tailWord_4548434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548434).length < 2 ^ (prefixWord ++ tailWord_4548434).sum := by decide
  have hdescent : baseEnd_4548434 < baseStart_4548434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548461 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4548461 : Nat := 118140960795 + 4548461 * 2 ^ 59
def prefixEnd_4548461 : Nat := 4983230072969 + 3 ^ 40 * 4548461 * 2
def baseEnd_4548461 : Nat := 2335546731230033859119515

theorem tailTrace_4548461 : CollatzResearch.WordTrace tailWord_4548461 prefixEnd_4548461 2335546731230033859119515 := by
  unfold tailWord_4548461
  simp only [CollatzResearch.WordTrace]
  refine ⟨165896001574710087138485237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110597334383140058092323491 165896001574710087138485237)
  ·
    refine ⟨15552750147629070669232991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165896001574710087138485237 15552750147629070669232991)
    ·
      refine ⟨23329125221443606003849487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15552750147629070669232991 23329125221443606003849487)
      ·
        refine ⟨34993687832165409005774231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23329125221443606003849487 34993687832165409005774231)
        ·
          refine ⟨52490531748248113508661347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34993687832165409005774231 52490531748248113508661347)
          ·
            refine ⟨78735797622372170262992021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52490531748248113508661347 78735797622372170262992021)
            ·
              refine ⟨3690740513548695481077751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78735797622372170262992021 3690740513548695481077751)
              ·
                refine ⟨5536110770323043221616627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690740513548695481077751 5536110770323043221616627)
                ·
                  refine ⟨8304166155484564832424941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536110770323043221616627 8304166155484564832424941)
                  ·
                    refine ⟨3114062308306711812159353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8304166155484564832424941 3114062308306711812159353)
                    ·
                      refine ⟨2335546731230033859119515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114062308306711812159353 2335546731230033859119515)
                      ·
                        rfl

theorem cell23_4548461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4548461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548461 prefixEnd_4548461 := by exact prefixLift 4548461
  have htrace : WordTrace (prefixWord ++ tailWord_4548461) baseStart_4548461 baseEnd_4548461 := by
    simpa [prefixWord, tailWord_4548461, baseEnd_4548461] using wordTrace_append hprefix tailTrace_4548461
  have hstable : (prefixWord ++ tailWord_4548461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548461).length < 2 ^ (prefixWord ++ tailWord_4548461).sum := by decide
  have hdescent : baseEnd_4548461 < baseStart_4548461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548480 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 7]
def baseStart_4548480 : Nat := 118140960795 + 4548480 * 2 ^ 59
def prefixEnd_4548480 : Nat := 4983230072969 + 3 ^ 40 * 4548480 * 2
def baseEnd_4548480 : Nat := 259506276373607698309103

theorem tailTrace_4548480 : CollatzResearch.WordTrace tailWord_4548480 prefixEnd_4548480 259506276373607698309103 := by
  unfold tailWord_4548480
  simp only [CollatzResearch.WordTrace]
  refine ⟨82948347280820626691713447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110597796374427502255617929 82948347280820626691713447)
  ·
    refine ⟨124422520921230940037570171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82948347280820626691713447 124422520921230940037570171)
    ·
      refine ⟨186633781381846410056355257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124422520921230940037570171 186633781381846410056355257)
      ·
        refine ⟨139975336036384807542266443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186633781381846410056355257 139975336036384807542266443)
        ·
          refine ⟨209963004054577211313399665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139975336036384807542266443 209963004054577211313399665)
          ·
            refine ⟨157472253040932908485049749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209963004054577211313399665 157472253040932908485049749)
            ·
              refine ⟨7381511861293730085236707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157472253040932908485049749 7381511861293730085236707)
              ·
                refine ⟨11072267791940595127855061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381511861293730085236707 11072267791940595127855061)
                ·
                  refine ⟨259506276373607698309103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11072267791940595127855061 259506276373607698309103)
                  ·
                    rfl

theorem cell23_4548480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_4548480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548480 prefixEnd_4548480 := by exact prefixLift 4548480
  have htrace : WordTrace (prefixWord ++ tailWord_4548480) baseStart_4548480 baseEnd_4548480 := by
    simpa [prefixWord, tailWord_4548480, baseEnd_4548480] using wordTrace_append hprefix tailTrace_4548480
  have hstable : (prefixWord ++ tailWord_4548480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548480).length < 2 ^ (prefixWord ++ tailWord_4548480).sum := by decide
  have hdescent : baseEnd_4548480 < baseStart_4548480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548560 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_4548560 : Nat := 118140960795 + 4548560 * 2 ^ 59
def prefixEnd_4548560 : Nat := 4983230072969 + 3 ^ 40 * 4548560 * 2
def baseEnd_4548560 : Nat := 2335597565814828971781559

theorem tailTrace_4548560 : CollatzResearch.WordTrace tailWord_4548560 prefixEnd_4548560 2335597565814828971781559 := by
  unfold tailWord_4548560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82949806200675713523169567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110599741600900951364226089 82949806200675713523169567)
  ·
    refine ⟨124424709301013570284754351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82949806200675713523169567 124424709301013570284754351)
    ·
      refine ⟨186637063951520355427131527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124424709301013570284754351 186637063951520355427131527)
      ·
        refine ⟨279955595927280533140697291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186637063951520355427131527 279955595927280533140697291)
        ·
          refine ⟨419933393890920799711045937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279955595927280533140697291 419933393890920799711045937)
          ·
            refine ⟨314950045418190599783284453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419933393890920799711045937 314950045418190599783284453)
            ·
              refine ⟨59053133515910737459365835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314950045418190599783284453 59053133515910737459365835)
              ·
                refine ⟨88579700273866106189048753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59053133515910737459365835 88579700273866106189048753)
                ·
                  refine ⟨66434775205399579641786565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88579700273866106189048753 66434775205399579641786565)
                  ·
                    refine ⟨12456520351012421182834981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66434775205399579641786565 12456520351012421182834981)
                    ·
                      refine ⟨2335597565814828971781559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12456520351012421182834981 2335597565814828971781559)
                      ·
                        rfl

theorem cell23_4548560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_4548560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548560 prefixEnd_4548560 := by exact prefixLift 4548560
  have htrace : WordTrace (prefixWord ++ tailWord_4548560) baseStart_4548560 baseEnd_4548560 := by
    simpa [prefixWord, tailWord_4548560, baseEnd_4548560] using wordTrace_append hprefix tailTrace_4548560
  have hstable : (prefixWord ++ tailWord_4548560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548560).length < 2 ^ (prefixWord ++ tailWord_4548560).sum := by decide
  have hdescent : baseEnd_4548560 < baseStart_4548560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548564 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4548564 : Nat := 118140960795 + 4548564 * 2 ^ 59
def prefixEnd_4548564 : Nat := 4983230072969 + 3 ^ 40 * 4548564 * 2
def baseEnd_4548564 : Nat := 2335599619737446956131541

theorem tailTrace_4548564 : CollatzResearch.WordTrace tailWord_4548564 prefixEnd_4548564 2335599619737446956131541 := by
  unfold tailWord_4548564
  simp only [CollatzResearch.WordTrace]
  refine ⟨82949879146668467864742373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110599838862224623819656497 82949879146668467864742373)
  ·
    refine ⟨15553102340000337724639195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82949879146668467864742373 15553102340000337724639195)
    ·
      refine ⟨23329653510000506586958793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15553102340000337724639195 23329653510000506586958793)
      ·
        refine ⟨17497240132500379940219095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23329653510000506586958793 17497240132500379940219095)
        ·
          refine ⟨26245860198750569910328643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17497240132500379940219095 26245860198750569910328643)
          ·
            refine ⟨39368790298125854865492965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26245860198750569910328643 39368790298125854865492965)
            ·
              refine ⟨7381648180898597787279931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39368790298125854865492965 7381648180898597787279931)
              ·
                refine ⟨11072472271347896680919897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381648180898597787279931 11072472271347896680919897)
                ·
                  refine ⟨8304354203510922510689923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11072472271347896680919897 8304354203510922510689923)
                  ·
                    refine ⟨12456531305266383766034885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8304354203510922510689923 12456531305266383766034885)
                    ·
                      refine ⟨2335599619737446956131541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12456531305266383766034885 2335599619737446956131541)
                      ·
                        rfl

theorem cell23_4548564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4548564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548564 prefixEnd_4548564 := by exact prefixLift 4548564
  have htrace : WordTrace (prefixWord ++ tailWord_4548564) baseStart_4548564 baseEnd_4548564 := by
    simpa [prefixWord, tailWord_4548564, baseEnd_4548564] using wordTrace_append hprefix tailTrace_4548564
  have hstable : (prefixWord ++ tailWord_4548564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548564).length < 2 ^ (prefixWord ++ tailWord_4548564).sum := by decide
  have hdescent : baseEnd_4548564 < baseStart_4548564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548618 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_4548618 : Nat := 118140960795 + 4548618 * 2 ^ 59
def prefixEnd_4548618 : Nat := 4983230072969 + 3 ^ 40 * 4548618 * 2
def baseEnd_4548618 : Nat := 2335627347692789744856293

theorem tailTrace_4548618 : CollatzResearch.WordTrace tailWord_4548618 prefixEnd_4548618 2335627347692789744856293 := by
  unfold tailWord_4548618
  simp only [CollatzResearch.WordTrace]
  refine ⟨41475431958785325737987627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110601151890094201967967005 41475431958785325737987627)
  ·
    refine ⟨62213147938177988606981441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41475431958785325737987627 62213147938177988606981441)
    ·
      refine ⟨46659860953633491455236081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62213147938177988606981441 46659860953633491455236081)
      ·
        refine ⟨34994895715225118591427061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46659860953633491455236081 34994895715225118591427061)
        ·
          refine ⟨3280771473302354867946287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34994895715225118591427061 3280771473302354867946287)
          ·
            refine ⟨4921157209953532301919431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280771473302354867946287 4921157209953532301919431)
            ·
              refine ⟨7381735814930298452879147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921157209953532301919431 7381735814930298452879147)
              ·
                refine ⟨11072603722395447679318721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7381735814930298452879147 11072603722395447679318721)
                ·
                  refine ⟨8304452791796585759489041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11072603722395447679318721 8304452791796585759489041)
                  ·
                    refine ⟨6228339593847439319616781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8304452791796585759489041 6228339593847439319616781)
                    ·
                      refine ⟨2335627347692789744856293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228339593847439319616781 2335627347692789744856293)
                      ·
                        rfl

theorem cell23_4548618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_4548618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548618 prefixEnd_4548618 := by exact prefixLift 4548618
  have htrace : WordTrace (prefixWord ++ tailWord_4548618) baseStart_4548618 baseEnd_4548618 := by
    simpa [prefixWord, tailWord_4548618, baseEnd_4548618] using wordTrace_append hprefix tailTrace_4548618
  have hstable : (prefixWord ++ tailWord_4548618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548618).length < 2 ^ (prefixWord ++ tailWord_4548618).sum := by decide
  have hdescent : baseEnd_4548618 < baseStart_4548618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548634 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_4548634 : Nat := 118140960795 + 4548634 * 2 ^ 59
def prefixEnd_4548634 : Nat := 4983230072969 + 3 ^ 40 * 4548634 * 2
def baseEnd_4548634 : Nat := 778545187794420560752073

theorem tailTrace_4548634 : CollatzResearch.WordTrace tailWord_4548634 prefixEnd_4548634 778545187794420560752073 := by
  unfold tailWord_4548634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41475577850770834421133239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110601540935388891789688637 41475577850770834421133239)
  ·
    refine ⟨62213366776156251631699859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41475577850770834421133239 62213366776156251631699859)
    ·
      refine ⟨93320050164234377447549789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62213366776156251631699859 93320050164234377447549789)
      ·
        refine ⟨34995018811587891542831171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93320050164234377447549789 34995018811587891542831171)
        ·
          refine ⟨52492528217381837314246757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34995018811587891542831171 52492528217381837314246757)
          ·
            refine ⟨9842349040759094496421267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52492528217381837314246757 9842349040759094496421267)
            ·
              refine ⟨14763523561138641744631901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9842349040759094496421267 14763523561138641744631901)
              ·
                refine ⟨5536321335426990654236963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14763523561138641744631901 5536321335426990654236963)
                ·
                  refine ⟨8304482003140485981355445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536321335426990654236963 8304482003140485981355445)
                  ·
                    refine ⟨778545187794420560752073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8304482003140485981355445 778545187794420560752073)
                    ·
                      rfl

theorem cell23_4548634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_4548634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548634 prefixEnd_4548634 := by exact prefixLift 4548634
  have htrace : WordTrace (prefixWord ++ tailWord_4548634) baseStart_4548634 baseEnd_4548634 := by
    simpa [prefixWord, tailWord_4548634, baseEnd_4548634] using wordTrace_append hprefix tailTrace_4548634
  have hstable : (prefixWord ++ tailWord_4548634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548634).length < 2 ^ (prefixWord ++ tailWord_4548634).sum := by decide
  have hdescent : baseEnd_4548634 < baseStart_4548634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548657 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4548657 : Nat := 118140960795 + 4548657 * 2 ^ 59
def prefixEnd_4548657 : Nat := 4983230072969 + 3 ^ 40 * 4548657 * 2
def baseEnd_4548657 : Nat := 2335647373438315092268613

theorem tailTrace_4548657 : CollatzResearch.WordTrace tailWord_4548657 prefixEnd_4548657 2335647373438315092268613 := by
  unfold tailWord_4548657
  simp only [CollatzResearch.WordTrace]
  refine ⟨165903150282000012612620225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110602100188000008408413483 165903150282000012612620225)
  ·
    refine ⟨124427362711500009459465169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165903150282000012612620225 124427362711500009459465169)
    ·
      refine ⟨93320522033625007094598877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124427362711500009459465169 93320522033625007094598877)
      ·
        refine ⟨34995195762609377660474579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93320522033625007094598877 34995195762609377660474579)
        ·
          refine ⟨52492793643914066490711869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34995195762609377660474579 52492793643914066490711869)
          ·
            refine ⟨19684797616467774934016951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52492793643914066490711869 19684797616467774934016951)
            ·
              refine ⟨29527196424701662401025427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19684797616467774934016951 29527196424701662401025427)
              ·
                refine ⟨44290794637052493601538141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29527196424701662401025427 44290794637052493601538141)
                ·
                  refine ⟨16609047988894685100576803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44290794637052493601538141 16609047988894685100576803)
                  ·
                    refine ⟨24913571983342027650865205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16609047988894685100576803 24913571983342027650865205)
                    ·
                      refine ⟨2335647373438315092268613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24913571983342027650865205 2335647373438315092268613)
                      ·
                        rfl

theorem cell23_4548657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4548657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548657 prefixEnd_4548657 := by exact prefixLift 4548657
  have htrace : WordTrace (prefixWord ++ tailWord_4548657) baseStart_4548657 baseEnd_4548657 := by
    simpa [prefixWord, tailWord_4548657, baseEnd_4548657] using wordTrace_append hprefix tailTrace_4548657
  have hstable : (prefixWord ++ tailWord_4548657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548657).length < 2 ^ (prefixWord ++ tailWord_4548657).sum := by decide
  have hdescent : baseEnd_4548657 < baseStart_4548657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548671 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 3, 2, 2]
def baseStart_4548671 : Nat := 118140960795 + 4548671 * 2 ^ 59
def prefixEnd_4548671 : Nat := 4983230072969 + 3 ^ 40 * 4548671 * 2
def baseEnd_4548671 : Nat := 2335654562167478037493549

theorem tailTrace_4548671 : CollatzResearch.WordTrace tailWord_4548671 prefixEnd_4548671 2335654562167478037493549 := by
  unfold tailWord_4548671
  simp only [CollatzResearch.WordTrace]
  refine ⟨165903660903949293003629867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110602440602632862002419911 165903660903949293003629867)
  ·
    refine ⟨248855491355923939505444801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165903660903949293003629867 248855491355923939505444801)
    ·
      refine ⟨186641618516942954629083601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248855491355923939505444801 186641618516942954629083601)
      ·
        refine ⟨139981213887707215971812701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186641618516942954629083601 139981213887707215971812701)
        ·
          refine ⟨52492955207890205989429763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139981213887707215971812701 52492955207890205989429763)
          ·
            refine ⟨78739432811835308984144645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52492955207890205989429763 78739432811835308984144645)
            ·
              refine ⟨14763643652219120434527121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78739432811835308984144645 14763643652219120434527121)
              ·
                refine ⟨11072732739164340325895341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14763643652219120434527121 11072732739164340325895341)
                ·
                  refine ⟨4152274777186627622210753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11072732739164340325895341 4152274777186627622210753)
                  ·
                    refine ⟨3114206082889970716658065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4152274777186627622210753 3114206082889970716658065)
                    ·
                      refine ⟨2335654562167478037493549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114206082889970716658065 2335654562167478037493549)
                      ·
                        rfl

theorem cell23_4548671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_4548671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548671 prefixEnd_4548671 := by exact prefixLift 4548671
  have htrace : WordTrace (prefixWord ++ tailWord_4548671) baseStart_4548671 baseEnd_4548671 := by
    simpa [prefixWord, tailWord_4548671, baseEnd_4548671] using wordTrace_append hprefix tailTrace_4548671
  have hstable : (prefixWord ++ tailWord_4548671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548671).length < 2 ^ (prefixWord ++ tailWord_4548671).sum := by decide
  have hdescent : baseEnd_4548671 < baseStart_4548671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548721 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_4548721 : Nat := 118140960795 + 4548721 * 2 ^ 59
def prefixEnd_4548721 : Nat := 4983230072969 + 3 ^ 40 * 4548721 * 2
def baseEnd_4548721 : Nat := 2335680236200202841868319

theorem tailTrace_4548721 : CollatzResearch.WordTrace tailWord_4548721 prefixEnd_4548721 2335680236200202841868319 := by
  unfold tailWord_4548721
  simp only [CollatzResearch.WordTrace]
  refine ⟨165905484553768151542950017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110603656369178767695300011 165905484553768151542950017)
  ·
    refine ⟨124429113415326113657212513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165905484553768151542950017 124429113415326113657212513)
    ·
      refine ⟨93321835061494585242909385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124429113415326113657212513 93321835061494585242909385)
      ·
        refine ⟨69991376296120938932182039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93321835061494585242909385 69991376296120938932182039)
        ·
          refine ⟨104987064444181408398273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69991376296120938932182039 104987064444181408398273059)
          ·
            refine ⟨157480596666272112597409589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104987064444181408398273059 157480596666272112597409589)
            ·
              refine ⟨14763805937463010556007149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157480596666272112597409589 14763805937463010556007149)
              ·
                refine ⟨5536427226548628958502681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14763805937463010556007149 5536427226548628958502681)
                ·
                  refine ⟨4152320419911471718877011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5536427226548628958502681 4152320419911471718877011)
                  ·
                    refine ⟨6228480629867207578315517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4152320419911471718877011 6228480629867207578315517)
                    ·
                      refine ⟨2335680236200202841868319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228480629867207578315517 2335680236200202841868319)
                      ·
                        rfl

theorem cell23_4548721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_4548721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548721 prefixEnd_4548721 := by exact prefixLift 4548721
  have htrace : WordTrace (prefixWord ++ tailWord_4548721) baseStart_4548721 baseEnd_4548721 := by
    simpa [prefixWord, tailWord_4548721, baseEnd_4548721] using wordTrace_append hprefix tailTrace_4548721
  have hstable : (prefixWord ++ tailWord_4548721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548721).length < 2 ^ (prefixWord ++ tailWord_4548721).sum := by decide
  have hdescent : baseEnd_4548721 < baseStart_4548721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548754 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4548754 : Nat := 118140960795 + 4548754 * 2 ^ 59
def prefixEnd_4548754 : Nat := 4983230072969 + 3 ^ 40 * 4548754 * 2
def baseEnd_4548754 : Nat := 778565727020600404251889

theorem tailTrace_4548754 : CollatzResearch.WordTrace tailWord_4548754 prefixEnd_4548754 778565727020600404251889 := by
  unfold tailWord_4548754
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476672040662149544725329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110604458775099065452600877 41476672040662149544725329)
  ·
    refine ⟨31107504030496612158543997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41476672040662149544725329 31107504030496612158543997)
    ·
      refine ⟨11665314011436229559453999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31107504030496612158543997 11665314011436229559453999)
      ·
        refine ⟨17497971017154344339180999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665314011436229559453999 17497971017154344339180999)
        ·
          refine ⟨26246956525731516508771499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17497971017154344339180999 26246956525731516508771499)
          ·
            refine ⟨39370434788597274763157249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26246956525731516508771499 39370434788597274763157249)
            ·
              refine ⟨29527826091447956072367937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39370434788597274763157249 29527826091447956072367937)
              ·
                refine ⟨22145869568585967054275953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29527826091447956072367937 22145869568585967054275953)
                ·
                  refine ⟨16609402176439475290706965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22145869568585967054275953 16609402176439475290706965)
                  ·
                    refine ⟨778565727020600404251889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16609402176439475290706965 778565727020600404251889)
                    ·
                      rfl

theorem cell23_4548754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4548754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548754 prefixEnd_4548754 := by exact prefixLift 4548754
  have htrace : WordTrace (prefixWord ++ tailWord_4548754) baseStart_4548754 baseEnd_4548754 := by
    simpa [prefixWord, tailWord_4548754, baseEnd_4548754] using wordTrace_append hprefix tailTrace_4548754
  have hstable : (prefixWord ++ tailWord_4548754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548754).length < 2 ^ (prefixWord ++ tailWord_4548754).sum := by decide
  have hdescent : baseEnd_4548754 < baseStart_4548754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548756 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4548756 : Nat := 118140960795 + 4548756 * 2 ^ 59
def prefixEnd_4548756 : Nat := 4983230072969 + 3 ^ 40 * 4548756 * 2
def baseEnd_4548756 : Nat := 2335698208023110204930659

theorem tailTrace_4548756 : CollatzResearch.WordTrace tailWord_4548756 prefixEnd_4548756 2335698208023110204930659 := by
  unfold tailWord_4548756
  simp only [CollatzResearch.WordTrace]
  refine ⟨82953380554320676260237061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110604507405760901680316081 82953380554320676260237061)
  ·
    refine ⟨15553758853935126798794449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82953380554320676260237061 15553758853935126798794449)
    ·
      refine ⟨11665319140451345099095837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15553758853935126798794449 11665319140451345099095837)
      ·
        refine ⟨4374494677669254412160939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11665319140451345099095837 4374494677669254412160939)
        ·
          refine ⟨6561742016503881618241409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374494677669254412160939 6561742016503881618241409)
          ·
            refine ⟨4921306512377911213681057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561742016503881618241409 4921306512377911213681057)
            ·
              refine ⟨3690979884283433410260793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921306512377911213681057 3690979884283433410260793)
              ·
                refine ⟨2768234913212575057695595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690979884283433410260793 2768234913212575057695595)
                ·
                  refine ⟨4152352369818862586543393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768234913212575057695595 4152352369818862586543393)
                  ·
                    refine ⟨3114264277364146939907545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4152352369818862586543393 3114264277364146939907545)
                    ·
                      refine ⟨2335698208023110204930659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114264277364146939907545 2335698208023110204930659)
                      ·
                        rfl

theorem cell23_4548756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4548756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548756 prefixEnd_4548756 := by exact prefixLift 4548756
  have htrace : WordTrace (prefixWord ++ tailWord_4548756) baseStart_4548756 baseEnd_4548756 := by
    simpa [prefixWord, tailWord_4548756, baseEnd_4548756] using wordTrace_append hprefix tailTrace_4548756
  have hstable : (prefixWord ++ tailWord_4548756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548756).length < 2 ^ (prefixWord ++ tailWord_4548756).sum := by decide
  have hdescent : baseEnd_4548756 < baseStart_4548756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548761 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 4, 2, 2]
def baseStart_4548761 : Nat := 118140960795 + 4548761 * 2 ^ 59
def prefixEnd_4548761 : Nat := 4983230072969 + 3 ^ 40 * 4548761 * 2
def baseEnd_4548761 : Nat := 2335700775426382685368135

theorem tailTrace_4548761 : CollatzResearch.WordTrace tailWord_4548761 prefixEnd_4548761 2335700775426382685368135 := by
  unfold tailWord_4548761
  simp only [CollatzResearch.WordTrace]
  refine ⟨165906943473623238374406137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110604628982415492249604091 165906943473623238374406137)
  ·
    refine ⟨124430207605217428780804603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165906943473623238374406137 124430207605217428780804603)
    ·
      refine ⟨186645311407826143171206905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124430207605217428780804603 186645311407826143171206905)
      ·
        refine ⟨139983983555869607378405179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186645311407826143171206905 139983983555869607378405179)
        ·
          refine ⟨209975975333804411067607769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139983983555869607378405179 209975975333804411067607769)
          ·
            refine ⟨157481981500353308300705827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209975975333804411067607769 157481981500353308300705827)
            ·
              refine ⟨236222972250529962451058741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157481981500353308300705827 236222972250529962451058741)
              ·
                refine ⟨22145903648487183979786757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236222972250529962451058741 22145903648487183979786757)
                ·
                  refine ⟨4152356934091346996210017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22145903648487183979786757 4152356934091346996210017)
                  ·
                    refine ⟨3114267700568510247157513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4152356934091346996210017 3114267700568510247157513)
                    ·
                      refine ⟨2335700775426382685368135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114267700568510247157513 2335700775426382685368135)
                      ·
                        rfl

theorem cell23_4548761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_4548761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548761 prefixEnd_4548761 := by exact prefixLift 4548761
  have htrace : WordTrace (prefixWord ++ tailWord_4548761) baseStart_4548761 baseEnd_4548761 := by
    simpa [prefixWord, tailWord_4548761, baseEnd_4548761] using wordTrace_append hprefix tailTrace_4548761
  have hstable : (prefixWord ++ tailWord_4548761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548761).length < 2 ^ (prefixWord ++ tailWord_4548761).sum := by decide
  have hdescent : baseEnd_4548761 < baseStart_4548761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548764 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4548764 : Nat := 118140960795 + 4548764 * 2 ^ 59
def prefixEnd_4548764 : Nat := 4983230072969 + 3 ^ 40 * 4548764 * 2
def baseEnd_4548764 : Nat := 2335702315868346173630621

theorem tailTrace_4548764 : CollatzResearch.WordTrace tailWord_4548764 prefixEnd_4548764 2335702315868346173630621 := by
  unfold tailWord_4548764
  simp only [CollatzResearch.WordTrace]
  refine ⟨82953526446306184943382673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110604701928408246591176897 82953526446306184943382673)
  ·
    refine ⟨62215144834729638707537005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82953526446306184943382673 62215144834729638707537005)
    ·
      refine ⟨23330679313023614515326377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62215144834729638707537005 23330679313023614515326377)
      ·
        refine ⟨17498009484767710886494783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23330679313023614515326377 17498009484767710886494783)
        ·
          refine ⟨26247014227151566329742175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498009484767710886494783 26247014227151566329742175)
          ·
            refine ⟨39370521340727349494613263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26247014227151566329742175 39370521340727349494613263)
            ·
              refine ⟨59055782011091024241919895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39370521340727349494613263 59055782011091024241919895)
              ·
                refine ⟨88583673016636536362879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59055782011091024241919895 88583673016636536362879843)
                ·
                  refine ⟨132875509524954804544319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88583673016636536362879843 132875509524954804544319765)
                  ·
                    refine ⟨6228539508982256463014989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132875509524954804544319765 6228539508982256463014989)
                    ·
                      refine ⟨2335702315868346173630621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228539508982256463014989 2335702315868346173630621)
                      ·
                        rfl

theorem cell23_4548764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4548764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548764 prefixEnd_4548764 := by exact prefixLift 4548764
  have htrace : WordTrace (prefixWord ++ tailWord_4548764) baseStart_4548764 baseEnd_4548764 := by
    simpa [prefixWord, tailWord_4548764, baseEnd_4548764] using wordTrace_append hprefix tailTrace_4548764
  have hstable : (prefixWord ++ tailWord_4548764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548764).length < 2 ^ (prefixWord ++ tailWord_4548764).sum := by decide
  have hdescent : baseEnd_4548764 < baseStart_4548764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548827 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 8]
def baseStart_4548827 : Nat := 118140960795 + 4548827 * 2 ^ 59
def prefixEnd_4548827 : Nat := 4983230072969 + 3 ^ 40 * 4548827 * 2
def baseEnd_4548827 : Nat := 778578221716526475714277

theorem tailTrace_4548827 : CollatzResearch.WordTrace tailWord_4548827 prefixEnd_4548827 778578221716526475714277 := by
  unfold tailWord_4548827
  simp only [CollatzResearch.WordTrace]
  refine ⟨165909350691384131646308735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110606233794256087764205823 165909350691384131646308735)
  ·
    refine ⟨248864026037076197469463103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165909350691384131646308735 248864026037076197469463103)
    ·
      refine ⟨373296039055614296204194655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248864026037076197469463103 373296039055614296204194655)
      ·
        refine ⟨559944058583421444306291983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373296039055614296204194655 559944058583421444306291983)
        ·
          refine ⟨839916087875132166459437975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559944058583421444306291983 839916087875132166459437975)
          ·
            refine ⟨1259874131812698249689156963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839916087875132166459437975 1259874131812698249689156963)
            ·
              refine ⟨1889811197719047374533735445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259874131812698249689156963 1889811197719047374533735445)
              ·
                refine ⟨88584899893080345681268849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1889811197719047374533735445 88584899893080345681268849)
                ·
                  refine ⟨66438674919810259260951637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88584899893080345681268849 66438674919810259260951637)
                  ·
                    refine ⟨778578221716526475714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66438674919810259260951637 778578221716526475714277)
                    ·
                      rfl

theorem cell23_4548827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_4548827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548827 prefixEnd_4548827 := by exact prefixLift 4548827
  have htrace : WordTrace (prefixWord ++ tailWord_4548827) baseStart_4548827 baseEnd_4548827 := by
    simpa [prefixWord, tailWord_4548827, baseEnd_4548827] using wordTrace_append hprefix tailTrace_4548827
  have hstable : (prefixWord ++ tailWord_4548827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548827).length < 2 ^ (prefixWord ++ tailWord_4548827).sum := by decide
  have hdescent : baseEnd_4548827 < baseStart_4548827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548868 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4548868 : Nat := 118140960795 + 4548868 * 2 ^ 59
def prefixEnd_4548868 : Nat := 4983230072969 + 3 ^ 40 * 4548868 * 2
def baseEnd_4548868 : Nat := 2335755717856413766730143

theorem tailTrace_4548868 : CollatzResearch.WordTrace tailWord_4548868 prefixEnd_4548868 2335755717856413766730143 := by
  unfold tailWord_4548868
  simp only [CollatzResearch.WordTrace]
  refine ⟨82955423042117797824275629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110607230722823730432367505 82955423042117797824275629)
  ·
    refine ⟨31108283640794174184103361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82955423042117797824275629 31108283640794174184103361)
    ·
      refine ⟨23331212730595630638077521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31108283640794174184103361 23331212730595630638077521)
      ·
        refine ⟨17498409547946722978558141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23331212730595630638077521 17498409547946722978558141)
        ·
          refine ⟨6561903580480021116959303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17498409547946722978558141 6561903580480021116959303)
          ·
            refine ⟨9842855370720031675438955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561903580480021116959303 9842855370720031675438955)
            ·
              refine ⟨14764283056080047513158433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9842855370720031675438955 14764283056080047513158433)
              ·
                refine ⟨11073212292060035634868825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14764283056080047513158433 11073212292060035634868825)
                ·
                  refine ⟨8304909219045026726151619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11073212292060035634868825 8304909219045026726151619)
                  ·
                    refine ⟨12457363828567540089227429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8304909219045026726151619 12457363828567540089227429)
                    ·
                      refine ⟨2335755717856413766730143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12457363828567540089227429 2335755717856413766730143)
                      ·
                        rfl

theorem cell23_4548868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4548868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548868 prefixEnd_4548868 := by exact prefixLift 4548868
  have htrace : WordTrace (prefixWord ++ tailWord_4548868) baseStart_4548868 baseEnd_4548868 := by
    simpa [prefixWord, tailWord_4548868, baseEnd_4548868] using wordTrace_append hprefix tailTrace_4548868
  have hstable : (prefixWord ++ tailWord_4548868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548868).length < 2 ^ (prefixWord ++ tailWord_4548868).sum := by decide
  have hdescent : baseEnd_4548868 < baseStart_4548868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548874 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_4548874 : Nat := 118140960795 + 4548874 * 2 ^ 59
def prefixEnd_4548874 : Nat := 4983230072969 + 3 ^ 40 * 4548874 * 2
def baseEnd_4548874 : Nat := 259528755415593415917235

theorem tailTrace_4548874 : CollatzResearch.WordTrace tailWord_4548874 prefixEnd_4548874 259528755415593415917235 := by
  unfold tailWord_4548874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41477766230553464668317419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110607376614809239115513117 41477766230553464668317419)
  ·
    refine ⟨62216649345830197002476129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41477766230553464668317419 62216649345830197002476129)
    ·
      refine ⟨46662487009372647751857097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62216649345830197002476129 46662487009372647751857097)
      ·
        refine ⟨34996865257029485813892823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46662487009372647751857097 34996865257029485813892823)
        ·
          refine ⟨52495297885544228720839235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34996865257029485813892823 52495297885544228720839235)
          ·
            refine ⟨78742946828316343081258853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52495297885544228720839235 78742946828316343081258853)
            ·
              refine ⟨14764302530309314327736035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78742946828316343081258853 14764302530309314327736035)
              ·
                refine ⟨22146453795463971491604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14764302530309314327736035 22146453795463971491604053)
                ·
                  refine ⟨259528755415593415917235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22146453795463971491604053 259528755415593415917235)
                  ·
                    rfl

theorem cell23_4548874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_4548874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548874 prefixEnd_4548874 := by exact prefixLift 4548874
  have htrace : WordTrace (prefixWord ++ tailWord_4548874) baseStart_4548874 baseEnd_4548874 := by
    simpa [prefixWord, tailWord_4548874, baseEnd_4548874] using wordTrace_append hprefix tailTrace_4548874
  have hstable : (prefixWord ++ tailWord_4548874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548874).length < 2 ^ (prefixWord ++ tailWord_4548874).sum := by decide
  have hdescent : baseEnd_4548874 < baseStart_4548874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548891 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 6]
def baseStart_4548891 : Nat := 118140960795 + 4548891 * 2 ^ 59
def prefixEnd_4548891 : Nat := 4983230072969 + 3 ^ 40 * 4548891 * 2
def baseEnd_4548891 : Nat := 259529725323496352971393

theorem tailTrace_4548891 : CollatzResearch.WordTrace tailWord_4548891 prefixEnd_4548891 259529725323496352971393 := by
  unfold tailWord_4548891
  simp only [CollatzResearch.WordTrace]
  refine ⟨165911684963152270576638527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110607789975434847051092351 165911684963152270576638527)
  ·
    refine ⟨248867527444728405864957791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165911684963152270576638527 248867527444728405864957791)
    ·
      refine ⟨373301291167092608797436687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248867527444728405864957791 373301291167092608797436687)
      ·
        refine ⟨559951936750638913196155031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373301291167092608797436687 559951936750638913196155031)
        ·
          refine ⟨839927905125958369794232547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559951936750638913196155031 839927905125958369794232547)
          ·
            refine ⟨1259891857688937554691348821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839927905125958369794232547 1259891857688937554691348821)
            ·
              refine ⟨3691089426823059242259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1259891857688937554691348821 3691089426823059242259811)
              ·
                refine ⟨5536634140234588863389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691089426823059242259811 5536634140234588863389717)
                ·
                  refine ⟨259529725323496352971393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5536634140234588863389717 259529725323496352971393)
                  ·
                    rfl

theorem cell23_4548891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 6].length) (baseStart_4548891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548891 prefixEnd_4548891 := by exact prefixLift 4548891
  have htrace : WordTrace (prefixWord ++ tailWord_4548891) baseStart_4548891 baseEnd_4548891 := by
    simpa [prefixWord, tailWord_4548891, baseEnd_4548891] using wordTrace_append hprefix tailTrace_4548891
  have hstable : (prefixWord ++ tailWord_4548891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548891).length < 2 ^ (prefixWord ++ tailWord_4548891).sum := by decide
  have hdescent : baseEnd_4548891 < baseStart_4548891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548911 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 5, 2]
def baseStart_4548911 : Nat := 118140960795 + 4548911 * 2 ^ 59
def prefixEnd_4548911 : Nat := 4983230072969 + 3 ^ 40 * 4548911 * 2
def baseEnd_4548911 : Nat := 2335777797524557098492445

theorem tailTrace_4548911 : CollatzResearch.WordTrace tailWord_4548911 prefixEnd_4548911 2335777797524557098492445 := by
  unfold tailWord_4548911
  simp only [CollatzResearch.WordTrace]
  refine ⟨165912414423079813992366587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110608276282053209328244391 165912414423079813992366587)
  ·
    refine ⟨248868621634619720988549881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165912414423079813992366587 248868621634619720988549881)
    ·
      refine ⟨186651466225964790741412411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248868621634619720988549881 186651466225964790741412411)
      ·
        refine ⟨279977199338947186112118617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186651466225964790741412411 279977199338947186112118617)
        ·
          refine ⟨209982899504210389584088963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279977199338947186112118617 209982899504210389584088963)
          ·
            refine ⟨314974349256315584376133445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209982899504210389584088963 314974349256315584376133445)
            ·
              refine ⟨59057690485559172070525021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314974349256315584376133445 59057690485559172070525021)
              ·
                refine ⟨22146633932084689526446883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59057690485559172070525021 22146633932084689526446883)
                ·
                  refine ⟨33219950898127034289670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22146633932084689526446883 33219950898127034289670325)
                  ·
                    refine ⟨3114370396699409464656593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33219950898127034289670325 3114370396699409464656593)
                    ·
                      refine ⟨2335777797524557098492445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114370396699409464656593 2335777797524557098492445)
                      ·
                        rfl

theorem cell23_4548911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5, 2].length) (baseStart_4548911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548911 prefixEnd_4548911 := by exact prefixLift 4548911
  have htrace : WordTrace (prefixWord ++ tailWord_4548911) baseStart_4548911 baseEnd_4548911 := by
    simpa [prefixWord, tailWord_4548911, baseEnd_4548911] using wordTrace_append hprefix tailTrace_4548911
  have hstable : (prefixWord ++ tailWord_4548911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548911).length < 2 ^ (prefixWord ++ tailWord_4548911).sum := by decide
  have hdescent : baseEnd_4548911 < baseStart_4548911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548929 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4548929 : Nat := 118140960795 + 4548929 * 2 ^ 59
def prefixEnd_4548929 : Nat := 4983230072969 + 3 ^ 40 * 4548929 * 2
def baseEnd_4548929 : Nat := 778595680058779342689121

theorem tailTrace_4548929 : CollatzResearch.WordTrace tailWord_4548929 prefixEnd_4548929 778595680058779342689121 := by
  unfold tailWord_4548929
  simp only [CollatzResearch.WordTrace]
  refine ⟨165913070937014603066521841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110608713958009735377681227 165913070937014603066521841)
  ·
    refine ⟨124434803202760952299891381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165913070937014603066521841 124434803202760952299891381)
    ·
      refine ⟨11665762800258839278114817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124434803202760952299891381 11665762800258839278114817)
      ·
        refine ⟨8749322100194129458586113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11665762800258839278114817 8749322100194129458586113)
        ·
          refine ⟨6561991575145597093939585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8749322100194129458586113 6561991575145597093939585)
          ·
            refine ⟨4921493681359197820454689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6561991575145597093939585 4921493681359197820454689)
            ·
              refine ⟨3691120261019398365341017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921493681359197820454689 3691120261019398365341017)
              ·
                refine ⟨2768340195764548774005763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691120261019398365341017 2768340195764548774005763)
                ·
                  refine ⟨4152510293646823161008645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768340195764548774005763 4152510293646823161008645)
                  ·
                    refine ⟨778595680058779342689121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4152510293646823161008645 778595680058779342689121)
                    ·
                      rfl

theorem cell23_4548929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4548929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548929 prefixEnd_4548929 := by exact prefixLift 4548929
  have htrace : WordTrace (prefixWord ++ tailWord_4548929) baseStart_4548929 baseEnd_4548929 := by
    simpa [prefixWord, tailWord_4548929, baseEnd_4548929] using wordTrace_append hprefix tailTrace_4548929
  have hstable : (prefixWord ++ tailWord_4548929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548929).length < 2 ^ (prefixWord ++ tailWord_4548929).sum := by decide
  have hdescent : baseEnd_4548929 < baseStart_4548929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548935 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_4548935 : Nat := 118140960795 + 4548935 * 2 ^ 59
def prefixEnd_4548935 : Nat := 4983230072969 + 3 ^ 40 * 4548935 * 2
def baseEnd_4548935 : Nat := 2335790121060265004592335

theorem tailTrace_4548935 : CollatzResearch.WordTrace tailWord_4548935 prefixEnd_4548935 2335790121060265004592335 := by
  unfold tailWord_4548935
  simp only [CollatzResearch.WordTrace]
  refine ⟨165913289774992866091240259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110608859849995244060826839 165913289774992866091240259)
  ·
    refine ⟨248869934662489299136860389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165913289774992866091240259 248869934662489299136860389)
    ·
      refine ⟨46663112749216743588161323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248869934662489299136860389 46663112749216743588161323)
      ·
        refine ⟨69994669123825115382241985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46663112749216743588161323 69994669123825115382241985)
        ·
          refine ⟨52496001842868836536681489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69994669123825115382241985 52496001842868836536681489)
          ·
            refine ⟨39372001382151627402511117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52496001842868836536681489 39372001382151627402511117)
            ·
              refine ⟨14764500518306860275941669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39372001382151627402511117 14764500518306860275941669)
              ·
                refine ⟨2768343847182536301739063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14764500518306860275941669 2768343847182536301739063)
                ·
                  refine ⟨4152515770773804452608595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768343847182536301739063 4152515770773804452608595)
                  ·
                    refine ⟨6228773656160706678912893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4152515770773804452608595 6228773656160706678912893)
                    ·
                      refine ⟨2335790121060265004592335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228773656160706678912893 2335790121060265004592335)
                      ·
                        rfl

theorem cell23_4548935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_4548935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548935 prefixEnd_4548935 := by exact prefixLift 4548935
  have htrace : WordTrace (prefixWord ++ tailWord_4548935) baseStart_4548935 baseEnd_4548935 := by
    simpa [prefixWord, tailWord_4548935, baseEnd_4548935] using wordTrace_append hprefix tailTrace_4548935
  have hstable : (prefixWord ++ tailWord_4548935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548935).length < 2 ^ (prefixWord ++ tailWord_4548935).sum := by decide
  have hdescent : baseEnd_4548935 < baseStart_4548935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548951 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 6]
def baseStart_4548951 : Nat := 118140960795 + 4548951 * 2 ^ 59
def prefixEnd_4548951 : Nat := 4983230072969 + 3 ^ 40 * 4548951 * 2
def baseEnd_4548951 : Nat := 778599445583578980664087

theorem tailTrace_4548951 : CollatzResearch.WordTrace tailWord_4548951 prefixEnd_4548951 778599445583578980664087 := by
  unfold tailWord_4548951
  simp only [CollatzResearch.WordTrace]
  refine ⟨165913873342934900823822707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110609248895289933882548471 165913873342934900823822707)
  ·
    refine ⟨248870810014402351235734061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165913873342934900823822707 248870810014402351235734061)
    ·
      refine ⟨93326553755400881713400273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248870810014402351235734061 93326553755400881713400273)
      ·
        refine ⟨69994915316550661285050205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93326553755400881713400273 69994915316550661285050205)
        ·
          refine ⟨26248093243706497981893827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69994915316550661285050205 26248093243706497981893827)
          ·
            refine ⟨39372139865559746972840741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26248093243706497981893827 39372139865559746972840741)
            ·
              refine ⟨7382276224792452557407639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39372139865559746972840741 7382276224792452557407639)
              ·
                refine ⟨11073414337188678836111459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382276224792452557407639 11073414337188678836111459)
                ·
                  refine ⟨16610121505783018254167189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11073414337188678836111459 16610121505783018254167189)
                  ·
                    refine ⟨778599445583578980664087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16610121505783018254167189 778599445583578980664087)
                    ·
                      rfl

theorem cell23_4548951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_4548951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548951 prefixEnd_4548951 := by exact prefixLift 4548951
  have htrace : WordTrace (prefixWord ++ tailWord_4548951) baseStart_4548951 baseEnd_4548951 := by
    simpa [prefixWord, tailWord_4548951, baseEnd_4548951] using wordTrace_append hprefix tailTrace_4548951
  have hstable : (prefixWord ++ tailWord_4548951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548951).length < 2 ^ (prefixWord ++ tailWord_4548951).sum := by decide
  have hdescent : baseEnd_4548951 < baseStart_4548951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548962 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4548962 : Nat := 118140960795 + 4548962 * 2 ^ 59
def prefixEnd_4548962 : Nat := 4983230072969 + 3 ^ 40 * 4548962 * 2
def baseEnd_4548962 : Nat := 2335803985037936398954711

theorem tailTrace_4548962 : CollatzResearch.WordTrace tailWord_4548962 prefixEnd_4548962 2335803985037936398954711 := by
  unfold tailWord_4548962
  simp only [CollatzResearch.WordTrace]
  refine ⟨41478568636473762425618285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110609516363930033134982093 41478568636473762425618285)
  ·
    refine ⟨15554463238677660909606857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41478568636473762425618285 15554463238677660909606857)
    ·
      refine ⟨11665847429008245682205143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15554463238677660909606857 11665847429008245682205143)
      ·
        refine ⟨17498771143512368523307715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665847429008245682205143 17498771143512368523307715)
        ·
          refine ⟨26248156715268552784961573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498771143512368523307715 26248156715268552784961573)
          ·
            refine ⟨4921529384112853647180295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26248156715268552784961573 4921529384112853647180295)
            ·
              refine ⟨7382294076169280470770443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921529384112853647180295 7382294076169280470770443)
              ·
                refine ⟨11073441114253920706155665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382294076169280470770443 11073441114253920706155665)
                ·
                  refine ⟨8305080835690440529616749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11073441114253920706155665 8305080835690440529616749)
                  ·
                    refine ⟨3114405313383915198606281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8305080835690440529616749 3114405313383915198606281)
                    ·
                      refine ⟨2335803985037936398954711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114405313383915198606281 2335803985037936398954711)
                      ·
                        rfl

theorem cell23_4548962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4548962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548962 prefixEnd_4548962 := by exact prefixLift 4548962
  have htrace : WordTrace (prefixWord ++ tailWord_4548962) baseStart_4548962 baseEnd_4548962 := by
    simpa [prefixWord, tailWord_4548962, baseEnd_4548962] using wordTrace_append hprefix tailTrace_4548962
  have hstable : (prefixWord ++ tailWord_4548962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548962).length < 2 ^ (prefixWord ++ tailWord_4548962).sum := by decide
  have hdescent : baseEnd_4548962 < baseStart_4548962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548972 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_4548972 : Nat := 118140960795 + 4548972 * 2 ^ 59
def prefixEnd_4548972 : Nat := 4983230072969 + 3 ^ 40 * 4548972 * 2
def baseEnd_4548972 : Nat := 778603039948160453276555

theorem tailTrace_4548972 : CollatzResearch.WordTrace tailWord_4548972 prefixEnd_4548972 778603039948160453276555 := by
  unfold tailWord_4548972
  simp only [CollatzResearch.WordTrace]
  refine ⟨82957319637929410705168585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110609759517239214273558113 82957319637929410705168585)
  ·
    refine ⟨62217989728447058028876439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82957319637929410705168585 62217989728447058028876439)
    ·
      refine ⟨93326984592670587043314659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62217989728447058028876439 93326984592670587043314659)
      ·
        refine ⟨139990476889005880564971989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93326984592670587043314659 139990476889005880564971989)
        ·
          refine ⟨3281026802086075325741531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 139990476889005880564971989 3281026802086075325741531)
          ·
            refine ⟨4921540203129112988612297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281026802086075325741531 4921540203129112988612297)
            ·
              refine ⟨3691155152346834741459223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921540203129112988612297 3691155152346834741459223)
              ·
                refine ⟨5536732728520252112188835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691155152346834741459223 5536732728520252112188835)
                ·
                  refine ⟨8305099092780378168283253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536732728520252112188835 8305099092780378168283253)
                  ·
                    refine ⟨778603039948160453276555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8305099092780378168283253 778603039948160453276555)
                    ·
                      rfl

theorem cell23_4548972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_4548972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548972 prefixEnd_4548972 := by exact prefixLift 4548972
  have htrace : WordTrace (prefixWord ++ tailWord_4548972) baseStart_4548972 baseEnd_4548972 := by
    simpa [prefixWord, tailWord_4548972, baseEnd_4548972] using wordTrace_append hprefix tailTrace_4548972
  have hstable : (prefixWord ++ tailWord_4548972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548972).length < 2 ^ (prefixWord ++ tailWord_4548972).sum := by decide
  have hdescent : baseEnd_4548972 < baseStart_4548972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4548981 : List Nat := [1, 3, 4, 1, 2, 2, 10]
def baseStart_4548981 : Nat := 118140960795 + 4548981 * 2 ^ 59
def prefixEnd_4548981 : Nat := 4983230072969 + 3 ^ 40 * 4548981 * 2
def baseEnd_4548981 : Nat := 28837206681115701538483

theorem tailTrace_4548981 : CollatzResearch.WordTrace tailWord_4548981 prefixEnd_4548981 28837206681115701538483 := by
  unfold tailWord_4548981
  simp only [CollatzResearch.WordTrace]
  refine ⟨165914967532826215947414797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110609978355217477298276531 165914967532826215947414797)
  ·
    refine ⟨62218112824809830980280549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165914967532826215947414797 62218112824809830980280549)
    ·
      refine ⟨11665896154651843308802603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62218112824809830980280549 11665896154651843308802603)
      ·
        refine ⟨17498844231977764963203905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665896154651843308802603 17498844231977764963203905)
        ·
          refine ⟨13124133173983323722402929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17498844231977764963203905 13124133173983323722402929)
          ·
            refine ⟨9843099880487492791802197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13124133173983323722402929 9843099880487492791802197)
            ·
              refine ⟨28837206681115701538483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9843099880487492791802197 28837206681115701538483)
              ·
                rfl

theorem cell23_4548981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 10].length) (baseStart_4548981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4548981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4548981 prefixEnd_4548981 := by exact prefixLift 4548981
  have htrace : WordTrace (prefixWord ++ tailWord_4548981) baseStart_4548981 baseEnd_4548981 := by
    simpa [prefixWord, tailWord_4548981, baseEnd_4548981] using wordTrace_append hprefix tailTrace_4548981
  have hstable : (prefixWord ++ tailWord_4548981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4548981).length < 2 ^ (prefixWord ++ tailWord_4548981).sum := by decide
  have hdescent : baseEnd_4548981 < baseStart_4548981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4548981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549002 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_4549002 : Nat := 118140960795 + 4549002 * 2 ^ 59
def prefixEnd_4549002 : Nat := 4983230072969 + 3 ^ 40 * 4549002 * 2
def baseEnd_4549002 : Nat := 778608174754705414151509

theorem tailTrace_4549002 : CollatzResearch.WordTrace tailWord_4549002 prefixEnd_4549002 778608174754705414151509 := by
  unfold tailWord_4549002
  simp only [CollatzResearch.WordTrace]
  refine ⟨41478933366437534133482315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110610488977166757689286173 41478933366437534133482315)
  ·
    refine ⟨62218400049656301200223473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41478933366437534133482315 62218400049656301200223473)
    ·
      refine ⟨46663800037242225900167605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62218400049656301200223473 46663800037242225900167605)
      ·
        refine ⟨4374731253491458678140713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46663800037242225900167605 4374731253491458678140713)
        ·
          refine ⟨3281048440118594008605535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4374731253491458678140713 3281048440118594008605535)
          ·
            refine ⟨4921572660177891012908303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281048440118594008605535 4921572660177891012908303)
            ·
              refine ⟨7382358990266836519362455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921572660177891012908303 7382358990266836519362455)
              ·
                refine ⟨11073538485400254779043683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7382358990266836519362455 11073538485400254779043683)
                ·
                  refine ⟨16610307728100382168565525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11073538485400254779043683 16610307728100382168565525)
                  ·
                    refine ⟨778608174754705414151509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16610307728100382168565525 778608174754705414151509)
                    ·
                      rfl

theorem cell23_4549002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_4549002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549002 prefixEnd_4549002 := by exact prefixLift 4549002
  have htrace : WordTrace (prefixWord ++ tailWord_4549002) baseStart_4549002 baseEnd_4549002 := by
    simpa [prefixWord, tailWord_4549002, baseEnd_4549002] using wordTrace_append hprefix tailTrace_4549002
  have hstable : (prefixWord ++ tailWord_4549002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549002).length < 2 ^ (prefixWord ++ tailWord_4549002).sum := by decide
  have hdescent : baseEnd_4549002 < baseStart_4549002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549012 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4549012 : Nat := 118140960795 + 4549012 * 2 ^ 59
def prefixEnd_4549012 : Nat := 4983230072969 + 3 ^ 40 * 4549012 * 2
def baseEnd_4549012 : Nat := 2335829659070661203329481

theorem tailTrace_4549012 : CollatzResearch.WordTrace tailWord_4549012 prefixEnd_4549012 2335829659070661203329481 := by
  unfold tailWord_4549012
  simp only [CollatzResearch.WordTrace]
  refine ⟨82958049097856954120896645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110610732130475938827862193 82958049097856954120896645)
  ·
    refine ⟨15554634205848178897668121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82958049097856954120896645 15554634205848178897668121)
    ·
      refine ⟨11665975654386134173251091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15554634205848178897668121 11665975654386134173251091)
      ·
        refine ⟨17498963481579201259876637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665975654386134173251091 17498963481579201259876637)
        ·
          refine ⟨6562111305592200472453739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17498963481579201259876637 6562111305592200472453739)
          ·
            refine ⟨9843166958388300708680609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562111305592200472453739 9843166958388300708680609)
            ·
              refine ⟨7382375218791225531510457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9843166958388300708680609 7382375218791225531510457)
              ·
                refine ⟨5536781414093419148632843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382375218791225531510457 5536781414093419148632843)
                ·
                  refine ⟨8305172121140128722949265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536781414093419148632843 8305172121140128722949265)
                  ·
                    refine ⟨6228879090855096542211949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8305172121140128722949265 6228879090855096542211949)
                    ·
                      refine ⟨2335829659070661203329481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6228879090855096542211949 2335829659070661203329481)
                      ·
                        rfl

theorem cell23_4549012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4549012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549012 prefixEnd_4549012 := by exact prefixLift 4549012
  have htrace : WordTrace (prefixWord ++ tailWord_4549012) baseStart_4549012 baseEnd_4549012 := by
    simpa [prefixWord, tailWord_4549012, baseEnd_4549012] using wordTrace_append hprefix tailTrace_4549012
  have hstable : (prefixWord ++ tailWord_4549012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549012).length < 2 ^ (prefixWord ++ tailWord_4549012).sum := by decide
  have hdescent : baseEnd_4549012 < baseStart_4549012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549088 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 5]
def baseStart_4549088 : Nat := 118140960795 + 4549088 * 2 ^ 59
def prefixEnd_4549088 : Nat := 4983230072969 + 3 ^ 40 * 4549088 * 2
def baseEnd_4549088 : Nat := 259540964844489211775459

theorem tailTrace_4549088 : CollatzResearch.WordTrace tailWord_4549088 prefixEnd_4549088 259540964844489211775459 := by
  unfold tailWord_4549088
  simp only [CollatzResearch.WordTrace]
  refine ⟨82959435071719286610779959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110612580095625715481039945 82959435071719286610779959)
  ·
    refine ⟨124439152607578929916169939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82959435071719286610779959 124439152607578929916169939)
    ·
      refine ⟨186658728911368394874254909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124439152607578929916169939 186658728911368394874254909)
      ·
        refine ⟨69997023341763148077845591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186658728911368394874254909 69997023341763148077845591)
        ·
          refine ⟨104995535012644722116768387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69997023341763148077845591 104995535012644722116768387)
          ·
            refine ⟨157493302518967083175152581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104995535012644722116768387 157493302518967083175152581)
            ·
              refine ⟨29529994222306328095341109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157493302518967083175152581 29529994222306328095341109)
              ·
                refine ⟨2768436958341218258938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29529994222306328095341109 2768436958341218258938229)
                ·
                  refine ⟨259540964844489211775459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768436958341218258938229 259540964844489211775459)
                  ·
                    rfl

theorem cell23_4549088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 5].length) (baseStart_4549088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549088 prefixEnd_4549088 := by exact prefixLift 4549088
  have htrace : WordTrace (prefixWord ++ tailWord_4549088) baseStart_4549088 baseEnd_4549088 := by
    simpa [prefixWord, tailWord_4549088, baseEnd_4549088] using wordTrace_append hprefix tailTrace_4549088
  have hstable : (prefixWord ++ tailWord_4549088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549088).length < 2 ^ (prefixWord ++ tailWord_4549088).sum := by decide
  have hdescent : baseEnd_4549088 < baseStart_4549088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549155 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 4, 2]
def baseStart_4549155 : Nat := 118140960795 + 4549155 * 2 ^ 59
def prefixEnd_4549155 : Nat := 4983230072969 + 3 ^ 40 * 4549155 * 2
def baseEnd_4549155 : Nat := 2335903086804254143841323

theorem tailTrace_4549155 : CollatzResearch.WordTrace tailWord_4549155 prefixEnd_4549155 2335903086804254143841323 := by
  unfold tailWord_4549155
  simp only [CollatzResearch.WordTrace]
  refine ⟨165921313834195843664248919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110614209222797229109499279 165921313834195843664248919)
  ·
    refine ⟨248881970751293765496373379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165921313834195843664248919 248881970751293765496373379)
    ·
      refine ⟨373322956126940648244560069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248881970751293765496373379 373322956126940648244560069)
      ·
        refine ⟨69998054273801371545855013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373322956126940648244560069 69998054273801371545855013)
        ·
          refine ⟨13124635176337757164847815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69998054273801371545855013 13124635176337757164847815)
          ·
            refine ⟨19686952764506635747271723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13124635176337757164847815 19686952764506635747271723)
            ·
              refine ⟨29530429146759953620907585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19686952764506635747271723 29530429146759953620907585)
              ·
                refine ⟨22147821860069965215680689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29530429146759953620907585 22147821860069965215680689)
                ·
                  refine ⟨16610866395052473911760517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22147821860069965215680689 16610866395052473911760517)
                  ·
                    refine ⟨3114537449072338858455097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16610866395052473911760517 3114537449072338858455097)
                    ·
                      refine ⟨2335903086804254143841323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114537449072338858455097 2335903086804254143841323)
                      ·
                        rfl

theorem cell23_4549155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_4549155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549155 prefixEnd_4549155 := by exact prefixLift 4549155
  have htrace : WordTrace (prefixWord ++ tailWord_4549155) baseStart_4549155 baseEnd_4549155 := by
    simpa [prefixWord, tailWord_4549155, baseEnd_4549155] using wordTrace_append hprefix tailTrace_4549155
  have hstable : (prefixWord ++ tailWord_4549155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549155).length < 2 ^ (prefixWord ++ tailWord_4549155).sum := by decide
  have hdescent : baseEnd_4549155 < baseStart_4549155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549205 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4549205 : Nat := 118140960795 + 4549205 * 2 ^ 59
def prefixEnd_4549205 : Nat := 4983230072969 + 3 ^ 40 * 4549205 * 2
def baseEnd_4549205 : Nat := 2335928760836978948216093

theorem tailTrace_4549205 : CollatzResearch.WordTrace tailWord_4549205 prefixEnd_4549205 2335928760836978948216093 := by
  unfold tailWord_4549205
  simp only [CollatzResearch.WordTrace]
  refine ⟨165923137484014702203569069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110615424989343134802379379 165923137484014702203569069)
  ·
    refine ⟨62221176556505513326338401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165923137484014702203569069 62221176556505513326338401)
    ·
      refine ⟨46665882417379134994753801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62221176556505513326338401 46665882417379134994753801)
      ·
        refine ⟨34999411813034351246065351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46665882417379134994753801 34999411813034351246065351)
        ·
          refine ⟨52499117719551526869098027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34999411813034351246065351 52499117719551526869098027)
          ·
            refine ⟨78748676579327290303647041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52499117719551526869098027 78748676579327290303647041)
            ·
              refine ⟨59061507434495467727735281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78748676579327290303647041 59061507434495467727735281)
              ·
                refine ⟨44296130575871600795801461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59061507434495467727735281 44296130575871600795801461)
                ·
                  refine ⟨4152762241487962574606387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44296130575871600795801461 4152762241487962574606387)
                  ·
                    refine ⟨6229143362231943861909581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4152762241487962574606387 6229143362231943861909581)
                    ·
                      refine ⟨2335928760836978948216093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229143362231943861909581 2335928760836978948216093)
                      ·
                        rfl

theorem cell23_4549205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4549205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549205 prefixEnd_4549205 := by exact prefixLift 4549205
  have htrace : WordTrace (prefixWord ++ tailWord_4549205) baseStart_4549205 baseEnd_4549205 := by
    simpa [prefixWord, tailWord_4549205, baseEnd_4549205] using wordTrace_append hprefix tailTrace_4549205
  have hstable : (prefixWord ++ tailWord_4549205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549205).length < 2 ^ (prefixWord ++ tailWord_4549205).sum := by decide
  have hdescent : baseEnd_4549205 < baseStart_4549205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_4549211 : Nat := 118140960795 + 4549211 * 2 ^ 59
def prefixEnd_4549211 : Nat := 4983230072969 + 3 ^ 40 * 4549211 * 2
def baseEnd_4549211 : Nat := 2335931841720905924741065

theorem tailTrace_4549211 : CollatzResearch.WordTrace tailWord_4549211 prefixEnd_4549211 2335931841720905924741065 := by
  unfold tailWord_4549211
  simp only [CollatzResearch.WordTrace]
  refine ⟨165923356321992965228287487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110615570881328643485524991 165923356321992965228287487)
  ·
    refine ⟨248885034482989447842431231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165923356321992965228287487 248885034482989447842431231)
    ·
      refine ⟨373327551724484171763646847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248885034482989447842431231 373327551724484171763646847)
      ·
        refine ⟨559991327586726257645470271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373327551724484171763646847 559991327586726257645470271)
        ·
          refine ⟨839986991380089386468205407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559991327586726257645470271 839986991380089386468205407)
          ·
            refine ⟨1259980487070134079702308111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 839986991380089386468205407 1259980487070134079702308111)
            ·
              refine ⟨1889970730605201119553462167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259980487070134079702308111 1889970730605201119553462167)
              ·
                refine ⟨2834956095907801679330193251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889970730605201119553462167 2834956095907801679330193251)
                ·
                  refine ⟨4252434143861702518995289877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834956095907801679330193251 4252434143861702518995289877)
                  ·
                    refine ⟨199332850493517305577904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4252434143861702518995289877 199332850493517305577904213)
                    ·
                      refine ⟨2335931841720905924741065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199332850493517305577904213 2335931841720905924741065)
                      ·
                        rfl

theorem cell23_4549211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_4549211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549211 prefixEnd_4549211 := by exact prefixLift 4549211
  have htrace : WordTrace (prefixWord ++ tailWord_4549211) baseStart_4549211 baseEnd_4549211 := by
    simpa [prefixWord, tailWord_4549211, baseEnd_4549211] using wordTrace_append hprefix tailTrace_4549211
  have hstable : (prefixWord ++ tailWord_4549211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549211).length < 2 ^ (prefixWord ++ tailWord_4549211).sum := by decide
  have hdescent : baseEnd_4549211 < baseStart_4549211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549272 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_4549272 : Nat := 118140960795 + 4549272 * 2 ^ 59
def prefixEnd_4549272 : Nat := 4983230072969 + 3 ^ 40 * 4549272 * 2
def baseEnd_4549272 : Nat := 778654388013610062026095

theorem tailTrace_4549272 : CollatzResearch.WordTrace tailWord_4549272 prefixEnd_4549272 778654388013610062026095 := by
  unfold tailWord_4549272
  simp only [CollatzResearch.WordTrace]
  refine ⟨82962790587385986323129035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110617054116514648430838713 82962790587385986323129035)
  ·
    refine ⟨124444185881078979484693553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82962790587385986323129035 124444185881078979484693553)
    ·
      refine ⟨93333139410809234613520165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124444185881078979484693553 93333139410809234613520165)
      ·
        refine ⟨17499963639526731490035031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93333139410809234613520165 17499963639526731490035031)
        ·
          refine ⟨26249945459290097235052547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17499963639526731490035031 26249945459290097235052547)
          ·
            refine ⟨39374918188935145852578821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26249945459290097235052547 39374918188935145852578821)
            ·
              refine ⟨7382797160425339847358529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39374918188935145852578821 7382797160425339847358529)
              ·
                refine ⟨5537097870319004885518897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382797160425339847358529 5537097870319004885518897)
                ·
                  refine ⟨4152823402739253664139173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537097870319004885518897 4152823402739253664139173)
                  ·
                    refine ⟨778654388013610062026095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4152823402739253664139173 778654388013610062026095)
                    ·
                      rfl

theorem cell23_4549272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_4549272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549272 prefixEnd_4549272 := by exact prefixLift 4549272
  have htrace : WordTrace (prefixWord ++ tailWord_4549272) baseStart_4549272 baseEnd_4549272 := by
    simpa [prefixWord, tailWord_4549272, baseEnd_4549272] using wordTrace_append hprefix tailTrace_4549272
  have hstable : (prefixWord ++ tailWord_4549272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549272).length < 2 ^ (prefixWord ++ tailWord_4549272).sum := by decide
  have hdescent : baseEnd_4549272 < baseStart_4549272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549295 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_4549295 : Nat := 118140960795 + 4549295 * 2 ^ 59
def prefixEnd_4549295 : Nat := 4983230072969 + 3 ^ 40 * 4549295 * 2
def baseEnd_4549295 : Nat := 2335974974095883596090679

theorem tailTrace_4549295 : CollatzResearch.WordTrace tailWord_4549295 prefixEnd_4549295 2335974974095883596090679 := by
  unfold tailWord_4549295
  simp only [CollatzResearch.WordTrace]
  refine ⟨165926420053688647574345339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110617613369125765049563559 165926420053688647574345339)
  ·
    refine ⟨248889630080532971361518009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165926420053688647574345339 248889630080532971361518009)
    ·
      refine ⟨186667222560399728521138507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248889630080532971361518009 186667222560399728521138507)
      ·
        refine ⟨280000833840599592781707761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186667222560399728521138507 280000833840599592781707761)
        ·
          refine ⟨210000625380449694586280821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280000833840599592781707761 210000625380449694586280821)
          ·
            refine ⟨19687558629417158867463827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210000625380449694586280821 19687558629417158867463827)
            ·
              refine ⟨29531337944125738301195741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19687558629417158867463827 29531337944125738301195741)
              ·
                refine ⟨11074251729047151862948403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29531337944125738301195741 11074251729047151862948403)
                ·
                  refine ⟨16611377593570727794422605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11074251729047151862948403 16611377593570727794422605)
                  ·
                    refine ⟨6229266597589022922908477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16611377593570727794422605 6229266597589022922908477)
                    ·
                      refine ⟨2335974974095883596090679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229266597589022922908477 2335974974095883596090679)
                      ·
                        rfl

theorem cell23_4549295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_4549295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549295 prefixEnd_4549295 := by exact prefixLift 4549295
  have htrace : WordTrace (prefixWord ++ tailWord_4549295) baseStart_4549295 baseEnd_4549295 := by
    simpa [prefixWord, tailWord_4549295, baseEnd_4549295] using wordTrace_append hprefix tailTrace_4549295
  have hstable : (prefixWord ++ tailWord_4549295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549295).length < 2 ^ (prefixWord ++ tailWord_4549295).sum := by decide
  have hdescent : baseEnd_4549295 < baseStart_4549295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549298 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_4549298 : Nat := 118140960795 + 4549298 * 2 ^ 59
def prefixEnd_4549298 : Nat := 4983230072969 + 3 ^ 40 * 4549298 * 2
def baseEnd_4549298 : Nat := 778658838179282361451055

theorem tailTrace_4549298 : CollatzResearch.WordTrace tailWord_4549298 prefixEnd_4549298 778658838179282361451055 := by
  unfold tailWord_4549298
  simp only [CollatzResearch.WordTrace]
  refine ⟨41481632368169444771676137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110617686315118519391136365 41481632368169444771676137)
  ·
    refine ⟨31111224276127083578757103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41481632368169444771676137 31111224276127083578757103)
    ·
      refine ⟨46666836414190625368135655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31111224276127083578757103 46666836414190625368135655)
      ·
        refine ⟨70000254621285938052203483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46666836414190625368135655 70000254621285938052203483)
        ·
          refine ⟨105000381931928907078305225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70000254621285938052203483 105000381931928907078305225)
          ·
            refine ⟨78750286448946680308728919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105000381931928907078305225 78750286448946680308728919)
            ·
              refine ⟨118125429673420020463093379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78750286448946680308728919 118125429673420020463093379)
              ·
                refine ⟨177188144510130030694640069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118125429673420020463093379 177188144510130030694640069)
                ·
                  refine ⟨33222777095649380755245013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177188144510130030694640069 33222777095649380755245013)
                  ·
                    refine ⟨778658838179282361451055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33222777095649380755245013 778658838179282361451055)
                    ·
                      rfl

theorem cell23_4549298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_4549298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549298 prefixEnd_4549298 := by exact prefixLift 4549298
  have htrace : WordTrace (prefixWord ++ tailWord_4549298) baseStart_4549298 baseEnd_4549298 := by
    simpa [prefixWord, tailWord_4549298, baseEnd_4549298] using wordTrace_append hprefix tailTrace_4549298
  have hstable : (prefixWord ++ tailWord_4549298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549298).length < 2 ^ (prefixWord ++ tailWord_4549298).sum := by decide
  have hdescent : baseEnd_4549298 < baseStart_4549298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549313 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4549313 : Nat := 118140960795 + 4549313 * 2 ^ 59
def prefixEnd_4549313 : Nat := 4983230072969 + 3 ^ 40 * 4549313 * 2
def baseEnd_4549313 : Nat := 2335984216747664525665597

theorem tailTrace_4549313 : CollatzResearch.WordTrace tailWord_4549313 prefixEnd_4549313 2335984216747664525665597 := by
  unfold tailWord_4549313
  simp only [CollatzResearch.WordTrace]
  refine ⟨165927076567623436648500593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110618051045082291099000395 165927076567623436648500593)
  ·
    refine ⟨124445307425717577486375445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165927076567623436648500593 124445307425717577486375445)
    ·
      refine ⟨5833373785580511444673849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124445307425717577486375445 5833373785580511444673849)
      ·
        refine ⟨4375030339185383583505387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5833373785580511444673849 4375030339185383583505387)
        ·
          refine ⟨6562545508778075375258081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375030339185383583505387 6562545508778075375258081)
          ·
            refine ⟨4921909131583556531443561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6562545508778075375258081 4921909131583556531443561)
            ·
              refine ⟨3691431848687667398582671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921909131583556531443561 3691431848687667398582671)
              ·
                refine ⟨5537147773031501097874007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691431848687667398582671 5537147773031501097874007)
                ·
                  refine ⟨8305721659547251646811011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5537147773031501097874007 8305721659547251646811011)
                  ·
                    refine ⟨12458582489320877470216517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8305721659547251646811011 12458582489320877470216517)
                    ·
                      refine ⟨2335984216747664525665597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12458582489320877470216517 2335984216747664525665597)
                      ·
                        rfl

theorem cell23_4549313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4549313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549313 prefixEnd_4549313 := by exact prefixLift 4549313
  have htrace : WordTrace (prefixWord ++ tailWord_4549313) baseStart_4549313 baseEnd_4549313 := by
    simpa [prefixWord, tailWord_4549313, baseEnd_4549313] using wordTrace_append hprefix tailTrace_4549313
  have hstable : (prefixWord ++ tailWord_4549313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549313).length < 2 ^ (prefixWord ++ tailWord_4549313).sum := by decide
  have hdescent : baseEnd_4549313 < baseStart_4549313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549316 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_4549316 : Nat := 118140960795 + 4549316 * 2 ^ 59
def prefixEnd_4549316 : Nat := 4983230072969 + 3 ^ 40 * 4549316 * 2
def baseEnd_4549316 : Nat := 2335985757189628013928083

theorem tailTrace_4549316 : CollatzResearch.WordTrace tailWord_4549316 prefixEnd_4549316 2335985757189628013928083 := by
  unfold tailWord_4549316
  simp only [CollatzResearch.WordTrace]
  refine ⟨82963592993306284080429901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110618123991075045440573201 82963592993306284080429901)
  ·
    refine ⟨31111347372489856530161213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82963592993306284080429901 31111347372489856530161213)
    ·
      refine ⟨11666755264683696198810455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31111347372489856530161213 11666755264683696198810455)
      ·
        refine ⟨17500132897025544298215683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11666755264683696198810455 17500132897025544298215683)
        ·
          refine ⟨26250199345538316447323525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17500132897025544298215683 26250199345538316447323525)
          ·
            refine ⟨4921912377288434333873161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26250199345538316447323525 4921912377288434333873161)
            ·
              refine ⟨3691434282966325750404871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921912377288434333873161 3691434282966325750404871)
              ·
                refine ⟨5537151424449488625607307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691434282966325750404871 5537151424449488625607307)
                ·
                  refine ⟨8305727136674232938410961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5537151424449488625607307 8305727136674232938410961)
                  ·
                    refine ⟨6229295352505674703808221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8305727136674232938410961 6229295352505674703808221)
                    ·
                      refine ⟨2335985757189628013928083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229295352505674703808221 2335985757189628013928083)
                      ·
                        rfl

theorem cell23_4549316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_4549316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549316 prefixEnd_4549316 := by exact prefixLift 4549316
  have htrace : WordTrace (prefixWord ++ tailWord_4549316) baseStart_4549316 baseEnd_4549316 := by
    simpa [prefixWord, tailWord_4549316, baseEnd_4549316] using wordTrace_append hprefix tailTrace_4549316
  have hstable : (prefixWord ++ tailWord_4549316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549316).length < 2 ^ (prefixWord ++ tailWord_4549316).sum := by decide
  have hdescent : baseEnd_4549316 < baseStart_4549316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549345 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_4549345 : Nat := 118140960795 + 4549345 * 2 ^ 59
def prefixEnd_4549345 : Nat := 4983230072969 + 3 ^ 40 * 4549345 * 2
def baseEnd_4549345 : Nat := 778666882709536133488483

theorem tailTrace_4549345 : CollatzResearch.WordTrace tailWord_4549345 prefixEnd_4549345 778666882709536133488483 := by
  unfold tailWord_4549345
  simp only [CollatzResearch.WordTrace]
  refine ⟨165928243703507506113665489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110618829135671670742443659 165928243703507506113665489)
  ·
    refine ⟨124446182777630629585249117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165928243703507506113665489 124446182777630629585249117)
    ·
      refine ⟨46667318541611486094468419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124446182777630629585249117 46667318541611486094468419)
      ·
        refine ⟨70000977812417229141702629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46667318541611486094468419 70000977812417229141702629)
        ·
          refine ⟨13125183339828230464069243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70000977812417229141702629 13125183339828230464069243)
          ·
            refine ⟨19687775009742345696103865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13125183339828230464069243 19687775009742345696103865)
            ·
              refine ⟨14765831257306759272077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19687775009742345696103865 14765831257306759272077899)
              ·
                refine ⟨22148746885960138908116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14765831257306759272077899 22148746885960138908116849)
                ·
                  refine ⟨16611560164470104181087637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22148746885960138908116849 16611560164470104181087637)
                  ·
                    refine ⟨778666882709536133488483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16611560164470104181087637 778666882709536133488483)
                    ·
                      rfl

theorem cell23_4549345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_4549345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549345 prefixEnd_4549345 := by exact prefixLift 4549345
  have htrace : WordTrace (prefixWord ++ tailWord_4549345) baseStart_4549345 baseEnd_4549345 := by
    simpa [prefixWord, tailWord_4549345, baseEnd_4549345] using wordTrace_append hprefix tailTrace_4549345
  have hstable : (prefixWord ++ tailWord_4549345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549345).length < 2 ^ (prefixWord ++ tailWord_4549345).sum := by decide
  have hdescent : baseEnd_4549345 < baseStart_4549345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549364 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4549364 : Nat := 118140960795 + 4549364 * 2 ^ 59
def prefixEnd_4549364 : Nat := 4983230072969 + 3 ^ 40 * 4549364 * 2
def baseEnd_4549364 : Nat := 2336010404261043826127863

theorem tailTrace_4549364 : CollatzResearch.WordTrace tailWord_4549364 prefixEnd_4549364 2336010404261043826127863 := by
  unfold tailWord_4549364
  simp only [CollatzResearch.WordTrace]
  refine ⟨82964468345219336179303573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110619291126959114905738097 82964468345219336179303573)
  ·
    refine ⟨3888959453682156383404855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82964468345219336179303573 3888959453682156383404855)
    ·
      refine ⟨5833439180523234575107283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888959453682156383404855 5833439180523234575107283)
      ·
        refine ⟨8750158770784851862660925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833439180523234575107283 8750158770784851862660925)
        ·
          refine ⟨3281309539044319448497847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8750158770784851862660925 3281309539044319448497847)
          ·
            refine ⟨4921964308566479172746771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281309539044319448497847 4921964308566479172746771)
            ·
              refine ⟨7382946462849718759120157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921964308566479172746771 7382946462849718759120157)
              ·
                refine ⟨2768604923568644534670059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7382946462849718759120157 2768604923568644534670059)
                ·
                  refine ⟨4152907385352966802005089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768604923568644534670059 4152907385352966802005089)
                  ·
                    refine ⟨3114680539014725101503817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4152907385352966802005089 3114680539014725101503817)
                    ·
                      refine ⟨2336010404261043826127863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114680539014725101503817 2336010404261043826127863)
                      ·
                        rfl

theorem cell23_4549364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4549364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549364 prefixEnd_4549364 := by exact prefixLift 4549364
  have htrace : WordTrace (prefixWord ++ tailWord_4549364) baseStart_4549364 baseEnd_4549364 := by
    simpa [prefixWord, tailWord_4549364, baseEnd_4549364] using wordTrace_append hprefix tailTrace_4549364
  have hstable : (prefixWord ++ tailWord_4549364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549364).length < 2 ^ (prefixWord ++ tailWord_4549364).sum := by decide
  have hdescent : baseEnd_4549364 < baseStart_4549364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549385 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_4549385 : Nat := 118140960795 + 4549385 * 2 ^ 59
def prefixEnd_4549385 : Nat := 4983230072969 + 3 ^ 40 * 4549385 * 2
def baseEnd_4549385 : Nat := 2336021187354788243965265

theorem tailTrace_4549385 : CollatzResearch.WordTrace tailWord_4549385 prefixEnd_4549385 2336021187354788243965265 := by
  unfold tailWord_4549385
  simp only [CollatzResearch.WordTrace]
  refine ⟨165929702623362592945121609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110619801748908395296747739 165929702623362592945121609)
  ·
    refine ⟨124447276967521944708841207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165929702623362592945121609 124447276967521944708841207)
    ·
      refine ⟨186670915451282917063261811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124447276967521944708841207 186670915451282917063261811)
      ·
        refine ⟨280006373176924375594892717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186670915451282917063261811 280006373176924375594892717)
        ·
          refine ⟨105002389941346640848084769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280006373176924375594892717 105002389941346640848084769)
          ·
            refine ⟨78751792456009980636063577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105002389941346640848084769 78751792456009980636063577)
            ·
              refine ⟨59063844342007485477047683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78751792456009980636063577 59063844342007485477047683)
              ·
                refine ⟨88595766513011228215571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59063844342007485477047683 88595766513011228215571525)
                ·
                  refine ⟨16611706221189605290419661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88595766513011228215571525 16611706221189605290419661)
                  ·
                    refine ⟨6229389832946101983907373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16611706221189605290419661 6229389832946101983907373)
                    ·
                      refine ⟨2336021187354788243965265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229389832946101983907373 2336021187354788243965265)
                      ·
                        rfl

theorem cell23_4549385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_4549385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549385 prefixEnd_4549385 := by exact prefixLift 4549385
  have htrace : WordTrace (prefixWord ++ tailWord_4549385) baseStart_4549385 baseEnd_4549385 := by
    simpa [prefixWord, tailWord_4549385, baseEnd_4549385] using wordTrace_append hprefix tailTrace_4549385
  have hstable : (prefixWord ++ tailWord_4549385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549385).length < 2 ^ (prefixWord ++ tailWord_4549385).sum := by decide
  have hdescent : baseEnd_4549385 < baseStart_4549385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549479 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_4549479 : Nat := 118140960795 + 4549479 * 2 ^ 59
def prefixEnd_4549479 : Nat := 4983230072969 + 3 ^ 40 * 4549479 * 2
def baseEnd_4549479 : Nat := 2336069454536310876189833

theorem tailTrace_4549479 : CollatzResearch.WordTrace tailWord_4549479 prefixEnd_4549479 2336069454536310876189833 := by
  unfold tailWord_4549479
  simp only [CollatzResearch.WordTrace]
  refine ⟨165933131085022046999043491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110622087390014697999362327 165933131085022046999043491)
  ·
    refine ⟨248899696627533070498565237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165933131085022046999043491 248899696627533070498565237)
    ·
      refine ⟨23334346558831225359240491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248899696627533070498565237 23334346558831225359240491)
      ·
        refine ⟨35001519838246838038860737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23334346558831225359240491 35001519838246838038860737)
        ·
          refine ⟨26251139878685128529145553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35001519838246838038860737 26251139878685128529145553)
          ·
            refine ⟨19688354909013846396859165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26251139878685128529145553 19688354909013846396859165)
            ·
              refine ⟨7383133090880192398822187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19688354909013846396859165 7383133090880192398822187)
              ·
                refine ⟨11074699636320288598233281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7383133090880192398822187 11074699636320288598233281)
                ·
                  refine ⟨8306024727240216448674961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11074699636320288598233281 8306024727240216448674961)
                  ·
                    refine ⟨6229518545430162336506221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8306024727240216448674961 6229518545430162336506221)
                    ·
                      refine ⟨2336069454536310876189833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229518545430162336506221 2336069454536310876189833)
                      ·
                        rfl

theorem cell23_4549479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_4549479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549479 prefixEnd_4549479 := by exact prefixLift 4549479
  have htrace : WordTrace (prefixWord ++ tailWord_4549479) baseStart_4549479 baseEnd_4549479 := by
    simpa [prefixWord, tailWord_4549479, baseEnd_4549479] using wordTrace_append hprefix tailTrace_4549479
  have hstable : (prefixWord ++ tailWord_4549479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549479).length < 2 ^ (prefixWord ++ tailWord_4549479).sum := by decide
  have hdescent : baseEnd_4549479 < baseStart_4549479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549509 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_4549509 : Nat := 118140960795 + 4549509 * 2 ^ 59
def prefixEnd_4549509 : Nat := 4983230072969 + 3 ^ 40 * 4549509 * 2
def baseEnd_4549509 : Nat := 2336084858955945758814695

theorem tailTrace_4549509 : CollatzResearch.WordTrace tailWord_4549509 prefixEnd_4549509 2336084858955945758814695 := by
  unfold tailWord_4549509
  simp only [CollatzResearch.WordTrace]
  refine ⟨165934225274913362122635581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110622816849942241415090387 165934225274913362122635581)
  ·
    refine ⟨62225334478092510795988343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165934225274913362122635581 62225334478092510795988343)
    ·
      refine ⟨93338001717138766193982515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62225334478092510795988343 93338001717138766193982515)
      ·
        refine ⟨140007002575708149290973773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93338001717138766193982515 140007002575708149290973773)
        ·
          refine ⟨52502625965890555984115165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140007002575708149290973773 52502625965890555984115165)
          ·
            refine ⟨19688484737208958494043187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52502625965890555984115165 19688484737208958494043187)
            ·
              refine ⟨29532727105813437741064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19688484737208958494043187 29532727105813437741064781)
              ·
                refine ⟨11074772664680039152899293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29532727105813437741064781 11074772664680039152899293)
                ·
                  refine ⟨4153039749255014682337235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11074772664680039152899293 4153039749255014682337235)
                  ·
                    refine ⟨6229559623882522023505853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4153039749255014682337235 6229559623882522023505853)
                    ·
                      refine ⟨2336084858955945758814695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229559623882522023505853 2336084858955945758814695)
                      ·
                        rfl

theorem cell23_4549509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_4549509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549509 prefixEnd_4549509 := by exact prefixLift 4549509
  have htrace : WordTrace (prefixWord ++ tailWord_4549509) baseStart_4549509 baseEnd_4549509 := by
    simpa [prefixWord, tailWord_4549509, baseEnd_4549509] using wordTrace_append hprefix tailTrace_4549509
  have hstable : (prefixWord ++ tailWord_4549509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549509).length < 2 ^ (prefixWord ++ tailWord_4549509).sum := by decide
  have hdescent : baseEnd_4549509 < baseStart_4549509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549576 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_4549576 : Nat := 118140960795 + 4549576 * 2 ^ 59
def prefixEnd_4549576 : Nat := 4983230072969 + 3 ^ 40 * 4549576 * 2
def baseEnd_4549576 : Nat := 778706420719932332225629

theorem tailTrace_4549576 : CollatzResearch.WordTrace tailWord_4549576 prefixEnd_4549576 778706420719932332225629 := by
  unfold tailWord_4549576
  simp only [CollatzResearch.WordTrace]
  refine ⟨82968334482835316282662291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110624445977113755043549721 82968334482835316282662291)
  ·
    refine ⟨124452501724252974423993437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82968334482835316282662291 124452501724252974423993437)
    ·
      refine ⟨46669688146594865408997539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124452501724252974423993437 46669688146594865408997539)
      ·
        refine ⟨70004532219892298113496309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46669688146594865408997539 70004532219892298113496309)
        ·
          refine ⟨6562924895614902948140279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70004532219892298113496309 6562924895614902948140279)
          ·
            refine ⟨9844387343422354422210419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562924895614902948140279 9844387343422354422210419)
            ·
              refine ⟨14766581015133531633315629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9844387343422354422210419 14766581015133531633315629)
              ·
                refine ⟨5537467880675074362493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14766581015133531633315629 5537467880675074362493361)
                ·
                  refine ⟨4153100910506305771870021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537467880675074362493361 4153100910506305771870021)
                  ·
                    refine ⟨778706420719932332225629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153100910506305771870021 778706420719932332225629)
                    ·
                      rfl

theorem cell23_4549576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_4549576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549576 prefixEnd_4549576 := by exact prefixLift 4549576
  have htrace : WordTrace (prefixWord ++ tailWord_4549576) baseStart_4549576 baseEnd_4549576 := by
    simpa [prefixWord, tailWord_4549576, baseEnd_4549576] using wordTrace_append hprefix tailTrace_4549576
  have hstable : (prefixWord ++ tailWord_4549576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549576).length < 2 ^ (prefixWord ++ tailWord_4549576).sum := by decide
  have hdescent : baseEnd_4549576 < baseStart_4549576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549586 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4549586 : Nat := 118140960795 + 4549586 * 2 ^ 59
def prefixEnd_4549586 : Nat := 4983230072969 + 3 ^ 40 * 4549586 * 2
def baseEnd_4549586 : Nat := 2336124396966341957551841

theorem tailTrace_4549586 : CollatzResearch.WordTrace tailWord_4549586 prefixEnd_4549586 2336124396966341957551841 := by
  unfold tailWord_4549586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41484258423908601068297153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110624689130422936182125741 41484258423908601068297153)
  ·
    refine ⟨31113193817931450801222865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41484258423908601068297153 31113193817931450801222865)
    ·
      refine ⟨23334895363448588100917149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31113193817931450801222865 23334895363448588100917149)
      ·
        refine ⟨8750585761293220537843931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23334895363448588100917149 8750585761293220537843931)
        ·
          refine ⟨13125878641939830806765897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750585761293220537843931 13125878641939830806765897)
          ·
            refine ⟨9844408981454873105074423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13125878641939830806765897 9844408981454873105074423)
            ·
              refine ⟨14766613472182309657611635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9844408981454873105074423 14766613472182309657611635)
              ·
                refine ⟨22149920208273464486417453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14766613472182309657611635 22149920208273464486417453)
                ·
                  refine ⟨8306220078102549182406545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22149920208273464486417453 8306220078102549182406545)
                  ·
                    refine ⟨6229665058576911886804909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8306220078102549182406545 6229665058576911886804909)
                    ·
                      refine ⟨2336124396966341957551841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6229665058576911886804909 2336124396966341957551841)
                      ·
                        rfl

theorem cell23_4549586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4549586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549586 prefixEnd_4549586 := by exact prefixLift 4549586
  have htrace : WordTrace (prefixWord ++ tailWord_4549586) baseStart_4549586 baseEnd_4549586 := by
    simpa [prefixWord, tailWord_4549586, baseEnd_4549586] using wordTrace_append hprefix tailTrace_4549586
  have hstable : (prefixWord ++ tailWord_4549586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549586).length < 2 ^ (prefixWord ++ tailWord_4549586).sum := by decide
  have hdescent : baseEnd_4549586 < baseStart_4549586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549617 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_4549617 : Nat := 118140960795 + 4549617 * 2 ^ 59
def prefixEnd_4549617 : Nat := 4983230072969 + 3 ^ 40 * 4549617 * 2
def baseEnd_4549617 : Nat := 2336140314866631336264199

theorem tailTrace_4549617 : CollatzResearch.WordTrace tailWord_4549617 prefixEnd_4549617 2336140314866631336264199 := by
  unfold tailWord_4549617
  simp only [CollatzResearch.WordTrace]
  refine ⟨165938164358522096567567105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110625442905681397711711403 165938164358522096567567105)
  ·
    refine ⟨124453623268891572425675329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165938164358522096567567105 124453623268891572425675329)
    ·
      refine ⟨93340217451668679319256497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124453623268891572425675329 93340217451668679319256497)
      ·
        refine ⟨70005163088751509489442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93340217451668679319256497 70005163088751509489442373)
        ·
          refine ⟨13125968079140908029270445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70005163088751509489442373 13125968079140908029270445)
          ·
            refine ⟨4922238029677840510976417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13125968079140908029270445 4922238029677840510976417)
            ·
              refine ⟨3691678522258380383232313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4922238029677840510976417 3691678522258380383232313)
              ·
                refine ⟨2768758891693785287424235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691678522258380383232313 2768758891693785287424235)
                ·
                  refine ⟨4153138337540677931136353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768758891693785287424235 4153138337540677931136353)
                  ·
                    refine ⟨3114853753155508448352265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4153138337540677931136353 3114853753155508448352265)
                    ·
                      refine ⟨2336140314866631336264199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114853753155508448352265 2336140314866631336264199)
                      ·
                        rfl

theorem cell23_4549617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_4549617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549617 prefixEnd_4549617 := by exact prefixLift 4549617
  have htrace : WordTrace (prefixWord ++ tailWord_4549617) baseStart_4549617 baseEnd_4549617 := by
    simpa [prefixWord, tailWord_4549617, baseEnd_4549617] using wordTrace_append hprefix tailTrace_4549617
  have hstable : (prefixWord ++ tailWord_4549617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549617).length < 2 ^ (prefixWord ++ tailWord_4549617).sum := by decide
  have hdescent : baseEnd_4549617 < baseStart_4549617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549656 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_4549656 : Nat := 118140960795 + 4549656 * 2 ^ 59
def prefixEnd_4549656 : Nat := 4983230072969 + 3 ^ 40 * 4549656 * 2
def baseEnd_4549656 : Nat := 2336160340612156683676519

theorem tailTrace_4549656 : CollatzResearch.WordTrace tailWord_4549656 prefixEnd_4549656 2336160340612156683676519 := by
  unfold tailWord_4549656
  simp only [CollatzResearch.WordTrace]
  refine ⟨82969793402690403114118411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110626391203587204152157881 82969793402690403114118411)
  ·
    refine ⟨124454690104035604671177617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82969793402690403114118411 124454690104035604671177617)
    ·
      refine ⟨93341017578026703503383213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124454690104035604671177617 93341017578026703503383213)
      ·
        refine ⟨35002881591760013813768705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93341017578026703503383213 35002881591760013813768705)
        ·
          refine ⟨26252161193820010360326529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35002881591760013813768705 26252161193820010360326529)
          ·
            refine ⟨19689120895365007770244897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26252161193820010360326529 19689120895365007770244897)
            ·
              refine ⟨14766840671523755827683673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19689120895365007770244897 14766840671523755827683673)
              ·
                refine ⟨11075130503642816870762755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14766840671523755827683673 11075130503642816870762755)
                ·
                  refine ⟨16612695755464225306144133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11075130503642816870762755 16612695755464225306144133)
                  ·
                    refine ⟨3114880454149542244902025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16612695755464225306144133 3114880454149542244902025)
                    ·
                      refine ⟨2336160340612156683676519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114880454149542244902025 2336160340612156683676519)
                      ·
                        rfl

theorem cell23_4549656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_4549656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549656 prefixEnd_4549656 := by exact prefixLift 4549656
  have htrace : WordTrace (prefixWord ++ tailWord_4549656) baseStart_4549656 baseEnd_4549656 := by
    simpa [prefixWord, tailWord_4549656, baseEnd_4549656] using wordTrace_append hprefix tailTrace_4549656
  have hstable : (prefixWord ++ tailWord_4549656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549656).length < 2 ^ (prefixWord ++ tailWord_4549656).sum := by decide
  have hdescent : baseEnd_4549656 < baseStart_4549656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549686 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4549686 : Nat := 118140960795 + 4549686 * 2 ^ 59
def prefixEnd_4549686 : Nat := 4983230072969 + 3 ^ 40 * 4549686 * 2
def baseEnd_4549686 : Nat := 2336175745031791566301381

theorem tailTrace_4549686 : CollatzResearch.WordTrace tailWord_4549686 prefixEnd_4549686 2336175745031791566301381 := by
  unfold tailWord_4549686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371292562204507584489307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110627120663514747567885941 10371292562204507584489307)
  ·
    refine ⟨15556938843306761376733961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10371292562204507584489307 15556938843306761376733961)
    ·
      refine ⟨11667704132480071032550471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15556938843306761376733961 11667704132480071032550471)
      ·
        refine ⟨17501556198720106548825707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11667704132480071032550471 17501556198720106548825707)
        ·
          refine ⟨26252334298080159823238561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17501556198720106548825707 26252334298080159823238561)
          ·
            refine ⟨19689250723560119867428921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26252334298080159823238561 19689250723560119867428921)
            ·
              refine ⟨14766938042670089900571691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19689250723560119867428921 14766938042670089900571691)
              ·
                refine ⟨22150407064005134850857537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14766938042670089900571691 22150407064005134850857537)
                ·
                  refine ⟨16612805298003851138143153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22150407064005134850857537 16612805298003851138143153)
                  ·
                    refine ⟨12459603973502888353607365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16612805298003851138143153 12459603973502888353607365)
                    ·
                      refine ⟨2336175745031791566301381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12459603973502888353607365 2336175745031791566301381)
                      ·
                        rfl

theorem cell23_4549686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4549686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549686 prefixEnd_4549686 := by exact prefixLift 4549686
  have htrace : WordTrace (prefixWord ++ tailWord_4549686) baseStart_4549686 baseEnd_4549686 := by
    simpa [prefixWord, tailWord_4549686, baseEnd_4549686] using wordTrace_append hprefix tailTrace_4549686
  have hstable : (prefixWord ++ tailWord_4549686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549686).length < 2 ^ (prefixWord ++ tailWord_4549686).sum := by decide
  have hdescent : baseEnd_4549686 < baseStart_4549686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549729 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_4549729 : Nat := 118140960795 + 4549729 * 2 ^ 59
def prefixEnd_4549729 : Nat := 4983230072969 + 3 ^ 40 * 4549729 * 2
def baseEnd_4549729 : Nat := 2336197824699934898063683

theorem tailTrace_4549729 : CollatzResearch.WordTrace tailWord_4549729 prefixEnd_4549729 2336197824699934898063683 := by
  unfold tailWord_4549729
  simp only [CollatzResearch.WordTrace]
  refine ⟨165942249334116339695644241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110628166222744226463762827 165942249334116339695644241)
  ·
    refine ⟨124456687000587254771733181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165942249334116339695644241 124456687000587254771733181)
    ·
      refine ⟨46671257625220220539399943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124456687000587254771733181 46671257625220220539399943)
      ·
        refine ⟨70006886437830330809099915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46671257625220220539399943 70006886437830330809099915)
        ·
          refine ⟨105010329656745496213649873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70006886437830330809099915 105010329656745496213649873)
          ·
            refine ⟨78757747242559122160237405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105010329656745496213649873 78757747242559122160237405)
            ·
              refine ⟨29534155215959670810089027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78757747242559122160237405 29534155215959670810089027)
              ·
                refine ⟨44301232823939506215133541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29534155215959670810089027 44301232823939506215133541)
                ·
                  refine ⟨8306481154488657415337539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44301232823939506215133541 8306481154488657415337539)
                  ·
                    refine ⟨12459721731732986123006309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8306481154488657415337539 12459721731732986123006309)
                    ·
                      refine ⟨2336197824699934898063683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12459721731732986123006309 2336197824699934898063683)
                      ·
                        rfl

theorem cell23_4549729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_4549729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549729 prefixEnd_4549729 := by exact prefixLift 4549729
  have htrace : WordTrace (prefixWord ++ tailWord_4549729) baseStart_4549729 baseEnd_4549729 := by
    simpa [prefixWord, tailWord_4549729, baseEnd_4549729] using wordTrace_append hprefix tailTrace_4549729
  have hstable : (prefixWord ++ tailWord_4549729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549729).length < 2 ^ (prefixWord ++ tailWord_4549729).sum := by decide
  have hdescent : baseEnd_4549729 < baseStart_4549729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549730 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_4549730 : Nat := 118140960795 + 4549730 * 2 ^ 59
def prefixEnd_4549730 : Nat := 4983230072969 + 3 ^ 40 * 4549730 * 2
def baseEnd_4549730 : Nat := 259577593131176599350131

theorem tailTrace_4549730 : CollatzResearch.WordTrace tailWord_4549730 prefixEnd_4549730 259577593131176599350131 := by
  unfold tailWord_4549730
  simp only [CollatzResearch.WordTrace]
  refine ⟨41485571451778179216607661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110628190538075144577620429 41485571451778179216607661)
  ·
    refine ⟨15557089294416817206227873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41485571451778179216607661 15557089294416817206227873)
    ·
      refine ⟨11667816970812612904670905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15557089294416817206227873 11667816970812612904670905)
      ·
        refine ⟨8750862728109459678503179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11667816970812612904670905 8750862728109459678503179)
        ·
          refine ⟨13126294092164189517754769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750862728109459678503179 13126294092164189517754769)
          ·
            refine ⟨9844720569123142138316077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13126294092164189517754769 9844720569123142138316077)
            ·
              refine ⟨3691770213421178301868529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9844720569123142138316077 3691770213421178301868529)
              ·
                refine ⟨2768827660065883726401397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691770213421178301868529 2768827660065883726401397)
                ·
                  refine ⟨259577593131176599350131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768827660065883726401397 259577593131176599350131)
                  ·
                    rfl

theorem cell23_4549730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_4549730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549730 prefixEnd_4549730 := by exact prefixLift 4549730
  have htrace : WordTrace (prefixWord ++ tailWord_4549730) baseStart_4549730 baseEnd_4549730 := by
    simpa [prefixWord, tailWord_4549730, baseEnd_4549730] using wordTrace_append hprefix tailTrace_4549730
  have hstable : (prefixWord ++ tailWord_4549730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549730).length < 2 ^ (prefixWord ++ tailWord_4549730).sum := by decide
  have hdescent : baseEnd_4549730 < baseStart_4549730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549746 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_4549746 : Nat := 118140960795 + 4549746 * 2 ^ 59
def prefixEnd_4549746 : Nat := 4983230072969 + 3 ^ 40 * 4549746 * 2
def baseEnd_4549746 : Nat := 2336206553871061331551105

theorem tailTrace_4549746 : CollatzResearch.WordTrace tailWord_4549746 prefixEnd_4549746 2336206553871061331551105 := by
  unfold tailWord_4549746
  simp only [CollatzResearch.WordTrace]
  refine ⟨41485717343763687899753273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110628579583369834399342061 41485717343763687899753273)
  ·
    refine ⟨31114288007822765924814955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41485717343763687899753273 31114288007822765924814955)
    ·
      refine ⟨46671432011734148887222433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31114288007822765924814955 46671432011734148887222433)
      ·
        refine ⟨35003574008800611665416825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46671432011734148887222433 35003574008800611665416825)
        ·
          refine ⟨26252680506600458749062619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35003574008800611665416825 26252680506600458749062619)
          ·
            refine ⟨39379020759900688123593929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26252680506600458749062619 39379020759900688123593929)
            ·
              refine ⟨29534265569925516092695447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39379020759900688123593929 29534265569925516092695447)
              ·
                refine ⟨44301398354888274139043171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29534265569925516092695447 44301398354888274139043171)
                ·
                  refine ⟨66452097532332411208564757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44301398354888274139043171 66452097532332411208564757)
                  ·
                    refine ⟨3114942071828081775401473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66452097532332411208564757 3114942071828081775401473)
                    ·
                      refine ⟨2336206553871061331551105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114942071828081775401473 2336206553871061331551105)
                      ·
                        rfl

theorem cell23_4549746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_4549746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549746 prefixEnd_4549746 := by exact prefixLift 4549746
  have htrace : WordTrace (prefixWord ++ tailWord_4549746) baseStart_4549746 baseEnd_4549746 := by
    simpa [prefixWord, tailWord_4549746, baseEnd_4549746] using wordTrace_append hprefix tailTrace_4549746
  have hstable : (prefixWord ++ tailWord_4549746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549746).length < 2 ^ (prefixWord ++ tailWord_4549746).sum := by decide
  have hdescent : baseEnd_4549746 < baseStart_4549746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549786 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_4549786 : Nat := 118140960795 + 4549786 * 2 ^ 59
def prefixEnd_4549786 : Nat := 4983230072969 + 3 ^ 40 * 4549786 * 2
def baseEnd_4549786 : Nat := 259580788121915686116769

theorem tailTrace_4549786 : CollatzResearch.WordTrace tailWord_4549786 prefixEnd_4549786 259580788121915686116769 := by
  unfold tailWord_4549786
  simp only [CollatzResearch.WordTrace]
  refine ⟨41486082073727459607617303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110629552196606558953646141 41486082073727459607617303)
  ·
    refine ⟨62229123110591189411425955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41486082073727459607617303 62229123110591189411425955)
    ·
      refine ⟨93343684665886784117138933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62229123110591189411425955 93343684665886784117138933)
      ·
        refine ⟨8750970437426886010981775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93343684665886784117138933 8750970437426886010981775)
        ·
          refine ⟨13126455656140329016472663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750970437426886010981775 13126455656140329016472663)
          ·
            refine ⟨19689683484210493524708995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13126455656140329016472663 19689683484210493524708995)
            ·
              refine ⟨29534525226315740287063493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19689683484210493524708995 29534525226315740287063493)
              ·
                refine ⟨5537723479934201303824405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29534525226315740287063493 5537723479934201303824405)
                ·
                  refine ⟨259580788121915686116769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5537723479934201303824405 259580788121915686116769)
                  ·
                    rfl

theorem cell23_4549786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_4549786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549786 prefixEnd_4549786 := by exact prefixLift 4549786
  have htrace : WordTrace (prefixWord ++ tailWord_4549786) baseStart_4549786 baseEnd_4549786 := by
    simpa [prefixWord, tailWord_4549786, baseEnd_4549786] using wordTrace_append hprefix tailTrace_4549786
  have hstable : (prefixWord ++ tailWord_4549786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549786).length < 2 ^ (prefixWord ++ tailWord_4549786).sum := by decide
  have hdescent : baseEnd_4549786 < baseStart_4549786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549789 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4549789 : Nat := 118140960795 + 4549789 * 2 ^ 59
def prefixEnd_4549789 : Nat := 4983230072969 + 3 ^ 40 * 4549789 * 2
def baseEnd_4549789 : Nat := 2336228633539204663313407

theorem tailTrace_4549789 : CollatzResearch.WordTrace tailWord_4549789 prefixEnd_4549789 2336228633539204663313407 := by
  unfold tailWord_4549789
  simp only [CollatzResearch.WordTrace]
  refine ⟨165944437713898969942828421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110629625142599313295218947 165944437713898969942828421)
  ·
    refine ⟨31114582071356056864280329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165944437713898969942828421 31114582071356056864280329)
    ·
      refine ⟨23335936553517042648210247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31114582071356056864280329 23335936553517042648210247)
      ·
        refine ⟨35003904830275563972315371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23335936553517042648210247 35003904830275563972315371)
        ·
          refine ⟨52505857245413345958473057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35003904830275563972315371 52505857245413345958473057)
          ·
            refine ⟨39379392934060009468854793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52505857245413345958473057 39379392934060009468854793)
            ·
              refine ⟨29534544700545007101641095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39379392934060009468854793 29534544700545007101641095)
              ·
                refine ⟨44301817050817510652461643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29534544700545007101641095 44301817050817510652461643)
                ·
                  refine ⟨66452725576226265978692465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44301817050817510652461643 66452725576226265978692465)
                  ·
                    refine ⟨49839544182169699484019349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66452725576226265978692465 49839544182169699484019349)
                    ·
                      refine ⟨2336228633539204663313407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49839544182169699484019349 2336228633539204663313407)
                      ·
                        rfl

theorem cell23_4549789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4549789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549789 prefixEnd_4549789 := by exact prefixLift 4549789
  have htrace : WordTrace (prefixWord ++ tailWord_4549789) baseStart_4549789 baseEnd_4549789 := by
    simpa [prefixWord, tailWord_4549789, baseEnd_4549789] using wordTrace_append hprefix tailTrace_4549789
  have hstable : (prefixWord ++ tailWord_4549789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549789).length < 2 ^ (prefixWord ++ tailWord_4549789).sum := by decide
  have hdescent : baseEnd_4549789 < baseStart_4549789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549814 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4549814 : Nat := 118140960795 + 4549814 * 2 ^ 59
def prefixEnd_4549814 : Nat := 4983230072969 + 3 ^ 40 * 4549814 * 2
def baseEnd_4549814 : Nat := 2336241470555567065500793

theorem tailTrace_4549814 : CollatzResearch.WordTrace tailWord_4549814 prefixEnd_4549814 2336241470555567065500793 := by
  unfold tailWord_4549814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10371584346175524950780531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110630233025872266141658997 10371584346175524950780531)
  ·
    refine ⟨15557376519263287426170797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10371584346175524950780531 15557376519263287426170797)
    ·
      refine ⟨5834016194723732784814049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15557376519263287426170797 5834016194723732784814049)
      ·
        refine ⟨4375512146042799588610537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834016194723732784814049 4375512146042799588610537)
        ·
          refine ⟨3281634109532099691457903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4375512146042799588610537 3281634109532099691457903)
          ·
            refine ⟨4922451164298149537186855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281634109532099691457903 4922451164298149537186855)
            ·
              refine ⟨7383676746447224305780283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922451164298149537186855 7383676746447224305780283)
              ·
                refine ⟨11075515119670836458670425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7383676746447224305780283 11075515119670836458670425)
                ·
                  refine ⟨8306636339753127344002819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11075515119670836458670425 8306636339753127344002819)
                  ·
                    refine ⟨12459954509629691016004229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8306636339753127344002819 12459954509629691016004229)
                    ·
                      refine ⟨2336241470555567065500793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12459954509629691016004229 2336241470555567065500793)
                      ·
                        rfl

theorem cell23_4549814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4549814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549814 prefixEnd_4549814 := by exact prefixLift 4549814
  have htrace : WordTrace (prefixWord ++ tailWord_4549814) baseStart_4549814 baseEnd_4549814 := by
    simpa [prefixWord, tailWord_4549814, baseEnd_4549814] using wordTrace_append hprefix tailTrace_4549814
  have hstable : (prefixWord ++ tailWord_4549814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549814).length < 2 ^ (prefixWord ++ tailWord_4549814).sum := by decide
  have hdescent : baseEnd_4549814 < baseStart_4549814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549823 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 2, 3, 2]
def baseStart_4549823 : Nat := 118140960795 + 4549823 * 2 ^ 59
def prefixEnd_4549823 : Nat := 4983230072969 + 3 ^ 40 * 4549823 * 2
def baseEnd_4549823 : Nat := 2336246091881457530288251

theorem tailTrace_4549823 : CollatzResearch.WordTrace tailWord_4549823 prefixEnd_4549823 2336246091881457530288251 := by
  unfold tailWord_4549823
  simp only [CollatzResearch.WordTrace]
  refine ⟨165945677795775793749566123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110630451863850529166377415 165945677795775793749566123)
  ·
    refine ⟨248918516693663690624349185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165945677795775793749566123 248918516693663690624349185)
    ·
      refine ⟨186688887520247767968261889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248918516693663690624349185 186688887520247767968261889)
      ·
        refine ⟨140016665640185825976196417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186688887520247767968261889 140016665640185825976196417)
        ·
          refine ⟨105012499230139369482147313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140016665640185825976196417 105012499230139369482147313)
          ·
            refine ⟨78759374422604527111610485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105012499230139369482147313 78759374422604527111610485)
            ·
              refine ⟨7383691352119174416713483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78759374422604527111610485 7383691352119174416713483)
              ·
                refine ⟨11075537028178761625070225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7383691352119174416713483 11075537028178761625070225)
                ·
                  refine ⟨8306652771134071218802669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11075537028178761625070225 8306652771134071218802669)
                  ·
                    refine ⟨3114994789175276707051001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8306652771134071218802669 3114994789175276707051001)
                    ·
                      refine ⟨2336246091881457530288251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3114994789175276707051001 2336246091881457530288251)
                      ·
                        rfl

theorem cell23_4549823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_4549823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549823 prefixEnd_4549823 := by exact prefixLift 4549823
  have htrace : WordTrace (prefixWord ++ tailWord_4549823) baseStart_4549823 baseEnd_4549823 := by
    simpa [prefixWord, tailWord_4549823, baseEnd_4549823] using wordTrace_append hprefix tailTrace_4549823
  have hstable : (prefixWord ++ tailWord_4549823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549823).length < 2 ^ (prefixWord ++ tailWord_4549823).sum := by decide
  have hdescent : baseEnd_4549823 < baseStart_4549823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549837 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 6]
def baseStart_4549837 : Nat := 118140960795 + 4549837 * 2 ^ 59
def prefixEnd_4549837 : Nat := 4983230072969 + 3 ^ 40 * 4549837 * 2
def baseEnd_4549837 : Nat := 259583697845624497279243

theorem tailTrace_4549837 : CollatzResearch.WordTrace tailWord_4549837 prefixEnd_4549837 259583697845624497279243 := by
  unfold tailWord_4549837
  simp only [CollatzResearch.WordTrace]
  refine ⟨165946188417725074140575765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110630792278483382760383843 165946188417725074140575765)
  ·
    refine ⟨7778727582080862850339489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165946188417725074140575765 7778727582080862850339489)
    ·
      refine ⟨5834045686560647137754617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7778727582080862850339489 5834045686560647137754617)
      ·
        refine ⟨4375534264920485353315963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834045686560647137754617 4375534264920485353315963)
        ·
          refine ⟨6563301397380728029973945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375534264920485353315963 6563301397380728029973945)
          ·
            refine ⟨4922476048035546022480459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6563301397380728029973945 4922476048035546022480459)
            ·
              refine ⟨7383714072053319033720689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922476048035546022480459 7383714072053319033720689)
              ·
                refine ⟨5537785554039989275290517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7383714072053319033720689 5537785554039989275290517)
                ·
                  refine ⟨259583697845624497279243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5537785554039989275290517 259583697845624497279243)
                  ·
                    rfl

theorem cell23_4549837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_4549837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549837 prefixEnd_4549837 := by exact prefixLift 4549837
  have htrace : WordTrace (prefixWord ++ tailWord_4549837) baseStart_4549837 baseEnd_4549837 := by
    simpa [prefixWord, tailWord_4549837, baseEnd_4549837] using wordTrace_append hprefix tailTrace_4549837
  have hstable : (prefixWord ++ tailWord_4549837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549837).length < 2 ^ (prefixWord ++ tailWord_4549837).sum := by decide
  have hdescent : baseEnd_4549837 < baseStart_4549837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549849 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_4549849 : Nat := 118140960795 + 4549849 * 2 ^ 59
def prefixEnd_4549849 : Nat := 4983230072969 + 3 ^ 40 * 4549849 * 2
def baseEnd_4549849 : Nat := 2336259442378474428563131

theorem tailTrace_4549849 : CollatzResearch.WordTrace tailWord_4549849 prefixEnd_4549849 2336259442378474428563131 := by
  unfold tailWord_4549849
  simp only [CollatzResearch.WordTrace]
  refine ⟨165946626093681600190012601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110631084062454400126675067 165946626093681600190012601)
  ·
    refine ⟨124459969570261200142509451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165946626093681600190012601 124459969570261200142509451)
    ·
      refine ⟨186689954355391800213764177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124459969570261200142509451 186689954355391800213764177)
      ·
        refine ⟨140017465766543850160323133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186689954355391800213764177 140017465766543850160323133)
        ·
          refine ⟨52506549662453943810121175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140017465766543850160323133 52506549662453943810121175)
          ·
            refine ⟨78759824493680915715181763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52506549662453943810121175 78759824493680915715181763)
            ·
              refine ⟨118139736740521373572772645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78759824493680915715181763 118139736740521373572772645)
              ·
                refine ⟨22151200638847757544894871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118139736740521373572772645 22151200638847757544894871)
                ·
                  refine ⟨33226800958271636317342307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22151200638847757544894871 33226800958271636317342307)
                  ·
                    refine ⟨49840201437407454476013461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33226800958271636317342307 49840201437407454476013461)
                    ·
                      refine ⟨2336259442378474428563131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49840201437407454476013461 2336259442378474428563131)
                      ·
                        rfl

theorem cell23_4549849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_4549849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549849 prefixEnd_4549849 := by exact prefixLift 4549849
  have htrace : WordTrace (prefixWord ++ tailWord_4549849) baseStart_4549849 baseEnd_4549849 := by
    simpa [prefixWord, tailWord_4549849, baseEnd_4549849] using wordTrace_append hprefix tailTrace_4549849
  have hstable : (prefixWord ++ tailWord_4549849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549849).length < 2 ^ (prefixWord ++ tailWord_4549849).sum := by decide
  have hdescent : baseEnd_4549849 < baseStart_4549849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549856 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_4549856 : Nat := 118140960795 + 4549856 * 2 ^ 59
def prefixEnd_4549856 : Nat := 4983230072969 + 3 ^ 40 * 4549856 * 2
def baseEnd_4549856 : Nat := 2336263036743055901175599

theorem tailTrace_4549856 : CollatzResearch.WordTrace tailWord_4549856 prefixEnd_4549856 2336263036743055901175599 := by
  unfold tailWord_4549856
  simp only [CollatzResearch.WordTrace]
  refine ⟨82973440702328120192758711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110631254269770826923678281 82973440702328120192758711)
  ·
    refine ⟨124460161053492180289138067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82973440702328120192758711 124460161053492180289138067)
    ·
      refine ⟨186690241580238270433707101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124460161053492180289138067 186690241580238270433707101)
      ·
        refine ⟨70008840592589351412640163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186690241580238270433707101 70008840592589351412640163)
        ·
          refine ⟨105013260888884027118960245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70008840592589351412640163 105013260888884027118960245)
          ·
            refine ⟨9844993208332877542402523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105013260888884027118960245 9844993208332877542402523)
            ·
              refine ⟨14767489812499316313603785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9844993208332877542402523 14767489812499316313603785)
              ·
                refine ⟨11075617359374487235202839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14767489812499316313603785 11075617359374487235202839)
                ·
                  refine ⟨16613426039061730852804259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11075617359374487235202839 16613426039061730852804259)
                  ·
                    refine ⟨24920139058592596279206389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16613426039061730852804259 24920139058592596279206389)
                    ·
                      refine ⟨2336263036743055901175599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24920139058592596279206389 2336263036743055901175599)
                      ·
                        rfl

theorem cell23_4549856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_4549856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549856 prefixEnd_4549856 := by exact prefixLift 4549856
  have htrace : WordTrace (prefixWord ++ tailWord_4549856) baseStart_4549856 baseEnd_4549856 := by
    simpa [prefixWord, tailWord_4549856, baseEnd_4549856] using wordTrace_append hprefix tailTrace_4549856
  have hstable : (prefixWord ++ tailWord_4549856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549856).length < 2 ^ (prefixWord ++ tailWord_4549856).sum := by decide
  have hdescent : baseEnd_4549856 < baseStart_4549856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549866 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_4549866 : Nat := 118140960795 + 4549866 * 2 ^ 59
def prefixEnd_4549866 : Nat := 4983230072969 + 3 ^ 40 * 4549866 * 2
def baseEnd_4549866 : Nat := 2336268171549600862050553

theorem tailTrace_4549866 : CollatzResearch.WordTrace tailWord_4549866 prefixEnd_4549866 2336268171549600862050553 := by
  unfold tailWord_4549866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41486811533655003023345363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110631497423080008062254301 41486811533655003023345363)
  ·
    refine ⟨62230217300482504535018045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41486811533655003023345363 62230217300482504535018045)
    ·
      refine ⟨23336331487680939200631767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62230217300482504535018045 23336331487680939200631767)
      ·
        refine ⟨35004497231521408800947651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23336331487680939200631767 35004497231521408800947651)
        ·
          refine ⟨52506745847282113201421477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35004497231521408800947651 52506745847282113201421477)
          ·
            refine ⟨9845014846365396225266527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52506745847282113201421477 9845014846365396225266527)
            ·
              refine ⟨14767522269548094337899791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9845014846365396225266527 14767522269548094337899791)
              ·
                refine ⟨22151283404322141506849687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14767522269548094337899791 22151283404322141506849687)
                ·
                  refine ⟨33226925106483212260274531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22151283404322141506849687 33226925106483212260274531)
                  ·
                    refine ⟨49840387659724818390411797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33226925106483212260274531 49840387659724818390411797)
                    ·
                      refine ⟨2336268171549600862050553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49840387659724818390411797 2336268171549600862050553)
                      ·
                        rfl

theorem cell23_4549866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_4549866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549866 prefixEnd_4549866 := by exact prefixLift 4549866
  have htrace : WordTrace (prefixWord ++ tailWord_4549866) baseStart_4549866 baseEnd_4549866 := by
    simpa [prefixWord, tailWord_4549866, baseEnd_4549866] using wordTrace_append hprefix tailTrace_4549866
  have hstable : (prefixWord ++ tailWord_4549866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549866).length < 2 ^ (prefixWord ++ tailWord_4549866).sum := by decide
  have hdescent : baseEnd_4549866 < baseStart_4549866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549870 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_4549870 : Nat := 118140960795 + 4549870 * 2 ^ 59
def prefixEnd_4549870 : Nat := 4983230072969 + 3 ^ 40 * 4549870 * 2
def baseEnd_4549870 : Nat := 2336270225472218846400535

theorem tailTrace_4549870 : CollatzResearch.WordTrace tailWord_4549870 prefixEnd_4549870 2336270225472218846400535 := by
  unfold tailWord_4549870
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743424003325690097065883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110631594684403680517684709 20743424003325690097065883)
  ·
    refine ⟨31115136004988535145598825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20743424003325690097065883 31115136004988535145598825)
    ·
      refine ⟨23336352003741401359199119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31115136004988535145598825 23336352003741401359199119)
      ·
        refine ⟨35004528005612102038798679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23336352003741401359199119 35004528005612102038798679)
        ·
          refine ⟨52506792008418153058198019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35004528005612102038798679 52506792008418153058198019)
          ·
            refine ⟨78760188012627229587297029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52506792008418153058198019 78760188012627229587297029)
            ·
              refine ⟨14767535252367605547618193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78760188012627229587297029 14767535252367605547618193)
              ·
                refine ⟨11075651439275704160713645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14767535252367605547618193 11075651439275704160713645)
                ·
                  refine ⟨4153369289728389060267617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11075651439275704160713645 4153369289728389060267617)
                  ·
                    refine ⟨3115026967296291795200713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4153369289728389060267617 3115026967296291795200713)
                    ·
                      refine ⟨2336270225472218846400535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115026967296291795200713 2336270225472218846400535)
                      ·
                        rfl

theorem cell23_4549870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_4549870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549870 prefixEnd_4549870 := by exact prefixLift 4549870
  have htrace : WordTrace (prefixWord ++ tailWord_4549870) baseStart_4549870 baseEnd_4549870 := by
    simpa [prefixWord, tailWord_4549870, baseEnd_4549870] using wordTrace_append hprefix tailTrace_4549870
  have hstable : (prefixWord ++ tailWord_4549870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549870).length < 2 ^ (prefixWord ++ tailWord_4549870).sum := by decide
  have hdescent : baseEnd_4549870 < baseStart_4549870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549887 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 1, 2, 2]
def baseStart_4549887 : Nat := 118140960795 + 4549887 * 2 ^ 59
def prefixEnd_4549887 : Nat := 4983230072969 + 3 ^ 40 * 4549887 * 2
def baseEnd_4549887 : Nat := 2336278954643345279887957

theorem tailTrace_4549887 : CollatzResearch.WordTrace tailWord_4549887 prefixEnd_4549887 2336278954643345279887957 := by
  unfold tailWord_4549887
  simp only [CollatzResearch.WordTrace]
  refine ⟨165948012067543932679895915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110632008045029288453263943 165948012067543932679895915)
  ·
    refine ⟨248922018101315899019843873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165948012067543932679895915 248922018101315899019843873)
    ·
      refine ⟨186691513575986924264882905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248922018101315899019843873 186691513575986924264882905)
      ·
        refine ⟨140018635181990193198662179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186691513575986924264882905 140018635181990193198662179)
        ·
          refine ⟨210027952772985289797993269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140018635181990193198662179 210027952772985289797993269)
          ·
            refine ⟨19690120572467370918561869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210027952772985289797993269 19690120572467370918561869)
            ·
              refine ⟨7383795214675264094460701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19690120572467370918561869 7383795214675264094460701)
              ·
                refine ⟨2768923205503224035422763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7383795214675264094460701 2768923205503224035422763)
                ·
                  refine ⟨4153384808254836053134145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768923205503224035422763 4153384808254836053134145)
                  ·
                    refine ⟨3115038606191127039850609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4153384808254836053134145 3115038606191127039850609)
                    ·
                      refine ⟨2336278954643345279887957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115038606191127039850609 2336278954643345279887957)
                      ·
                        rfl

theorem cell23_4549887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_4549887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549887 prefixEnd_4549887 := by exact prefixLift 4549887
  have htrace : WordTrace (prefixWord ++ tailWord_4549887) baseStart_4549887 baseEnd_4549887 := by
    simpa [prefixWord, tailWord_4549887, baseEnd_4549887] using wordTrace_append hprefix tailTrace_4549887
  have hstable : (prefixWord ++ tailWord_4549887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549887).length < 2 ^ (prefixWord ++ tailWord_4549887).sum := by decide
  have hdescent : baseEnd_4549887 < baseStart_4549887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549890 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_4549890 : Nat := 118140960795 + 4549890 * 2 ^ 59
def prefixEnd_4549890 : Nat := 4983230072969 + 3 ^ 40 * 4549890 * 2
def baseEnd_4549890 : Nat := 2336280495085308768150443

theorem tailTrace_4549890 : CollatzResearch.WordTrace tailWord_4549890 prefixEnd_4549890 2336280495085308768150443 := by
  unfold tailWord_4549890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41487030371633266048063781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110632080991022042794836749 41487030371633266048063781)
  ·
    refine ⟨7778818194681237384011959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41487030371633266048063781 7778818194681237384011959)
    ·
      refine ⟨11668227292021856076017939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7778818194681237384011959 11668227292021856076017939)
      ·
        refine ⟨17502340938032784114026909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11668227292021856076017939 17502340938032784114026909)
        ·
          refine ⟨6563377851762294042760091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17502340938032784114026909 6563377851762294042760091)
          ·
            refine ⟨9845066777643441064140137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6563377851762294042760091 9845066777643441064140137)
            ·
              refine ⟨7383800083232580798105103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9845066777643441064140137 7383800083232580798105103)
              ·
                refine ⟨11075700124848871197157655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7383800083232580798105103 11075700124848871197157655)
                ·
                  refine ⟨16613550187273306795736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11075700124848871197157655 16613550187273306795736483)
                  ·
                    refine ⟨24920325280909960193604725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16613550187273306795736483 24920325280909960193604725)
                    ·
                      refine ⟨2336280495085308768150443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24920325280909960193604725 2336280495085308768150443)
                      ·
                        rfl

theorem cell23_4549890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_4549890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549890 prefixEnd_4549890 := by exact prefixLift 4549890
  have htrace : WordTrace (prefixWord ++ tailWord_4549890) baseStart_4549890 baseEnd_4549890 := by
    simpa [prefixWord, tailWord_4549890, baseEnd_4549890] using wordTrace_append hprefix tailTrace_4549890
  have hstable : (prefixWord ++ tailWord_4549890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549890).length < 2 ^ (prefixWord ++ tailWord_4549890).sum := by decide
  have hdescent : baseEnd_4549890 < baseStart_4549890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549946 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_4549946 : Nat := 118140960795 + 4549946 * 2 ^ 59
def prefixEnd_4549946 : Nat := 4983230072969 + 3 ^ 40 * 4549946 * 2
def baseEnd_4549946 : Nat := 2336309250001960549050185

theorem tailTrace_4549946 : CollatzResearch.WordTrace tailWord_4549946 prefixEnd_4549946 2336309250001960549050185 := by
  unfold tailWord_4549946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41487540993582546439073423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110633442649553457170862461 41487540993582546439073423)
  ·
    refine ⟨62231311490373819658610135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41487540993582546439073423 62231311490373819658610135)
    ·
      refine ⟨93346967235560729487915203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62231311490373819658610135 93346967235560729487915203)
      ·
        refine ⟨140020450853341094231872805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93346967235560729487915203 140020450853341094231872805)
        ·
          refine ⟨26253834535001455168476151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140020450853341094231872805 26253834535001455168476151)
          ·
            refine ⟨39380751802502182752714227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26253834535001455168476151 39380751802502182752714227)
            ·
              refine ⟨59071127703753274129071341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39380751802502182752714227 59071127703753274129071341)
              ·
                refine ⟨22151672888907477798401753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59071127703753274129071341 22151672888907477798401753)
                ·
                  refine ⟨16613754666680608348801315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22151672888907477798401753 16613754666680608348801315)
                  ·
                    refine ⟨24920632000020912523201973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16613754666680608348801315 24920632000020912523201973)
                    ·
                      refine ⟨2336309250001960549050185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24920632000020912523201973 2336309250001960549050185)
                      ·
                        rfl

theorem cell23_4549946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_4549946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549946 prefixEnd_4549946 := by exact prefixLift 4549946
  have htrace : WordTrace (prefixWord ++ tailWord_4549946) baseStart_4549946 baseEnd_4549946 := by
    simpa [prefixWord, tailWord_4549946, baseEnd_4549946] using wordTrace_append hprefix tailTrace_4549946
  have hstable : (prefixWord ++ tailWord_4549946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549946).length < 2 ^ (prefixWord ++ tailWord_4549946).sum := by decide
  have hdescent : baseEnd_4549946 < baseStart_4549946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549966 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_4549966 : Nat := 118140960795 + 4549966 * 2 ^ 59
def prefixEnd_4549966 : Nat := 4983230072969 + 3 ^ 40 * 4549966 * 2
def baseEnd_4549966 : Nat := 259591057735005607866677

theorem tailTrace_4549966 : CollatzResearch.WordTrace tailWord_4549966 prefixEnd_4549966 259591057735005607866677 := by
  unfold tailWord_4549966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743861679282216146502719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110633928956171819448014501 20743861679282216146502719)
  ·
    refine ⟨31115792518923324219754079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20743861679282216146502719 31115792518923324219754079)
    ·
      refine ⟨46673688778384986329631119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31115792518923324219754079 46673688778384986329631119)
      ·
        refine ⟨70010533167577479494446679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46673688778384986329631119 70010533167577479494446679)
        ·
          refine ⟨105015799751366219241670019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70010533167577479494446679 105015799751366219241670019)
          ·
            refine ⟨157523699627049328862505029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105015799751366219241670019 157523699627049328862505029)
            ·
              refine ⟨29535693680071749161719693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157523699627049328862505029 29535693680071749161719693)
              ·
                refine ⟨11075885130026905935644885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29535693680071749161719693 11075885130026905935644885)
                ·
                  refine ⟨259591057735005607866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11075885130026905935644885 259591057735005607866677)
                  ·
                    rfl

theorem cell23_4549966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_4549966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549966 prefixEnd_4549966 := by exact prefixLift 4549966
  have htrace : WordTrace (prefixWord ++ tailWord_4549966) baseStart_4549966 baseEnd_4549966 := by
    simpa [prefixWord, tailWord_4549966, baseEnd_4549966] using wordTrace_append hprefix tailTrace_4549966
  have hstable : (prefixWord ++ tailWord_4549966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549966).length < 2 ^ (prefixWord ++ tailWord_4549966).sum := by decide
  have hdescent : baseEnd_4549966 < baseStart_4549966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549973 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4549973 : Nat := 118140960795 + 4549973 * 2 ^ 59
def prefixEnd_4549973 : Nat := 4983230072969 + 3 ^ 40 * 4549973 * 2
def baseEnd_4549973 : Nat := 2336323113979631943412561

theorem tailTrace_4549973 : CollatzResearch.WordTrace tailWord_4549973 prefixEnd_4549973 2336323113979631943412561 := by
  unfold tailWord_4549973
  simp only [CollatzResearch.WordTrace]
  refine ⟨165951148745232369367526573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110634099163488246245017715 165951148745232369367526573)
  ·
    refine ⟨62231680779462138512822465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165951148745232369367526573 62231680779462138512822465)
    ·
      refine ⟨46673760584596603884616849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62231680779462138512822465 46673760584596603884616849)
      ·
        refine ⟨35005320438447452913462637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46673760584596603884616849 35005320438447452913462637)
        ·
          refine ⟨13126995164417794842548489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35005320438447452913462637 13126995164417794842548489)
          ·
            refine ⟨9845246373313346131911367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13126995164417794842548489 9845246373313346131911367)
            ·
              refine ⟨14767869559970019197867051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9845246373313346131911367 14767869559970019197867051)
              ·
                refine ⟨22151804339955028796800577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14767869559970019197867051 22151804339955028796800577)
                ·
                  refine ⟨16613853254966271597600433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22151804339955028796800577 16613853254966271597600433)
                  ·
                    refine ⟨12460389941224703698200325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16613853254966271597600433 12460389941224703698200325)
                    ·
                      refine ⟨2336323113979631943412561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12460389941224703698200325 2336323113979631943412561)
                      ·
                        rfl

theorem cell23_4549973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4549973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549973 prefixEnd_4549973 := by exact prefixLift 4549973
  have htrace : WordTrace (prefixWord ++ tailWord_4549973) baseStart_4549973 baseEnd_4549973 := by
    simpa [prefixWord, tailWord_4549973, baseEnd_4549973] using wordTrace_append hprefix tailTrace_4549973
  have hstable : (prefixWord ++ tailWord_4549973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549973).length < 2 ^ (prefixWord ++ tailWord_4549973).sum := by decide
  have hdescent : baseEnd_4549973 < baseStart_4549973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4549998 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4549998 : Nat := 118140960795 + 4549998 * 2 ^ 59
def prefixEnd_4549998 : Nat := 4983230072969 + 3 ^ 40 * 4549998 * 2
def baseEnd_4549998 : Nat := 2336335950995994345599947

theorem tailTrace_4549998 : CollatzResearch.WordTrace tailWord_4549998 prefixEnd_4549998 2336335950995994345599947 := by
  unfold tailWord_4549998
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744007571267724829648331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110634707046761199091457765 20744007571267724829648331)
  ·
    refine ⟨31116011356901587244472497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20744007571267724829648331 31116011356901587244472497)
    ·
      refine ⟨23337008517676190433354373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31116011356901587244472497 23337008517676190433354373)
      ·
        refine ⟨4375689097064285706253945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23337008517676190433354373 4375689097064285706253945)
        ·
          refine ⟨3281766822798214279690459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4375689097064285706253945 3281766822798214279690459)
          ·
            refine ⟨4922650234197321419535689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281766822798214279690459 4922650234197321419535689)
            ·
              refine ⟨3691987675647991064651767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4922650234197321419535689 3691987675647991064651767)
              ·
                refine ⟨5537981513471986596977651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691987675647991064651767 5537981513471986596977651)
                ·
                  refine ⟨8306972270207979895466477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5537981513471986596977651 8306972270207979895466477)
                  ·
                    refine ⟨3115114601327992460799929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8306972270207979895466477 3115114601327992460799929)
                    ·
                      refine ⟨2336335950995994345599947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115114601327992460799929 2336335950995994345599947)
                      ·
                        rfl

theorem cell23_4549998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4549998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4549998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4549998 prefixEnd_4549998 := by exact prefixLift 4549998
  have htrace : WordTrace (prefixWord ++ tailWord_4549998) baseStart_4549998 baseEnd_4549998 := by
    simpa [prefixWord, tailWord_4549998, baseEnd_4549998] using wordTrace_append hprefix tailTrace_4549998
  have hstable : (prefixWord ++ tailWord_4549998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4549998).length < 2 ^ (prefixWord ++ tailWord_4549998).sum := by decide
  have hdescent : baseEnd_4549998 < baseStart_4549998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4549998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550090 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_4550090 : Nat := 118140960795 + 4550090 * 2 ^ 59
def prefixEnd_4550090 : Nat := 4983230072969 + 3 ^ 40 * 4550090 * 2
def baseEnd_4550090 : Nat := 259598132357356442849947

theorem tailTrace_4550090 : CollatzResearch.WordTrace tailWord_4550090 prefixEnd_4550090 259598132357356442849947 := by
  unfold tailWord_4550090
  simp only [CollatzResearch.WordTrace]
  refine ⟨41488854021452124587383931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110636944057205665566357149 41488854021452124587383931)
  ·
    refine ⟨62233281032178186881075897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41488854021452124587383931 62233281032178186881075897)
    ·
      refine ⟨46674960774133640160806923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62233281032178186881075897 46674960774133640160806923)
      ·
        refine ⟨70012441161200460241210385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46674960774133640160806923 70012441161200460241210385)
        ·
          refine ⟨52509330870900345180907789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70012441161200460241210385 52509330870900345180907789)
          ·
            refine ⟨19690999076587629442840421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52509330870900345180907789 19690999076587629442840421)
            ·
              refine ⟨3692062326860180520532579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19690999076587629442840421 3692062326860180520532579)
              ·
                refine ⟨5538093490290270780798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692062326860180520532579 5538093490290270780798869)
                ·
                  refine ⟨259598132357356442849947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5538093490290270780798869 259598132357356442849947)
                  ·
                    rfl

theorem cell23_4550090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_4550090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550090 prefixEnd_4550090 := by exact prefixLift 4550090
  have htrace : WordTrace (prefixWord ++ tailWord_4550090) baseStart_4550090 baseEnd_4550090 := by
    simpa [prefixWord, tailWord_4550090, baseEnd_4550090] using wordTrace_append hprefix tailTrace_4550090
  have hstable : (prefixWord ++ tailWord_4550090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550090).length < 2 ^ (prefixWord ++ tailWord_4550090).sum := by decide
  have hdescent : baseEnd_4550090 < baseStart_4550090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550096 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_4550096 : Nat := 118140960795 + 4550096 * 2 ^ 59
def prefixEnd_4550096 : Nat := 4983230072969 + 3 ^ 40 * 4550096 * 2
def baseEnd_4550096 : Nat := 2336386272100134962174495

theorem tailTrace_4550096 : CollatzResearch.WordTrace tailWord_4550096 prefixEnd_4550096 2336386272100134962174495 := by
  unfold tailWord_4550096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82977817461893380687127071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110637089949191174249502761 82977817461893380687127071)
  ·
    refine ⟨124466726192840071030690607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82977817461893380687127071 124466726192840071030690607)
    ·
      refine ⟨186700089289260106546035911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124466726192840071030690607 186700089289260106546035911)
      ·
        refine ⟨280050133933890159819053867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186700089289260106546035911 280050133933890159819053867)
        ·
          refine ⟨420075200900835239728580801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280050133933890159819053867 420075200900835239728580801)
          ·
            refine ⟨315056400675626429796435601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420075200900835239728580801 315056400675626429796435601)
            ·
              refine ⟨236292300506719822347326701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315056400675626429796435601 236292300506719822347326701)
              ·
                refine ⟨88609612690019933380247513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236292300506719822347326701 88609612690019933380247513)
                ·
                  refine ⟨66457209517514950035185635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88609612690019933380247513 66457209517514950035185635)
                  ·
                    refine ⟨99685814276272425052778453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66457209517514950035185635 99685814276272425052778453)
                    ·
                      refine ⟨2336386272100134962174495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99685814276272425052778453 2336386272100134962174495)
                      ·
                        rfl

theorem cell23_4550096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_4550096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550096 prefixEnd_4550096 := by exact prefixLift 4550096
  have htrace : WordTrace (prefixWord ++ tailWord_4550096) baseStart_4550096 baseEnd_4550096 := by
    simpa [prefixWord, tailWord_4550096, baseEnd_4550096] using wordTrace_append hprefix tailTrace_4550096
  have hstable : (prefixWord ++ tailWord_4550096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550096).length < 2 ^ (prefixWord ++ tailWord_4550096).sum := by decide
  have hdescent : baseEnd_4550096 < baseStart_4550096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550177 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_4550177 : Nat := 118140960795 + 4550177 * 2 ^ 59
def prefixEnd_4550177 : Nat := 4983230072969 + 3 ^ 40 * 4550177 * 2
def baseEnd_4550177 : Nat := 2336427864033149145261623

theorem tailTrace_4550177 : CollatzResearch.WordTrace tailWord_4550177 prefixEnd_4550177 2336427864033149145261623 := by
  unfold tailWord_4550177
  simp only [CollatzResearch.WordTrace]
  refine ⟨165958589236493312207952785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110639059490995541471968523 165958589236493312207952785)
  ·
    refine ⟨124468941927369984155964589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165958589236493312207952785 124468941927369984155964589)
    ·
      refine ⟨46675853222763744058486721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124468941927369984155964589 46675853222763744058486721)
      ·
        refine ⟨35006889917072808043865041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46675853222763744058486721 35006889917072808043865041)
        ·
          refine ⟨26255167437804606032898781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35006889917072808043865041 26255167437804606032898781)
          ·
            refine ⟨9845687789176727262337043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26255167437804606032898781 9845687789176727262337043)
            ·
              refine ⟨14768531683765090893505565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9845687789176727262337043 14768531683765090893505565)
              ·
                refine ⟨5538199381411909085064587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14768531683765090893505565 5538199381411909085064587)
                ·
                  refine ⟨8307299072117863627596881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538199381411909085064587 8307299072117863627596881)
                  ·
                    refine ⟨6230474304088397720697661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8307299072117863627596881 6230474304088397720697661)
                    ·
                      refine ⟨2336427864033149145261623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6230474304088397720697661 2336427864033149145261623)
                      ·
                        rfl

theorem cell23_4550177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_4550177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550177 prefixEnd_4550177 := by exact prefixLift 4550177
  have htrace : WordTrace (prefixWord ++ tailWord_4550177) baseStart_4550177 baseEnd_4550177 := by
    simpa [prefixWord, tailWord_4550177, baseEnd_4550177] using wordTrace_append hprefix tailTrace_4550177
  have hstable : (prefixWord ++ tailWord_4550177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550177).length < 2 ^ (prefixWord ++ tailWord_4550177).sum := by decide
  have hdescent : baseEnd_4550177 < baseStart_4550177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550204 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_4550204 : Nat := 118140960795 + 4550204 * 2 ^ 59
def prefixEnd_4550204 : Nat := 4983230072969 + 3 ^ 40 * 4550204 * 2
def baseEnd_4550204 : Nat := 2336441728010820539623999

theorem tailTrace_4550204 : CollatzResearch.WordTrace tailWord_4550204 prefixEnd_4550204 2336441728010820539623999 := by
  unfold tailWord_4550204
  simp only [CollatzResearch.WordTrace]
  refine ⟨82979787003697747909592833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110639716004930330546123777 82979787003697747909592833)
  ·
    refine ⟨62234840252773310932194625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82979787003697747909592833 62234840252773310932194625)
    ·
      refine ⟨46676130189579983199145969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62234840252773310932194625 46676130189579983199145969)
      ·
        refine ⟨35007097642184987399359477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46676130189579983199145969 35007097642184987399359477)
        ·
          refine ⟨3281915403954842568689951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35007097642184987399359477 3281915403954842568689951)
          ·
            refine ⟨4922873105932263853034927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281915403954842568689951 4922873105932263853034927)
            ·
              refine ⟨7384309658898395779552391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922873105932263853034927 7384309658898395779552391)
              ·
                refine ⟨11076464488347593669328587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384309658898395779552391 11076464488347593669328587)
                ·
                  refine ⟨16614696732521390503992881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11076464488347593669328587 16614696732521390503992881)
                  ·
                    refine ⟨12461022549391042877994661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16614696732521390503992881 12461022549391042877994661)
                    ·
                      refine ⟨2336441728010820539623999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12461022549391042877994661 2336441728010820539623999)
                      ·
                        rfl

theorem cell23_4550204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_4550204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550204 prefixEnd_4550204 := by exact prefixLift 4550204
  have htrace : WordTrace (prefixWord ++ tailWord_4550204) baseStart_4550204 baseEnd_4550204 := by
    simpa [prefixWord, tailWord_4550204, baseEnd_4550204] using wordTrace_append hprefix tailTrace_4550204
  have hstable : (prefixWord ++ tailWord_4550204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550204).length < 2 ^ (prefixWord ++ tailWord_4550204).sum := by decide
  have hdescent : baseEnd_4550204 < baseStart_4550204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550207 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_4550207 : Nat := 118140960795 + 4550207 * 2 ^ 59
def prefixEnd_4550207 : Nat := 4983230072969 + 3 ^ 40 * 4550207 * 2
def baseEnd_4550207 : Nat := 2336443268452784027886485

theorem tailTrace_4550207 : CollatzResearch.WordTrace tailWord_4550207 prefixEnd_4550207 2336443268452784027886485 := by
  unfold tailWord_4550207
  simp only [CollatzResearch.WordTrace]
  refine ⟨165959683426384627331544875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110639788950923084887696583 165959683426384627331544875)
  ·
    refine ⟨248939525139576940997317313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165959683426384627331544875 248939525139576940997317313)
    ·
      refine ⟨186704643854682705747987985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248939525139576940997317313 186704643854682705747987985)
      ·
        refine ⟨140028482891012029310990989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186704643854682705747987985 140028482891012029310990989)
        ·
          refine ⟨52510681084129510991621621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140028482891012029310990989 52510681084129510991621621)
          ·
            refine ⟨4922876351637141655464527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52510681084129510991621621 4922876351637141655464527)
            ·
              refine ⟨7384314527455712483196791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922876351637141655464527 7384314527455712483196791)
              ·
                refine ⟨11076471791183568724795187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384314527455712483196791 11076471791183568724795187)
                ·
                  refine ⟨16614707686775353087192781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11076471791183568724795187 16614707686775353087192781)
                  ·
                    refine ⟨6230515382540757407697293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16614707686775353087192781 6230515382540757407697293)
                    ·
                      refine ⟨2336443268452784027886485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6230515382540757407697293 2336443268452784027886485)
                      ·
                        rfl

theorem cell23_4550207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_4550207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550207 prefixEnd_4550207 := by exact prefixLift 4550207
  have htrace : WordTrace (prefixWord ++ tailWord_4550207) baseStart_4550207 baseEnd_4550207 := by
    simpa [prefixWord, tailWord_4550207, baseEnd_4550207] using wordTrace_append hprefix tailTrace_4550207
  have hstable : (prefixWord ++ tailWord_4550207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550207).length < 2 ^ (prefixWord ++ tailWord_4550207).sum := by decide
  have hdescent : baseEnd_4550207 < baseStart_4550207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550304 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 5]
def baseStart_4550304 : Nat := 118140960795 + 4550304 * 2 ^ 59
def prefixEnd_4550304 : Nat := 4983230072969 + 3 ^ 40 * 4550304 * 2
def baseEnd_4550304 : Nat := 259610341786252238708171

theorem tailTrace_4550304 : CollatzResearch.WordTrace tailWord_4550304 prefixEnd_4550304 259610341786252238708171 := by
  unfold tailWord_4550304
  simp only [CollatzResearch.WordTrace]
  refine ⟨82981610653516606448912983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110642147538022141931883977 82981610653516606448912983)
  ·
    refine ⟨124472415980274909673369475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82981610653516606448912983 124472415980274909673369475)
    ·
      refine ⟨186708623970412364510054213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124472415980274909673369475 186708623970412364510054213)
      ·
        refine ⟨35007866994452318345635165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186708623970412364510054213 35007866994452318345635165)
        ·
          refine ⟨13127950122919619379613187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35007866994452318345635165 13127950122919619379613187)
          ·
            refine ⟨19691925184379429069419781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13127950122919619379613187 19691925184379429069419781)
            ·
              refine ⟨3692235972071142950516209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19691925184379429069419781 3692235972071142950516209)
              ·
                refine ⟨2769176979053357212887157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692235972071142950516209 2769176979053357212887157)
                ·
                  refine ⟨259610341786252238708171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2769176979053357212887157 259610341786252238708171)
                  ·
                    rfl

theorem cell23_4550304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 5].length) (baseStart_4550304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550304 prefixEnd_4550304 := by exact prefixLift 4550304
  have htrace : WordTrace (prefixWord ++ tailWord_4550304) baseStart_4550304 baseEnd_4550304 := by
    simpa [prefixWord, tailWord_4550304, baseEnd_4550304] using wordTrace_append hprefix tailTrace_4550304
  have hstable : (prefixWord ++ tailWord_4550304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550304).length < 2 ^ (prefixWord ++ tailWord_4550304).sum := by decide
  have hdescent : baseEnd_4550304 < baseStart_4550304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550320 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_4550320 : Nat := 118140960795 + 4550320 * 2 ^ 59
def prefixEnd_4550320 : Nat := 4983230072969 + 3 ^ 40 * 4550320 * 2
def baseEnd_4550320 : Nat := 2336501291766742085773465

theorem tailTrace_4550320 : CollatzResearch.WordTrace tailWord_4550320 prefixEnd_4550320 2336501291766742085773465 := by
  unfold tailWord_4550320
  simp only [CollatzResearch.WordTrace]
  refine ⟨82981902437487623815204207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110642536583316831753605609 82981902437487623815204207)
  ·
    refine ⟨124472853656231435722806311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82981902437487623815204207 124472853656231435722806311)
    ·
      refine ⟨186709280484347153584209467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124472853656231435722806311 186709280484347153584209467)
      ·
        refine ⟨280063920726520730376314201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186709280484347153584209467 280063920726520730376314201)
        ·
          refine ⟨210047940544890547782235651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280063920726520730376314201 210047940544890547782235651)
          ·
            refine ⟨315071910817335821673353477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210047940544890547782235651 315071910817335821673353477)
            ·
              refine ⟨59075983278250466563753777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315071910817335821673353477 59075983278250466563753777)
              ·
                refine ⟨44306987458687849922815333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59075983278250466563753777 44306987458687849922815333)
                ·
                  refine ⟨8307560148503971860527875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44306987458687849922815333 8307560148503971860527875)
                  ·
                    refine ⟨12461340222755957790791813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8307560148503971860527875 12461340222755957790791813)
                    ·
                      refine ⟨2336501291766742085773465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12461340222755957790791813 2336501291766742085773465)
                      ·
                        rfl

theorem cell23_4550320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_4550320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550320 prefixEnd_4550320 := by exact prefixLift 4550320
  have htrace : WordTrace (prefixWord ++ tailWord_4550320) baseStart_4550320 baseEnd_4550320 := by
    simpa [prefixWord, tailWord_4550320, baseEnd_4550320] using wordTrace_append hprefix tailTrace_4550320
  have hstable : (prefixWord ++ tailWord_4550320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550320).length < 2 ^ (prefixWord ++ tailWord_4550320).sum := by decide
  have hdescent : baseEnd_4550320 < baseStart_4550320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550334 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4550334 : Nat := 118140960795 + 4550334 * 2 ^ 59
def prefixEnd_4550334 : Nat := 4983230072969 + 3 ^ 40 * 4550334 * 2
def baseEnd_4550334 : Nat := 778836160165301676999467

theorem tailTrace_4550334 : CollatzResearch.WordTrace tailWord_4550334 prefixEnd_4550334 778836160165301676999467 := by
  unfold tailWord_4550334
  simp only [CollatzResearch.WordTrace]
  refine ⟨20745539437115566002677257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110642876997949685347612037 20745539437115566002677257)
  ·
    refine ⟨15559154577836674502007943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20745539437115566002677257 15559154577836674502007943)
    ·
      refine ⟨23338731866755011753011915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559154577836674502007943 23338731866755011753011915)
      ·
        refine ⟨35008097800132517629517873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23338731866755011753011915 35008097800132517629517873)
        ·
          refine ⟨26256073350099388222138405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35008097800132517629517873 26256073350099388222138405)
          ·
            refine ⟨4923013753143635291650951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26256073350099388222138405 4923013753143635291650951)
            ·
              refine ⟨7384520629715452937476427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923013753143635291650951 7384520629715452937476427)
              ·
                refine ⟨11076780944573179406214641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384520629715452937476427 11076780944573179406214641)
                ·
                  refine ⟨8307585708429884554660981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11076780944573179406214641 8307585708429884554660981)
                  ·
                    refine ⟨778836160165301676999467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8307585708429884554660981 778836160165301676999467)
                    ·
                      rfl

theorem cell23_4550334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4550334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550334 prefixEnd_4550334 := by exact prefixLift 4550334
  have htrace : WordTrace (prefixWord ++ tailWord_4550334) baseStart_4550334 baseEnd_4550334 := by
    simpa [prefixWord, tailWord_4550334, baseEnd_4550334] using wordTrace_append hprefix tailTrace_4550334
  have hstable : (prefixWord ++ tailWord_4550334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550334).length < 2 ^ (prefixWord ++ tailWord_4550334).sum := by decide
  have hdescent : baseEnd_4550334 < baseStart_4550334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550350 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4550350 : Nat := 118140960795 + 4550350 * 2 ^ 59
def prefixEnd_4550350 : Nat := 4983230072969 + 3 ^ 40 * 4550350 * 2
def baseEnd_4550350 : Nat := 2336516696186376968398327

theorem tailTrace_4550350 : CollatzResearch.WordTrace tailWord_4550350 prefixEnd_4550350 2336516696186376968398327 := by
  unfold tailWord_4550350
  simp only [CollatzResearch.WordTrace]
  refine ⟨20745612383108320344250063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110643266043244375169333669 20745612383108320344250063)
  ·
    refine ⟨31118418574662480516375095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20745612383108320344250063 31118418574662480516375095)
    ·
      refine ⟨46677627861993720774562643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31118418574662480516375095 46677627861993720774562643)
      ·
        refine ⟨70016441792990581161843965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46677627861993720774562643 70016441792990581161843965)
        ·
          refine ⟨26256165672371467935691487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70016441792990581161843965 26256165672371467935691487)
          ·
            refine ⟨39384248508557201903537231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26256165672371467935691487 39384248508557201903537231)
            ·
              refine ⟨59076372762835802855305847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39384248508557201903537231 59076372762835802855305847)
              ·
                refine ⟨88614559144253704282958771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59076372762835802855305847 88614559144253704282958771)
                ·
                  refine ⟨132921838716380556424438157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88614559144253704282958771 132921838716380556424438157)
                  ·
                    refine ⟨49845689518642708659164309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132921838716380556424438157 49845689518642708659164309)
                    ·
                      refine ⟨2336516696186376968398327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49845689518642708659164309 2336516696186376968398327)
                      ·
                        rfl

theorem cell23_4550350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4550350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550350 prefixEnd_4550350 := by exact prefixLift 4550350
  have htrace : WordTrace (prefixWord ++ tailWord_4550350) baseStart_4550350 baseEnd_4550350 := by
    simpa [prefixWord, tailWord_4550350, baseEnd_4550350] using wordTrace_append hprefix tailTrace_4550350
  have hstable : (prefixWord ++ tailWord_4550350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550350).length < 2 ^ (prefixWord ++ tailWord_4550350).sum := by decide
  have hdescent : baseEnd_4550350 < baseStart_4550350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550354 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4550354 : Nat := 118140960795 + 4550354 * 2 ^ 59
def prefixEnd_4550354 : Nat := 4983230072969 + 3 ^ 40 * 4550354 * 2
def baseEnd_4550354 : Nat := 2336518750108994952748309

theorem tailTrace_4550354 : CollatzResearch.WordTrace tailWord_4550354 prefixEnd_4550354 2336518750108994952748309 := by
  unfold tailWord_4550354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41491261239213017859286529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110643363304568047624764077 41491261239213017859286529)
  ·
    refine ⟨31118445929409763394464897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41491261239213017859286529 31118445929409763394464897)
    ·
      refine ⟨23338834447057322545848673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31118445929409763394464897 23338834447057322545848673)
      ·
        refine ⟨17504125835292991909386505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23338834447057322545848673 17504125835292991909386505)
        ·
          refine ⟨13128094376469743932039879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17504125835292991909386505 13128094376469743932039879)
          ·
            refine ⟨19692141564704615898059819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13128094376469743932039879 19692141564704615898059819)
            ·
              refine ⟨29538212347056923847089729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19692141564704615898059819 29538212347056923847089729)
              ·
                refine ⟨22153659260292692885317297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29538212347056923847089729 22153659260292692885317297)
                ·
                  refine ⟨16615244445219519663987973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22153659260292692885317297 16615244445219519663987973)
                  ·
                    refine ⟨3115358333478659936997745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16615244445219519663987973 3115358333478659936997745)
                    ·
                      refine ⟨2336518750108994952748309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115358333478659936997745 2336518750108994952748309)
                      ·
                        rfl

theorem cell23_4550354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4550354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550354 prefixEnd_4550354 := by exact prefixLift 4550354
  have htrace : WordTrace (prefixWord ++ tailWord_4550354) baseStart_4550354 baseEnd_4550354 := by
    simpa [prefixWord, tailWord_4550354, baseEnd_4550354] using wordTrace_append hprefix tailTrace_4550354
  have hstable : (prefixWord ++ tailWord_4550354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550354).length < 2 ^ (prefixWord ++ tailWord_4550354).sum := by decide
  have hdescent : baseEnd_4550354 < baseStart_4550354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550360 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 8]
def baseStart_4550360 : Nat := 118140960795 + 4550360 * 2 ^ 59
def prefixEnd_4550360 : Nat := 4983230072969 + 3 ^ 40 * 4550360 * 2
def baseEnd_4550360 : Nat := 259613536776991325474809

theorem tailTrace_4550360 : CollatzResearch.WordTrace tailWord_4550360 prefixEnd_4550360 259613536776991325474809 := by
  unfold tailWord_4550360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82982631897415167230932267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110643509196553556307909689 82982631897415167230932267)
  ·
    refine ⟨124473947846122750846398401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82982631897415167230932267 124473947846122750846398401)
    ·
      refine ⟨93355460884592063134798801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124473947846122750846398401 93355460884592063134798801)
      ·
        refine ⟨70016595663444047351099101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93355460884592063134798801 70016595663444047351099101)
        ·
          refine ⟨26256223373791517756662163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70016595663444047351099101 26256223373791517756662163)
          ·
            refine ⟨39384335060687276634993245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26256223373791517756662163 39384335060687276634993245)
            ·
              refine ⟨14769125647757728738122467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39384335060687276634993245 14769125647757728738122467)
              ·
                refine ⟨22153688471636593107183701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14769125647757728738122467 22153688471636593107183701)
                ·
                  refine ⟨259613536776991325474809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22153688471636593107183701 259613536776991325474809)
                  ·
                    rfl

theorem cell23_4550360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_4550360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550360 prefixEnd_4550360 := by exact prefixLift 4550360
  have htrace : WordTrace (prefixWord ++ tailWord_4550360) baseStart_4550360 baseEnd_4550360 := by
    simpa [prefixWord, tailWord_4550360, baseEnd_4550360] using wordTrace_append hprefix tailTrace_4550360
  have hstable : (prefixWord ++ tailWord_4550360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550360).length < 2 ^ (prefixWord ++ tailWord_4550360).sum := by decide
  have hdescent : baseEnd_4550360 < baseStart_4550360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550414 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4550414 : Nat := 118140960795 + 4550414 * 2 ^ 59
def prefixEnd_4550414 : Nat := 4983230072969 + 3 ^ 40 * 4550414 * 2
def baseEnd_4550414 : Nat := 2336549558948264717998033

theorem tailTrace_4550414 : CollatzResearch.WordTrace tailWord_4550414 prefixEnd_4550414 2336549558948264717998033 := by
  unfold tailWord_4550414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20745904167079337710541287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110644822224423134456220197 20745904167079337710541287)
  ·
    refine ⟨31118856250619006565811931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20745904167079337710541287 31118856250619006565811931)
    ·
      refine ⟨46678284375928509848717897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31118856250619006565811931 46678284375928509848717897)
      ·
        refine ⟨35008713281946382386538423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46678284375928509848717897 35008713281946382386538423)
        ·
          refine ⟨52513069922919573579807635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35008713281946382386538423 52513069922919573579807635)
          ·
            refine ⟨78769604884379360369711453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52513069922919573579807635 78769604884379360369711453)
            ·
              refine ⟨29538601831642260138641795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78769604884379360369711453 29538601831642260138641795)
              ·
                refine ⟨44307902747463390207962693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29538601831642260138641795 44307902747463390207962693)
                ·
                  refine ⟨8307731765149385663993005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44307902747463390207962693 8307731765149385663993005)
                  ·
                    refine ⟨3115399411931019623997377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8307731765149385663993005 3115399411931019623997377)
                    ·
                      refine ⟨2336549558948264717998033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115399411931019623997377 2336549558948264717998033)
                      ·
                        rfl

theorem cell23_4550414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4550414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550414 prefixEnd_4550414 := by exact prefixLift 4550414
  have htrace : WordTrace (prefixWord ++ tailWord_4550414) baseStart_4550414 baseEnd_4550414 := by
    simpa [prefixWord, tailWord_4550414, baseEnd_4550414] using wordTrace_append hprefix tailTrace_4550414
  have hstable : (prefixWord ++ tailWord_4550414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550414).length < 2 ^ (prefixWord ++ tailWord_4550414).sum := by decide
  have hdescent : baseEnd_4550414 < baseStart_4550414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550421 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_4550421 : Nat := 118140960795 + 4550421 * 2 ^ 59
def prefixEnd_4550421 : Nat := 4983230072969 + 3 ^ 40 * 4550421 * 2
def baseEnd_4550421 : Nat := 2336553153312846190610501

theorem tailTrace_4550421 : CollatzResearch.WordTrace tailWord_4550421 prefixEnd_4550421 2336553153312846190610501 := by
  unfold tailWord_4550421
  simp only [CollatzResearch.WordTrace]
  refine ⟨165967488647609341879835117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110644992431739561253223411 165967488647609341879835117)
  ·
    refine ⟨62237808242853503204938169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165967488647609341879835117 62237808242853503204938169)
    ·
      refine ⟨46678356182140127403703627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62237808242853503204938169 46678356182140127403703627)
      ·
        refine ⟨70017534273210191105555441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46678356182140127403703627 70017534273210191105555441)
        ·
          refine ⟨52513150704907643329166581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70017534273210191105555441 52513150704907643329166581)
          ·
            refine ⟨4923107878585091562109367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52513150704907643329166581 4923107878585091562109367)
            ·
              refine ⟨7384661817877637343164051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923107878585091562109367 7384661817877637343164051)
              ·
                refine ⟨11076992726816456014746077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384661817877637343164051 11076992726816456014746077)
                ·
                  refine ⟨4153872272556171005529779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11076992726816456014746077 4153872272556171005529779)
                  ·
                    refine ⟨6230808408834256508294669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4153872272556171005529779 6230808408834256508294669)
                    ·
                      refine ⟨2336553153312846190610501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6230808408834256508294669 2336553153312846190610501)
                      ·
                        rfl

theorem cell23_4550421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_4550421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550421 prefixEnd_4550421 := by exact prefixLift 4550421
  have htrace : WordTrace (prefixWord ++ tailWord_4550421) baseStart_4550421 baseEnd_4550421 := by
    simpa [prefixWord, tailWord_4550421, baseEnd_4550421] using wordTrace_append hprefix tailTrace_4550421
  have hstable : (prefixWord ++ tailWord_4550421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550421).length < 2 ^ (prefixWord ++ tailWord_4550421).sum := by decide
  have hdescent : baseEnd_4550421 < baseStart_4550421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550444 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_4550444 : Nat := 118140960795 + 4550444 * 2 ^ 59
def prefixEnd_4550444 : Nat := 4983230072969 + 3 ^ 40 * 4550444 * 2
def baseEnd_4550444 : Nat := 2336564963367899600622895

theorem tailTrace_4550444 : CollatzResearch.WordTrace tailWord_4550444 prefixEnd_4550444 2336564963367899600622895 := by
  unfold tailWord_4550444
  simp only [CollatzResearch.WordTrace]
  refine ⟨82984163763263008403961193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110645551684350677871948257 82984163763263008403961193)
  ·
    refine ⟨62238122822447256302970895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82984163763263008403961193 62238122822447256302970895)
    ·
      refine ⟨93357184233670884454456343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62238122822447256302970895 93357184233670884454456343)
      ·
        refine ⟨140035776350506326681684515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93357184233670884454456343 140035776350506326681684515)
        ·
          refine ⟨210053664525759490022526773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140035776350506326681684515 210053664525759490022526773)
          ·
            refine ⟨19692531049289952189611885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210053664525759490022526773 19692531049289952189611885)
            ·
              refine ⟨7384699143483732071104457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19692531049289952189611885 7384699143483732071104457)
              ·
                refine ⟨5538524357612799053328343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384699143483732071104457 5538524357612799053328343)
                ·
                  refine ⟨8307786536419198579992515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538524357612799053328343 8307786536419198579992515)
                  ·
                    refine ⟨12461679804628797869988773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8307786536419198579992515 12461679804628797869988773)
                    ·
                      refine ⟨2336564963367899600622895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12461679804628797869988773 2336564963367899600622895)
                      ·
                        rfl

theorem cell23_4550444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_4550444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550444 prefixEnd_4550444 := by exact prefixLift 4550444
  have htrace : WordTrace (prefixWord ++ tailWord_4550444) baseStart_4550444 baseEnd_4550444 := by
    simpa [prefixWord, tailWord_4550444, baseEnd_4550444] using wordTrace_append hprefix tailTrace_4550444
  have hstable : (prefixWord ++ tailWord_4550444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550444).length < 2 ^ (prefixWord ++ tailWord_4550444).sum := by decide
  have hdescent : baseEnd_4550444 < baseStart_4550444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550447 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_4550447 : Nat := 118140960795 + 4550447 * 2 ^ 59
def prefixEnd_4550447 : Nat := 4983230072969 + 3 ^ 40 * 4550447 * 2
def baseEnd_4550447 : Nat := 2336566503809863088885381

theorem tailTrace_4550447 : CollatzResearch.WordTrace tailWord_4550447 prefixEnd_4550447 2336566503809863088885381 := by
  unfold tailWord_4550447
  simp only [CollatzResearch.WordTrace]
  refine ⟨165968436945515148320281595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110645624630343432213521063 165968436945515148320281595)
  ·
    refine ⟨248952655418272722480422393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165968436945515148320281595 248952655418272722480422393)
    ·
      refine ⟨186714491563704541860316795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248952655418272722480422393 186714491563704541860316795)
      ·
        refine ⟨280071737345556812790475193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186714491563704541860316795 280071737345556812790475193)
        ·
          refine ⟨210053803009167609592856395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280071737345556812790475193 210053803009167609592856395)
          ·
            refine ⟨315080704513751414389284593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210053803009167609592856395 315080704513751414389284593)
            ·
              refine ⟨236310528385313560791963445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315080704513751414389284593 236310528385313560791963445)
              ·
                refine ⟨22154112036123146324246573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236310528385313560791963445 22154112036123146324246573)
                ·
                  refine ⟨8307792013546179871592465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22154112036123146324246573 8307792013546179871592465)
                  ·
                    refine ⟨6230844010159634903694349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8307792013546179871592465 6230844010159634903694349)
                    ·
                      refine ⟨2336566503809863088885381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6230844010159634903694349 2336566503809863088885381)
                      ·
                        rfl

theorem cell23_4550447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_4550447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550447 prefixEnd_4550447 := by exact prefixLift 4550447
  have htrace : WordTrace (prefixWord ++ tailWord_4550447) baseStart_4550447 baseEnd_4550447 := by
    simpa [prefixWord, tailWord_4550447, baseEnd_4550447] using wordTrace_append hprefix tailTrace_4550447
  have hstable : (prefixWord ++ tailWord_4550447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550447).length < 2 ^ (prefixWord ++ tailWord_4550447).sum := by decide
  have hdescent : baseEnd_4550447 < baseStart_4550447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550454 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4550454 : Nat := 118140960795 + 4550454 * 2 ^ 59
def prefixEnd_4550454 : Nat := 4983230072969 + 3 ^ 40 * 4550454 * 2
def baseEnd_4550454 : Nat := 778856699391481520499283

theorem tailTrace_4550454 : CollatzResearch.WordTrace tailWord_4550454 prefixEnd_4550454 778856699391481520499283 := by
  unfold tailWord_4550454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10373043266030611782236651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110645794837659859010524277 10373043266030611782236651)
  ·
    refine ⟨15559564899045917673354977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10373043266030611782236651 15559564899045917673354977)
    ·
      refine ⟨11669673674284438255016233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15559564899045917673354977 11669673674284438255016233)
      ·
        refine ⟨8752255255713328691262175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11669673674284438255016233 8752255255713328691262175)
        ·
          refine ⟨13128382883569993036893263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8752255255713328691262175 13128382883569993036893263)
          ·
            refine ⟨19692574325354989555339895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13128382883569993036893263 19692574325354989555339895)
            ·
              refine ⟨29538861488032484333009843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19692574325354989555339895 29538861488032484333009843)
              ·
                refine ⟨44308292232048726499514765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29538861488032484333009843 44308292232048726499514765)
                ·
                  refine ⟨16615609587018272437318037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44308292232048726499514765 16615609587018272437318037)
                  ·
                    refine ⟨778856699391481520499283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16615609587018272437318037 778856699391481520499283)
                    ·
                      rfl

theorem cell23_4550454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4550454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550454 prefixEnd_4550454 := by exact prefixLift 4550454
  have htrace : WordTrace (prefixWord ++ tailWord_4550454) baseStart_4550454 baseEnd_4550454 := by
    simpa [prefixWord, tailWord_4550454, baseEnd_4550454] using wordTrace_append hprefix tailTrace_4550454
  have hstable : (prefixWord ++ tailWord_4550454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550454).length < 2 ^ (prefixWord ++ tailWord_4550454).sum := by decide
  have hdescent : baseEnd_4550454 < baseStart_4550454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550484 : List Nat := [2, 4, 1, 1, 3, 3, 1, 8]
def baseStart_4550484 : Nat := 118140960795 + 4550484 * 2 ^ 59
def prefixEnd_4550484 : Nat := 4983230072969 + 3 ^ 40 * 4550484 * 2
def baseEnd_4550484 : Nat := 86540203799780720152693

theorem tailTrace_4550484 : CollatzResearch.WordTrace tailWord_4550484 prefixEnd_4550484 86540203799780720152693 := by
  unfold tailWord_4550484
  simp only [CollatzResearch.WordTrace]
  refine ⟨82984893223190551819689253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110646524297587402426252337 82984893223190551819689253)
  ·
    refine ⟨15559667479348228466191735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82984893223190551819689253 15559667479348228466191735)
    ·
      refine ⟨23339501219022342699287603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559667479348228466191735 23339501219022342699287603)
      ·
        refine ⟨35009251828533514048931405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23339501219022342699287603 35009251828533514048931405)
        ·
          refine ⟨13128469435700067768349277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35009251828533514048931405 13128469435700067768349277)
          ·
            refine ⟨4923176038387525413130979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13128469435700067768349277 4923176038387525413130979)
            ·
              refine ⟨7384764057581288119696469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923176038387525413130979 7384764057581288119696469)
              ·
                refine ⟨86540203799780720152693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7384764057581288119696469 86540203799780720152693)
                ·
                  rfl

theorem cell23_4550484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 8].length) (baseStart_4550484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550484 prefixEnd_4550484 := by exact prefixLift 4550484
  have htrace : WordTrace (prefixWord ++ tailWord_4550484) baseStart_4550484 baseEnd_4550484 := by
    simpa [prefixWord, tailWord_4550484, baseEnd_4550484] using wordTrace_append hprefix tailTrace_4550484
  have hstable : (prefixWord ++ tailWord_4550484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550484).length < 2 ^ (prefixWord ++ tailWord_4550484).sum := by decide
  have hdescent : baseEnd_4550484 < baseStart_4550484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550521 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4550521 : Nat := 118140960795 + 4550521 * 2 ^ 59
def prefixEnd_4550521 : Nat := 4983230072969 + 3 ^ 40 * 4550521 * 2
def baseEnd_4550521 : Nat := 2336604501378295799360041

theorem tailTrace_4550521 : CollatzResearch.WordTrace tailWord_4550521 prefixEnd_4550521 2336604501378295799360041 := by
  unfold tailWord_4550521
  simp only [CollatzResearch.WordTrace]
  refine ⟨165971135947247058958475417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110647423964831372638983611 165971135947247058958475417)
  ·
    refine ⟨124478351960435294218856563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165971135947247058958475417 124478351960435294218856563)
    ·
      refine ⟨186717527940652941328284845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124478351960435294218856563 186717527940652941328284845)
      ·
        refine ⟨70019072977744852998106817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186717527940652941328284845 70019072977744852998106817)
        ·
          refine ⟨52514304733308639748580113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70019072977744852998106817 52514304733308639748580113)
          ·
            refine ⟨39385728549981479811435085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52514304733308639748580113 39385728549981479811435085)
            ·
              refine ⟨14769648206243054929288157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39385728549981479811435085 14769648206243054929288157)
              ·
                refine ⟨5538618077341145598483059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14769648206243054929288157 5538618077341145598483059)
                ·
                  refine ⟨8307927116011718397724589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538618077341145598483059 8307927116011718397724589)
                  ·
                    refine ⟨3115472668504394399146721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8307927116011718397724589 3115472668504394399146721)
                    ·
                      refine ⟨2336604501378295799360041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115472668504394399146721 2336604501378295799360041)
                      ·
                        rfl

theorem cell23_4550521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4550521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550521 prefixEnd_4550521 := by exact prefixLift 4550521
  have htrace : WordTrace (prefixWord ++ tailWord_4550521) baseStart_4550521 baseEnd_4550521 := by
    simpa [prefixWord, tailWord_4550521, baseEnd_4550521] using wordTrace_append hprefix tailTrace_4550521
  have hstable : (prefixWord ++ tailWord_4550521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550521).length < 2 ^ (prefixWord ++ tailWord_4550521).sum := by decide
  have hdescent : baseEnd_4550521 < baseStart_4550521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550551 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_4550551 : Nat := 118140960795 + 4550551 * 2 ^ 59
def prefixEnd_4550551 : Nat := 4983230072969 + 3 ^ 40 * 4550551 * 2
def baseEnd_4550551 : Nat := 2336619905797930681984903

theorem tailTrace_4550551 : CollatzResearch.WordTrace tailWord_4550551 prefixEnd_4550551 2336619905797930681984903 := by
  unfold tailWord_4550551
  simp only [CollatzResearch.WordTrace]
  refine ⟨165972230137138374082067507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110648153424758916054711671 165972230137138374082067507)
  ·
    refine ⟨248958345205707561123101261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165972230137138374082067507 248958345205707561123101261)
    ·
      refine ⟨93359379452140335421162973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248958345205707561123101261 93359379452140335421162973)
      ·
        refine ⟨35009767294552625782936115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93359379452140335421162973 35009767294552625782936115)
        ·
          refine ⟨52514650941828938674404173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35009767294552625782936115 52514650941828938674404173)
          ·
            refine ⟨19692994103185852002901565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52514650941828938674404173 19692994103185852002901565)
            ·
              refine ⟨7384872788694694501088087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19692994103185852002901565 7384872788694694501088087)
              ·
                refine ⟨11077309183042041751632131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7384872788694694501088087 11077309183042041751632131)
                ·
                  refine ⟨16615963774563062627448197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11077309183042041751632131 16615963774563062627448197)
                  ·
                    refine ⟨3115493207730574242646537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16615963774563062627448197 3115493207730574242646537)
                    ·
                      refine ⟨2336619905797930681984903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115493207730574242646537 2336619905797930681984903)
                      ·
                        rfl

theorem cell23_4550551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_4550551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550551 prefixEnd_4550551 := by exact prefixLift 4550551
  have htrace : WordTrace (prefixWord ++ tailWord_4550551) baseStart_4550551 baseEnd_4550551 := by
    simpa [prefixWord, tailWord_4550551, baseEnd_4550551] using wordTrace_append hprefix tailTrace_4550551
  have hstable : (prefixWord ++ tailWord_4550551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550551).length < 2 ^ (prefixWord ++ tailWord_4550551).sum := by decide
  have hdescent : baseEnd_4550551 < baseStart_4550551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550587 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 4, 5]
def baseStart_4550587 : Nat := 118140960795 + 4550587 * 2 ^ 59
def prefixEnd_4550587 : Nat := 4983230072969 + 3 ^ 40 * 4550587 * 2
def baseEnd_4550587 : Nat := 778879463700497513711579

theorem tailTrace_4550587 : CollatzResearch.WordTrace tailWord_4550587 prefixEnd_4550587 778879463700497513711579 := by
  unfold tailWord_4550587
  simp only [CollatzResearch.WordTrace]
  refine ⟨165973543165007952230378015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110649028776671968153585343 165973543165007952230378015)
  ·
    refine ⟨248960314747511928345567023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165973543165007952230378015 248960314747511928345567023)
    ·
      refine ⟨373440472121267892518350535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248960314747511928345567023 373440472121267892518350535)
      ·
        refine ⟨560160708181901838777525803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373440472121267892518350535 560160708181901838777525803)
        ·
          refine ⟨840241062272852758166288705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560160708181901838777525803 840241062272852758166288705)
          ·
            refine ⟨630180796704639568624716529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 840241062272852758166288705 630180796704639568624716529)
            ·
              refine ⟨472635597528479676468537397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630180796704639568624716529 472635597528479676468537397)
              ·
                refine ⟨44309587268294969668925381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 472635597528479676468537397 44309587268294969668925381)
                ·
                  refine ⟨8308047612805306812923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44309587268294969668925381 8308047612805306812923509)
                  ·
                    refine ⟨778879463700497513711579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8308047612805306812923509 778879463700497513711579)
                    ·
                      rfl

theorem cell23_4550587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].length) (baseStart_4550587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550587 prefixEnd_4550587 := by exact prefixLift 4550587
  have htrace : WordTrace (prefixWord ++ tailWord_4550587) baseStart_4550587 baseEnd_4550587 := by
    simpa [prefixWord, tailWord_4550587, baseEnd_4550587] using wordTrace_append hprefix tailTrace_4550587
  have hstable : (prefixWord ++ tailWord_4550587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550587).length < 2 ^ (prefixWord ++ tailWord_4550587).sum := by decide
  have hdescent : baseEnd_4550587 < baseStart_4550587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550591 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 5]
def baseStart_4550591 : Nat := 118140960795 + 4550591 * 2 ^ 59
def prefixEnd_4550591 : Nat := 4983230072969 + 3 ^ 40 * 4550591 * 2
def baseEnd_4550591 : Nat := 259626716113790058387191

theorem tailTrace_4550591 : CollatzResearch.WordTrace tailWord_4550591 prefixEnd_4550591 259626716113790058387191 := by
  unfold tailWord_4550591
  simp only [CollatzResearch.WordTrace]
  refine ⟨165973689056993460913523627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110649126037995640609015751 165973689056993460913523627)
  ·
    refine ⟨248960533585490191370285441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165973689056993460913523627 248960533585490191370285441)
    ·
      refine ⟨186720400189117643527714081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248960533585490191370285441 186720400189117643527714081)
      ·
        refine ⟨140040300141838232645785561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186720400189117643527714081 140040300141838232645785561)
        ·
          refine ⟨105030225106378674484339171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140040300141838232645785561 105030225106378674484339171)
          ·
            refine ⟨157545337659568011726508757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105030225106378674484339171 157545337659568011726508757)
            ·
              refine ⟨3692468851396125274840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157545337659568011726508757 3692468851396125274840049)
              ·
                refine ⟨2769351638547093956130037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692468851396125274840049 2769351638547093956130037)
                ·
                  refine ⟨259626716113790058387191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2769351638547093956130037 259626716113790058387191)
                  ·
                    rfl

theorem cell23_4550591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 5].length) (baseStart_4550591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550591 prefixEnd_4550591 := by exact prefixLift 4550591
  have htrace : WordTrace (prefixWord ++ tailWord_4550591) baseStart_4550591 baseEnd_4550591 := by
    simpa [prefixWord, tailWord_4550591, baseEnd_4550591] using wordTrace_append hprefix tailTrace_4550591
  have hstable : (prefixWord ++ tailWord_4550591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550591).length < 2 ^ (prefixWord ++ tailWord_4550591).sum := by decide
  have hdescent : baseEnd_4550591 < baseStart_4550591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550664 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 6]
def baseStart_4550664 : Nat := 118140960795 + 4550664 * 2 ^ 59
def prefixEnd_4550664 : Nat := 4983230072969 + 3 ^ 40 * 4550664 * 2
def baseEnd_4550664 : Nat := 259630881012432082207987

theorem tailTrace_4550664 : CollatzResearch.WordTrace tailWord_4550664 prefixEnd_4550664 259630881012432082207987 := by
  unfold tailWord_4550664
  simp only [CollatzResearch.WordTrace]
  refine ⟨82988175792864497190465523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110650901057152662920620697 82988175792864497190465523)
  ·
    refine ⟨124482263689296745785698285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82988175792864497190465523 124482263689296745785698285)
    ·
      refine ⟨46680848883486279669636857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124482263689296745785698285 46680848883486279669636857)
      ·
        refine ⟨35010636662614709752227643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46680848883486279669636857 35010636662614709752227643)
        ·
          refine ⟨52515954993922064628341465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35010636662614709752227643 52515954993922064628341465)
          ·
            refine ⟨39386966245441548471256099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52515954993922064628341465 39386966245441548471256099)
            ·
              refine ⟨59080449368162322706884149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39386966245441548471256099 59080449368162322706884149)
              ·
                refine ⟨5538792128265217753770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59080449368162322706884149 5538792128265217753770389)
                ·
                  refine ⟨259630881012432082207987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5538792128265217753770389 259630881012432082207987)
                  ·
                    rfl

theorem cell23_4550664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_4550664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550664 prefixEnd_4550664 := by exact prefixLift 4550664
  have htrace : WordTrace (prefixWord ++ tailWord_4550664) baseStart_4550664 baseEnd_4550664 := by
    simpa [prefixWord, tailWord_4550664, baseEnd_4550664] using wordTrace_append hprefix tailTrace_4550664
  have hstable : (prefixWord ++ tailWord_4550664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550664).length < 2 ^ (prefixWord ++ tailWord_4550664).sum := by decide
  have hdescent : baseEnd_4550664 < baseStart_4550664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550685 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_4550685 : Nat := 118140960795 + 4550685 * 2 ^ 59
def prefixEnd_4550685 : Nat := 4983230072969 + 3 ^ 40 * 4550685 * 2
def baseEnd_4550685 : Nat := 778896237401877719236429

theorem tailTrace_4550685 : CollatzResearch.WordTrace tailWord_4550685 prefixEnd_4550685 778896237401877719236429 := by
  unfold tailWord_4550685
  simp only [CollatzResearch.WordTrace]
  refine ⟨165977117518652914967445509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110651411679101943311630339 165977117518652914967445509)
  ·
    refine ⟨31120709534747421556396033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165977117518652914967445509 31120709534747421556396033)
    ·
      refine ⟨23340532151060566167297025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31120709534747421556396033 23340532151060566167297025)
      ·
        refine ⟨17505399113295424625472769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23340532151060566167297025 17505399113295424625472769)
        ·
          refine ⟨13129049334971568469104577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17505399113295424625472769 13129049334971568469104577)
          ·
            refine ⟨9846787001228676351828433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13129049334971568469104577 9846787001228676351828433)
            ·
              refine ⟨7385090250921507263871325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9846787001228676351828433 7385090250921507263871325)
              ·
                refine ⟨2769408844095565223951747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7385090250921507263871325 2769408844095565223951747)
                ·
                  refine ⟨4154113266143347835927621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769408844095565223951747 4154113266143347835927621)
                  ·
                    refine ⟨778896237401877719236429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154113266143347835927621 778896237401877719236429)
                    ·
                      rfl

theorem cell23_4550685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_4550685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550685 prefixEnd_4550685 := by exact prefixLift 4550685
  have htrace : WordTrace (prefixWord ++ tailWord_4550685) baseStart_4550685 baseEnd_4550685 := by
    simpa [prefixWord, tailWord_4550685, baseEnd_4550685] using wordTrace_append hprefix tailTrace_4550685
  have hstable : (prefixWord ++ tailWord_4550685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550685).length < 2 ^ (prefixWord ++ tailWord_4550685).sum := by decide
  have hdescent : baseEnd_4550685 < baseStart_4550685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550691 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 3]
def baseStart_4550691 : Nat := 118140960795 + 4550691 * 2 ^ 59
def prefixEnd_4550691 : Nat := 4983230072969 + 3 ^ 40 * 4550691 * 2
def baseEnd_4550691 : Nat := 2336691793089560134234259

theorem tailTrace_4550691 : CollatzResearch.WordTrace tailWord_4550691 prefixEnd_4550691 2336691793089560134234259 := by
  unfold tailWord_4550691
  simp only [CollatzResearch.WordTrace]
  refine ⟨165977336356631177992163927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110651557571087451994775951 165977336356631177992163927)
  ·
    refine ⟨248966004534946766988245891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165977336356631177992163927 248966004534946766988245891)
    ·
      refine ⟨373449006802420150482368837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248966004534946766988245891 373449006802420150482368837)
      ·
        refine ⟨70021688775453778215444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373449006802420150482368837 70021688775453778215444157)
        ·
          refine ⟨26258133290795166830791559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70021688775453778215444157 26258133290795166830791559)
          ·
            refine ⟨39387199936192750246187339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26258133290795166830791559 39387199936192750246187339)
            ·
              refine ⟨59080799904289125369281009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39387199936192750246187339 59080799904289125369281009)
              ·
                refine ⟨44310599928216844026960757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59080799904289125369281009 44310599928216844026960757)
                ·
                  refine ⟨4154118743270329127527571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44310599928216844026960757 4154118743270329127527571)
                  ·
                    refine ⟨6231178114905493691291357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154118743270329127527571 6231178114905493691291357)
                    ·
                      refine ⟨2336691793089560134234259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231178114905493691291357 2336691793089560134234259)
                      ·
                        rfl

theorem cell23_4550691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_4550691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550691 prefixEnd_4550691 := by exact prefixLift 4550691
  have htrace : WordTrace (prefixWord ++ tailWord_4550691) baseStart_4550691 baseEnd_4550691 := by
    simpa [prefixWord, tailWord_4550691, baseEnd_4550691] using wordTrace_append hprefix tailTrace_4550691
  have hstable : (prefixWord ++ tailWord_4550691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550691).length < 2 ^ (prefixWord ++ tailWord_4550691).sum := by decide
  have hdescent : baseEnd_4550691 < baseStart_4550691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550698 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_4550698 : Nat := 118140960795 + 4550698 * 2 ^ 59
def prefixEnd_4550698 : Nat := 4983230072969 + 3 ^ 40 * 4550698 * 2
def baseEnd_4550698 : Nat := 259632820828237956316303

theorem tailTrace_4550698 : CollatzResearch.WordTrace tailWord_4550698 prefixEnd_4550698 259632820828237956316303 := by
  unfold tailWord_4550698
  simp only [CollatzResearch.WordTrace]
  refine ⟨41494397916901454546917187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110651727778403878791779165 41494397916901454546917187)
  ·
    refine ⟨62241596875352181820375781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41494397916901454546917187 62241596875352181820375781)
    ·
      refine ⟨11670299414128534091320459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62241596875352181820375781 11670299414128534091320459)
      ·
        refine ⟨17505449121192801136980689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670299414128534091320459 17505449121192801136980689)
        ·
          refine ⟨13129086840894600852735517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17505449121192801136980689 13129086840894600852735517)
          ·
            refine ⟨4923407565335475319775819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13129086840894600852735517 4923407565335475319775819)
            ·
              refine ⟨7385111348003212979663729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923407565335475319775819 7385111348003212979663729)
              ·
                refine ⟨5538833511002409734747797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385111348003212979663729 5538833511002409734747797)
                ·
                  refine ⟨259632820828237956316303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5538833511002409734747797 259632820828237956316303)
                  ·
                    rfl

theorem cell23_4550698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_4550698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550698 prefixEnd_4550698 := by exact prefixLift 4550698
  have htrace : WordTrace (prefixWord ++ tailWord_4550698) baseStart_4550698 baseEnd_4550698 := by
    simpa [prefixWord, tailWord_4550698, baseEnd_4550698] using wordTrace_append hprefix tailTrace_4550698
  have hstable : (prefixWord ++ tailWord_4550698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550698).length < 2 ^ (prefixWord ++ tailWord_4550698).sum := by decide
  have hdescent : baseEnd_4550698 < baseStart_4550698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550741 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_4550741 : Nat := 118140960795 + 4550741 * 2 ^ 59
def prefixEnd_4550741 : Nat := 4983230072969 + 3 ^ 40 * 4550741 * 2
def baseEnd_4550741 : Nat := 778905822374094979536343

theorem tailTrace_4550741 : CollatzResearch.WordTrace tailWord_4550741 prefixEnd_4550741 778905822374094979536343 := by
  unfold tailWord_4550741
  simp only [CollatzResearch.WordTrace]
  refine ⟨165979160006450036531484077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110652773337633357687656051 165979160006450036531484077)
  ·
    refine ⟨62242185002418763699306529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165979160006450036531484077 62242185002418763699306529)
    ·
      refine ⟨46681638751814072774479897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62242185002418763699306529 46681638751814072774479897)
      ·
        refine ⟨35011229063860554580859923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46681638751814072774479897 35011229063860554580859923)
        ·
          refine ⟨52516843595790831871289885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35011229063860554580859923 52516843595790831871289885)
          ·
            refine ⟨19693816348421561951733707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52516843595790831871289885 19693816348421561951733707)
            ·
              refine ⟨29540724522632342927600561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19693816348421561951733707 29540724522632342927600561)
              ·
                refine ⟨22155543391974257195700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29540724522632342927600561 22155543391974257195700421)
                ·
                  refine ⟨4154164385995173224193829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22155543391974257195700421 4154164385995173224193829)
                  ·
                    refine ⟨778905822374094979536343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154164385995173224193829 778905822374094979536343)
                    ·
                      rfl

theorem cell23_4550741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_4550741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550741 prefixEnd_4550741 := by exact prefixLift 4550741
  have htrace : WordTrace (prefixWord ++ tailWord_4550741) baseStart_4550741 baseEnd_4550741 := by
    simpa [prefixWord, tailWord_4550741, baseEnd_4550741] using wordTrace_append hprefix tailTrace_4550741
  have hstable : (prefixWord ++ tailWord_4550741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550741).length < 2 ^ (prefixWord ++ tailWord_4550741).sum := by decide
  have hdescent : baseEnd_4550741 < baseStart_4550741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550748 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4550748 : Nat := 118140960795 + 4550748 * 2 ^ 59
def prefixEnd_4550748 : Nat := 4983230072969 + 3 ^ 40 * 4550748 * 2
def baseEnd_4550748 : Nat := 2336721061486866411221497

theorem tailTrace_4550748 : CollatzResearch.WordTrace tailWord_4550748 prefixEnd_4550748 2336721061486866411221497 := by
  unfold tailWord_4550748
  simp only [CollatzResearch.WordTrace]
  refine ⟨82989707658712338363494449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110652943544949784484659265 82989707658712338363494449)
  ·
    refine ⟨62242280744034253772620837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82989707658712338363494449 62242280744034253772620837)
    ·
      refine ⟨11670427639506422582366407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62242280744034253772620837 11670427639506422582366407)
      ·
        refine ⟨17505641459259633873549611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670427639506422582366407 17505641459259633873549611)
        ·
          refine ⟨26258462188889450810324417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505641459259633873549611 26258462188889450810324417)
          ·
            refine ⟨19693846641667088107743313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26258462188889450810324417 19693846641667088107743313)
            ·
              refine ⟨14770384981250316080807485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19693846641667088107743313 14770384981250316080807485)
              ·
                refine ⟨5538894367968868530302807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14770384981250316080807485 5538894367968868530302807)
                ·
                  refine ⟨8308341551953302795454211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5538894367968868530302807 8308341551953302795454211)
                  ·
                    refine ⟨12462512327929954193181317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8308341551953302795454211 12462512327929954193181317)
                    ·
                      refine ⟨2336721061486866411221497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12462512327929954193181317 2336721061486866411221497)
                      ·
                        rfl

theorem cell23_4550748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4550748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550748 prefixEnd_4550748 := by exact prefixLift 4550748
  have htrace : WordTrace (prefixWord ++ tailWord_4550748) baseStart_4550748 baseEnd_4550748 := by
    simpa [prefixWord, tailWord_4550748, baseEnd_4550748] using wordTrace_append hprefix tailTrace_4550748
  have hstable : (prefixWord ++ tailWord_4550748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550748).length < 2 ^ (prefixWord ++ tailWord_4550748).sum := by decide
  have hdescent : baseEnd_4550748 < baseStart_4550748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550775 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 2, 4]
def baseStart_4550775 : Nat := 118140960795 + 4550775 * 2 ^ 59
def prefixEnd_4550775 : Nat := 4983230072969 + 3 ^ 40 * 4550775 * 2
def baseEnd_4550775 : Nat := 778911641821512601861291

theorem tailTrace_4550775 : CollatzResearch.WordTrace tailWord_4550775 prefixEnd_4550775 778911641821512601861291 := by
  unfold tailWord_4550775
  simp only [CollatzResearch.WordTrace]
  refine ⟨165980400088326860338221779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110653600058884573558814519 165980400088326860338221779)
  ·
    refine ⟨248970600132490290507332669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165980400088326860338221779 248970600132490290507332669)
    ·
      refine ⟨93363975049683858940249751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248970600132490290507332669 93363975049683858940249751)
      ·
        refine ⟨140045962574525788410374627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93363975049683858940249751 140045962574525788410374627)
        ·
          refine ⟨210068943861788682615561941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140045962574525788410374627 210068943861788682615561941)
          ·
            refine ⟨4923490871760672248802233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 210068943861788682615561941 4923490871760672248802233)
            ·
              refine ⟨3692618153820504186601675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923490871760672248802233 3692618153820504186601675)
              ·
                refine ⟨5538927230730756279902513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692618153820504186601675 5538927230730756279902513)
                ·
                  refine ⟨4154195423048067209926885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538927230730756279902513 4154195423048067209926885)
                  ·
                    refine ⟨778911641821512601861291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154195423048067209926885 778911641821512601861291)
                    ·
                      rfl

theorem cell23_4550775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_4550775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550775 prefixEnd_4550775 := by exact prefixLift 4550775
  have htrace : WordTrace (prefixWord ++ tailWord_4550775) baseStart_4550775 baseEnd_4550775 := by
    simpa [prefixWord, tailWord_4550775, baseEnd_4550775] using wordTrace_append hprefix tailTrace_4550775
  have hstable : (prefixWord ++ tailWord_4550775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550775).length < 2 ^ (prefixWord ++ tailWord_4550775).sum := by decide
  have hdescent : baseEnd_4550775 < baseStart_4550775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550815 : List Nat := [1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4550815 : Nat := 118140960795 + 4550815 * 2 ^ 59
def prefixEnd_4550815 : Nat := 4983230072969 + 3 ^ 40 * 4550815 * 2
def baseEnd_4550815 : Nat := 2336755464690717649083689

theorem tailTrace_4550815 : CollatzResearch.WordTrace tailWord_4550815 prefixEnd_4550815 2336755464690717649083689 := by
  unfold tailWord_4550815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165981859008181947169677899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110654572672121298113118599 165981859008181947169677899)
  ·
    refine ⟨248972788512272920754516849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165981859008181947169677899 248972788512272920754516849)
    ·
      refine ⟨186729591384204690565887637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248972788512272920754516849 186729591384204690565887637)
      ·
        refine ⟨8752949596134594870275983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186729591384204690565887637 8752949596134594870275983)
        ·
          refine ⟨13129424394201892305413975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8752949596134594870275983 13129424394201892305413975)
          ·
            refine ⟨19694136591302838458120963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13129424394201892305413975 19694136591302838458120963)
            ·
              refine ⟨29541204886954257687181445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19694136591302838458120963 29541204886954257687181445)
              ·
                refine ⟨5538975916303923316346521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29541204886954257687181445 5538975916303923316346521)
                ·
                  refine ⟨4154231937227942487259891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538975916303923316346521 4154231937227942487259891)
                  ·
                    refine ⟨6231347905841913730889837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154231937227942487259891 6231347905841913730889837)
                    ·
                      refine ⟨2336755464690717649083689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231347905841913730889837 2336755464690717649083689)
                      ·
                        rfl

theorem cell23_4550815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4550815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550815 prefixEnd_4550815 := by exact prefixLift 4550815
  have htrace : WordTrace (prefixWord ++ tailWord_4550815) baseStart_4550815 baseEnd_4550815 := by
    simpa [prefixWord, tailWord_4550815, baseEnd_4550815] using wordTrace_append hprefix tailTrace_4550815
  have hstable : (prefixWord ++ tailWord_4550815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550815).length < 2 ^ (prefixWord ++ tailWord_4550815).sum := by decide
  have hdescent : baseEnd_4550815 < baseStart_4550815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550841 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4550841 : Nat := 118140960795 + 4550841 * 2 ^ 59
def prefixEnd_4550841 : Nat := 4983230072969 + 3 ^ 40 * 4550841 * 2
def baseEnd_4550841 : Nat := 2336768815187734547358569

theorem tailTrace_4550841 : CollatzResearch.WordTrace tailWord_4550841 prefixEnd_4550841 2336768815187734547358569 := by
  unfold tailWord_4550841
  simp only [CollatzResearch.WordTrace]
  refine ⟨165982807306087753610124377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110655204870725169073416251 165982807306087753610124377)
  ·
    refine ⟨124487105479565815207593283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165982807306087753610124377 124487105479565815207593283)
    ·
      refine ⟨186730658219348722811389925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124487105479565815207593283 186730658219348722811389925)
      ·
        refine ⟨35011998416127885527135611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186730658219348722811389925 35011998416127885527135611)
        ·
          refine ⟨52517997624191828290703417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35011998416127885527135611 52517997624191828290703417)
          ·
            refine ⟨39388498218143871218027563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52517997624191828290703417 39388498218143871218027563)
            ·
              refine ⟨59082747327215806827041345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39388498218143871218027563 59082747327215806827041345)
              ·
                refine ⟨44312060495411855120281009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59082747327215806827041345 44312060495411855120281009)
                ·
                  refine ⟨33234045371558891340210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44312060495411855120281009 33234045371558891340210757)
                  ·
                    refine ⟨6231383507167292126289517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33234045371558891340210757 6231383507167292126289517)
                    ·
                      refine ⟨2336768815187734547358569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231383507167292126289517 2336768815187734547358569)
                      ·
                        rfl

theorem cell23_4550841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4550841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550841 prefixEnd_4550841 := by exact prefixLift 4550841
  have htrace : WordTrace (prefixWord ++ tailWord_4550841) baseStart_4550841 baseEnd_4550841 := by
    simpa [prefixWord, tailWord_4550841, baseEnd_4550841] using wordTrace_append hprefix tailTrace_4550841
  have hstable : (prefixWord ++ tailWord_4550841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550841).length < 2 ^ (prefixWord ++ tailWord_4550841).sum := by decide
  have hdescent : baseEnd_4550841 < baseStart_4550841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550872 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_4550872 : Nat := 118140960795 + 4550872 * 2 ^ 59
def prefixEnd_4550872 : Nat := 4983230072969 + 3 ^ 40 * 4550872 * 2
def baseEnd_4550872 : Nat := 2336784733088023926070927

theorem tailTrace_4550872 : CollatzResearch.WordTrace tailWord_4550872 prefixEnd_4550872 2336784733088023926070927 := by
  unfold tailWord_4550872
  simp only [CollatzResearch.WordTrace]
  refine ⟨82991968984487722952251435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110655958645983630603001913 82991968984487722952251435)
  ·
    refine ⟨124487953476731584428377153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82991968984487722952251435 124487953476731584428377153)
    ·
      refine ⟨93365965107548688321282865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124487953476731584428377153 93365965107548688321282865)
      ·
        refine ⟨70024473830661516240962149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93365965107548688321282865 70024473830661516240962149)
        ·
          refine ⟨13129588843249034295180403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70024473830661516240962149 13129588843249034295180403)
          ·
            refine ⟨19694383264873551442770605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13129588843249034295180403 19694383264873551442770605)
            ·
              refine ⟨7385393724327581791038977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19694383264873551442770605 7385393724327581791038977)
              ·
                refine ⟨5539045293245686343279233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385393724327581791038977 5539045293245686343279233)
                ·
                  refine ⟨4154283969934264757459425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5539045293245686343279233 4154283969934264757459425)
                  ·
                    refine ⟨3115712977450698568094569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154283969934264757459425 3115712977450698568094569)
                    ·
                      refine ⟨2336784733088023926070927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115712977450698568094569 2336784733088023926070927)
                      ·
                        rfl

theorem cell23_4550872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_4550872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550872 prefixEnd_4550872 := by exact prefixLift 4550872
  have htrace : WordTrace (prefixWord ++ tailWord_4550872) baseStart_4550872 baseEnd_4550872 := by
    simpa [prefixWord, tailWord_4550872, baseEnd_4550872] using wordTrace_append hprefix tailTrace_4550872
  have hstable : (prefixWord ++ tailWord_4550872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550872).length < 2 ^ (prefixWord ++ tailWord_4550872).sum := by decide
  have hdescent : baseEnd_4550872 < baseStart_4550872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550888 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4550888 : Nat := 118140960795 + 4550888 * 2 ^ 59
def prefixEnd_4550888 : Nat := 4983230072969 + 3 ^ 40 * 4550888 * 2
def baseEnd_4550888 : Nat := 2336792948778495863470853

theorem tailTrace_4550888 : CollatzResearch.WordTrace tailWord_4550888 prefixEnd_4550888 2336792948778495863470853 := by
  unfold tailWord_4550888
  simp only [CollatzResearch.WordTrace]
  refine ⟨82992260768458740318542659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110656347691278320424723545 82992260768458740318542659)
  ·
    refine ⟨124488391152688110477813989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82992260768458740318542659 124488391152688110477813989)
    ·
      refine ⟨23341573341129020714590123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124488391152688110477813989 23341573341129020714590123)
      ·
        refine ⟨35012360011693531071885185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23341573341129020714590123 35012360011693531071885185)
        ·
          refine ⟨26259270008770148303913889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35012360011693531071885185 26259270008770148303913889)
          ·
            refine ⟨19694452506577611227935417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26259270008770148303913889 19694452506577611227935417)
            ·
              refine ⟨14770839379933208420951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19694452506577611227935417 14770839379933208420951563)
              ·
                refine ⟨22156259069899812631427345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14770839379933208420951563 22156259069899812631427345)
                ·
                  refine ⟨16617194302424859473570509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22156259069899812631427345 16617194302424859473570509)
                  ·
                    refine ⟨6231447863409322302588941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16617194302424859473570509 6231447863409322302588941)
                    ·
                      refine ⟨2336792948778495863470853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231447863409322302588941 2336792948778495863470853)
                      ·
                        rfl

theorem cell23_4550888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4550888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550888 prefixEnd_4550888 := by exact prefixLift 4550888
  have htrace : WordTrace (prefixWord ++ tailWord_4550888) baseStart_4550888 baseEnd_4550888 := by
    simpa [prefixWord, tailWord_4550888, baseEnd_4550888] using wordTrace_append hprefix tailTrace_4550888
  have hstable : (prefixWord ++ tailWord_4550888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550888).length < 2 ^ (prefixWord ++ tailWord_4550888).sum := by decide
  have hdescent : baseEnd_4550888 < baseStart_4550888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550911 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_4550911 : Nat := 118140960795 + 4550911 * 2 ^ 59
def prefixEnd_4550911 : Nat := 4983230072969 + 3 ^ 40 * 4550911 * 2
def baseEnd_4550911 : Nat := 2336804758833549273483247

theorem tailTrace_4550911 : CollatzResearch.WordTrace tailWord_4550911 prefixEnd_4550911 2336804758833549273483247 := by
  unfold tailWord_4550911
  simp only [CollatzResearch.WordTrace]
  refine ⟨165985360415834155565172587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110656906943889437043448391 165985360415834155565172587)
  ·
    refine ⟨248978040623751233347758881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165985360415834155565172587 248978040623751233347758881)
    ·
      refine ⟨186733530467813425010819161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248978040623751233347758881 186733530467813425010819161)
      ·
        refine ⟨140050147850860068758114371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186733530467813425010819161 140050147850860068758114371)
        ·
          refine ⟨210075221776290103137171557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140050147850860068758114371 210075221776290103137171557)
          ·
            refine ⟨39389104083054394338219667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210075221776290103137171557 39389104083054394338219667)
            ·
              refine ⟨59083656124581591507329501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39389104083054394338219667 59083656124581591507329501)
              ·
                refine ⟨22156371046718096815248563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59083656124581591507329501 22156371046718096815248563)
                ·
                  refine ⟨33234556570077145222872845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22156371046718096815248563 33234556570077145222872845)
                  ·
                    refine ⟨12462958713778929458577317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33234556570077145222872845 12462958713778929458577317)
                    ·
                      refine ⟨2336804758833549273483247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12462958713778929458577317 2336804758833549273483247)
                      ·
                        rfl

theorem cell23_4550911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_4550911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550911 prefixEnd_4550911 := by exact prefixLift 4550911
  have htrace : WordTrace (prefixWord ++ tailWord_4550911) baseStart_4550911 baseEnd_4550911 := by
    simpa [prefixWord, tailWord_4550911, baseEnd_4550911] using wordTrace_append hprefix tailTrace_4550911
  have hstable : (prefixWord ++ tailWord_4550911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550911).length < 2 ^ (prefixWord ++ tailWord_4550911).sum := by decide
  have hdescent : baseEnd_4550911 < baseStart_4550911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4550965 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4550965 : Nat := 118140960795 + 4550965 * 2 ^ 59
def prefixEnd_4550965 : Nat := 4983230072969 + 3 ^ 40 * 4550965 * 2
def baseEnd_4550965 : Nat := 2336832486788892062207999

theorem tailTrace_4550965 : CollatzResearch.WordTrace tailWord_4550965 prefixEnd_4550965 2336832486788892062207999 := by
  unfold tailWord_4550965
  simp only [CollatzResearch.WordTrace]
  refine ⟨165987329957638522787638349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110658219971759015191758899 165987329957638522787638349)
  ·
    refine ⟨62245248734114446045364381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165987329957638522787638349 62245248734114446045364381)
    ·
      refine ⟨23341968275292917267011643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62245248734114446045364381 23341968275292917267011643)
      ·
        refine ⟨35012952412939375900517465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23341968275292917267011643 35012952412939375900517465)
        ·
          refine ⟨26259714309704531925388099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35012952412939375900517465 26259714309704531925388099)
          ·
            refine ⟨39389571464556797888082149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26259714309704531925388099 39389571464556797888082149)
            ·
              refine ⟨7385544649604399604015403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39389571464556797888082149 7385544649604399604015403)
              ·
                refine ⟨11078316974406599406023105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7385544649604399604015403 11078316974406599406023105)
                ·
                  refine ⟨8308737730804949554517329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11078316974406599406023105 8308737730804949554517329)
                  ·
                    refine ⟨6231553298103712165887997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8308737730804949554517329 6231553298103712165887997)
                    ·
                      refine ⟨2336832486788892062207999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231553298103712165887997 2336832486788892062207999)
                      ·
                        rfl

theorem cell23_4550965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4550965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4550965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4550965 prefixEnd_4550965 := by exact prefixLift 4550965
  have htrace : WordTrace (prefixWord ++ tailWord_4550965) baseStart_4550965 baseEnd_4550965 := by
    simpa [prefixWord, tailWord_4550965, baseEnd_4550965] using wordTrace_append hprefix tailTrace_4550965
  have hstable : (prefixWord ++ tailWord_4550965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4550965).length < 2 ^ (prefixWord ++ tailWord_4550965).sum := by decide
  have hdescent : baseEnd_4550965 < baseStart_4550965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4550965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551029 : List Nat := [1, 3, 4, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4551029 : Nat := 118140960795 + 4551029 * 2 ^ 59
def prefixEnd_4551029 : Nat := 4983230072969 + 3 ^ 40 * 4551029 * 2
def baseEnd_4551029 : Nat := 2336865349550779811807705

theorem tailTrace_4551029 : CollatzResearch.WordTrace tailWord_4551029 prefixEnd_4551029 2336865349550779811807705 := by
  unfold tailWord_4551029
  simp only [CollatzResearch.WordTrace]
  refine ⟨165989664229406661717968141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110659776152937774478645427 165989664229406661717968141)
  ·
    refine ⟨62246124086027498144238053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165989664229406661717968141 62246124086027498144238053)
    ·
      refine ⟨11671148266130155902044635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62246124086027498144238053 11671148266130155902044635)
      ·
        refine ⟨17506722399195233853066953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11671148266130155902044635 17506722399195233853066953)
        ·
          refine ⟨13130041799396425389800215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17506722399195233853066953 13130041799396425389800215)
          ·
            refine ⟨19695062699094638084700323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13130041799396425389800215 19695062699094638084700323)
            ·
              refine ⟨29542594048641957127050485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19695062699094638084700323 29542594048641957127050485)
              ·
                refine ⟨2769618192060183480660983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29542594048641957127050485 2769618192060183480660983)
                ·
                  refine ⟨4154427288090275220991475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769618192060183480660983 4154427288090275220991475)
                  ·
                    refine ⟨6231640932135412831487213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154427288090275220991475 6231640932135412831487213)
                    ·
                      refine ⟨2336865349550779811807705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231640932135412831487213 2336865349550779811807705)
                      ·
                        rfl

theorem cell23_4551029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4551029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551029 prefixEnd_4551029 := by exact prefixLift 4551029
  have htrace : WordTrace (prefixWord ++ tailWord_4551029) baseStart_4551029 baseEnd_4551029 := by
    simpa [prefixWord, tailWord_4551029, baseEnd_4551029] using wordTrace_append hprefix tailTrace_4551029
  have hstable : (prefixWord ++ tailWord_4551029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551029).length < 2 ^ (prefixWord ++ tailWord_4551029).sum := by decide
  have hdescent : baseEnd_4551029 < baseStart_4551029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551035 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 4]
def baseStart_4551035 : Nat := 118140960795 + 4551035 * 2 ^ 59
def prefixEnd_4551035 : Nat := 4983230072969 + 3 ^ 40 * 4551035 * 2
def baseEnd_4551035 : Nat := 2336868430434706788332677

theorem tailTrace_4551035 : CollatzResearch.WordTrace tailWord_4551035 prefixEnd_4551035 2336868430434706788332677 := by
  unfold tailWord_4551035
  simp only [CollatzResearch.WordTrace]
  refine ⟨165989883067384924742686559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110659922044923283161791039 165989883067384924742686559)
  ·
    refine ⟨248984824601077387114029839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165989883067384924742686559 248984824601077387114029839)
    ·
      refine ⟨373477236901616080671044759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248984824601077387114029839 373477236901616080671044759)
      ·
        refine ⟨560215855352424121006567139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373477236901616080671044759 560215855352424121006567139)
        ·
          refine ⟨840323783028636181509850709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560215855352424121006567139 840323783028636181509850709)
          ·
            refine ⟨9847544332366830252068563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 840323783028636181509850709 9847544332366830252068563)
            ·
              refine ⟨14771316498550245378102845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847544332366830252068563 14771316498550245378102845)
              ·
                refine ⟨5539243686956342016788567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14771316498550245378102845 5539243686956342016788567)
                ·
                  refine ⟨8308865530434513025182851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539243686956342016788567 8308865530434513025182851)
                  ·
                    refine ⟨12463298295651769537774277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8308865530434513025182851 12463298295651769537774277)
                    ·
                      refine ⟨2336868430434706788332677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12463298295651769537774277 2336868430434706788332677)
                      ·
                        rfl

theorem cell23_4551035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 4].length) (baseStart_4551035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551035 prefixEnd_4551035 := by exact prefixLift 4551035
  have htrace : WordTrace (prefixWord ++ tailWord_4551035) baseStart_4551035 baseEnd_4551035 := by
    simpa [prefixWord, tailWord_4551035, baseEnd_4551035] using wordTrace_append hprefix tailTrace_4551035
  have hstable : (prefixWord ++ tailWord_4551035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551035).length < 2 ^ (prefixWord ++ tailWord_4551035).sum := by decide
  have hdescent : baseEnd_4551035 < baseStart_4551035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551048 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4551048 : Nat := 118140960795 + 4551048 * 2 ^ 59
def prefixEnd_4551048 : Nat := 4983230072969 + 3 ^ 40 * 4551048 * 2
def baseEnd_4551048 : Nat := 2336875105683215237470117

theorem tailTrace_4551048 : CollatzResearch.WordTrace tailWord_4551048 prefixEnd_4551048 2336875105683215237470117 := by
  unfold tailWord_4551048
  simp only [CollatzResearch.WordTrace]
  refine ⟨82995178608168913981454899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110660238144225218641939865 82995178608168913981454899)
  ·
    refine ⟨124492767912253370972182349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82995178608168913981454899 124492767912253370972182349)
    ·
      refine ⟨46684787967095014114568381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124492767912253370972182349 46684787967095014114568381)
      ·
        refine ⟨17506795487660630292963143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46684787967095014114568381 17506795487660630292963143)
        ·
          refine ⟨26260193231490945439444715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17506795487660630292963143 26260193231490945439444715)
          ·
            refine ⟨39390289847236418159167073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26260193231490945439444715 39390289847236418159167073)
            ·
              refine ⟨29542717385427313619375305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39390289847236418159167073 29542717385427313619375305)
              ·
                refine ⟨22157038039070485214531479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29542717385427313619375305 22157038039070485214531479)
                ·
                  refine ⟨33235557058605727821797219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22157038039070485214531479 33235557058605727821797219)
                  ·
                    refine ⟨49853335587908591732695829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33235557058605727821797219 49853335587908591732695829)
                    ·
                      refine ⟨2336875105683215237470117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49853335587908591732695829 2336875105683215237470117)
                      ·
                        rfl

theorem cell23_4551048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4551048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551048 prefixEnd_4551048 := by exact prefixLift 4551048
  have htrace : WordTrace (prefixWord ++ tailWord_4551048) baseStart_4551048 baseEnd_4551048 := by
    simpa [prefixWord, tailWord_4551048, baseEnd_4551048] using wordTrace_append hprefix tailTrace_4551048
  have hstable : (prefixWord ++ tailWord_4551048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551048).length < 2 ^ (prefixWord ++ tailWord_4551048).sum := by decide
  have hdescent : baseEnd_4551048 < baseStart_4551048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551052 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_4551052 : Nat := 118140960795 + 4551052 * 2 ^ 59
def prefixEnd_4551052 : Nat := 4983230072969 + 3 ^ 40 * 4551052 * 2
def baseEnd_4551052 : Nat := 2336877159605833221820099

theorem tailTrace_4551052 : CollatzResearch.WordTrace tailWord_4551052 prefixEnd_4551052 2336877159605833221820099 := by
  unfold tailWord_4551052
  simp only [CollatzResearch.WordTrace]
  refine ⟨82995251554161668323027705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110660335405548891097370273 82995251554161668323027705)
  ·
    refine ⟨62246438665621251242270779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82995251554161668323027705 62246438665621251242270779)
    ·
      refine ⟨93369657998431876863406169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62246438665621251242270779 93369657998431876863406169)
      ·
        refine ⟨70027243498823907647554627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93369657998431876863406169 70027243498823907647554627)
        ·
          refine ⟨105040865248235861471331941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70027243498823907647554627 105040865248235861471331941)
          ·
            refine ⟨19695162234044224025874739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105040865248235861471331941 19695162234044224025874739)
            ·
              refine ⟨29542743351066336038812109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19695162234044224025874739 29542743351066336038812109)
              ·
                refine ⟨11078528756649876014554541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29542743351066336038812109 11078528756649876014554541)
                ·
                  refine ⟨4154448283743703505457953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11078528756649876014554541 4154448283743703505457953)
                  ·
                    refine ⟨3115836212807777629093465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154448283743703505457953 3115836212807777629093465)
                    ·
                      refine ⟨2336877159605833221820099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115836212807777629093465 2336877159605833221820099)
                      ·
                        rfl

theorem cell23_4551052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_4551052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551052 prefixEnd_4551052 := by exact prefixLift 4551052
  have htrace : WordTrace (prefixWord ++ tailWord_4551052) baseStart_4551052 baseEnd_4551052 := by
    simpa [prefixWord, tailWord_4551052, baseEnd_4551052] using wordTrace_append hprefix tailTrace_4551052
  have hstable : (prefixWord ++ tailWord_4551052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551052).length < 2 ^ (prefixWord ++ tailWord_4551052).sum := by decide
  have hdescent : baseEnd_4551052 < baseStart_4551052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551072 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_4551072 : Nat := 118140960795 + 4551072 * 2 ^ 59
def prefixEnd_4551072 : Nat := 4983230072969 + 3 ^ 40 * 4551072 * 2
def baseEnd_4551072 : Nat := 2336887429218923143570007

theorem tailTrace_4551072 : CollatzResearch.WordTrace tailWord_4551072 prefixEnd_4551072 2336887429218923143570007 := by
  unfold tailWord_4551072
  simp only [CollatzResearch.WordTrace]
  refine ⟨82995616284125440030891735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110660821712167253374522313 82995616284125440030891735)
  ·
    refine ⟨124493424426188160046337603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82995616284125440030891735 124493424426188160046337603)
    ·
      refine ⟨186740136639282240069506405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124493424426188160046337603 186740136639282240069506405)
      ·
        refine ⟨35013775619865420013032451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186740136639282240069506405 35013775619865420013032451)
        ·
          refine ⟨52520663429798130019548677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35013775619865420013032451 52520663429798130019548677)
          ·
            refine ⟨9847624393087149378665377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52520663429798130019548677 9847624393087149378665377)
            ·
              refine ⟨7385718294815362033999033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9847624393087149378665377 7385718294815362033999033)
              ·
                refine ⟨5539288721111521525499275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385718294815362033999033 5539288721111521525499275)
                ·
                  refine ⟨8308933081667282288248913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539288721111521525499275 8308933081667282288248913)
                  ·
                    refine ⟨6231699811250461716186685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8308933081667282288248913 6231699811250461716186685)
                    ·
                      refine ⟨2336887429218923143570007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231699811250461716186685 2336887429218923143570007)
                      ·
                        rfl

theorem cell23_4551072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_4551072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551072 prefixEnd_4551072 := by exact prefixLift 4551072
  have htrace : WordTrace (prefixWord ++ tailWord_4551072) baseStart_4551072 baseEnd_4551072 := by
    simpa [prefixWord, tailWord_4551072, baseEnd_4551072] using wordTrace_append hprefix tailTrace_4551072
  have hstable : (prefixWord ++ tailWord_4551072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551072).length < 2 ^ (prefixWord ++ tailWord_4551072).sum := by decide
  have hdescent : baseEnd_4551072 < baseStart_4551072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551075 : List Nat := [1, 1, 1, 4, 1, 6, 2, 7]
def baseStart_4551075 : Nat := 118140960795 + 4551075 * 2 ^ 59
def prefixEnd_4551075 : Nat := 4983230072969 + 3 ^ 40 * 4551075 * 2
def baseEnd_4551075 : Nat := 86551443320773578956759

theorem tailTrace_4551075 : CollatzResearch.WordTrace tailWord_4551075 prefixEnd_4551075 86551443320773578956759 := by
  unfold tailWord_4551075
  simp only [CollatzResearch.WordTrace]
  refine ⟨165991341987240011574142679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110660894658160007716095119 165991341987240011574142679)
  ·
    refine ⟨248987012980860017361214019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165991341987240011574142679 248987012980860017361214019)
    ·
      refine ⟨373480519471290026041821029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248987012980860017361214019 373480519471290026041821029)
      ·
        refine ⟨70027597400866879882841443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373480519471290026041821029 70027597400866879882841443)
        ·
          refine ⟨105041396101300319824262165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70027597400866879882841443 105041396101300319824262165)
          ·
            refine ⟨4923815442248452491762289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105041396101300319824262165 4923815442248452491762289)
            ·
              refine ⟨3692861581686339368821717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923815442248452491762289 3692861581686339368821717)
              ·
                refine ⟨86551443320773578956759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3692861581686339368821717 86551443320773578956759)
                ·
                  rfl

theorem cell23_4551075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 7].length) (baseStart_4551075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551075 prefixEnd_4551075 := by exact prefixLift 4551075
  have htrace : WordTrace (prefixWord ++ tailWord_4551075) baseStart_4551075 baseEnd_4551075 := by
    simpa [prefixWord, tailWord_4551075, baseEnd_4551075] using wordTrace_append hprefix tailTrace_4551075
  have hstable : (prefixWord ++ tailWord_4551075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551075).length < 2 ^ (prefixWord ++ tailWord_4551075).sum := by decide
  have hdescent : baseEnd_4551075 < baseStart_4551075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551102 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_4551102 : Nat := 118140960795 + 4551102 * 2 ^ 59
def prefixEnd_4551102 : Nat := 4983230072969 + 3 ^ 40 * 4551102 * 2
def baseEnd_4551102 : Nat := 2336902833638558026194869

theorem tailTrace_4551102 : CollatzResearch.WordTrace tailWord_4551102 prefixEnd_4551102 2336902833638558026194869 := by
  unfold tailWord_4551102
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749040844767774398171945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110661551172094796790250373 20749040844767774398171945)
  ·
    refine ⟨15561780633575830798628959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20749040844767774398171945 15561780633575830798628959)
    ·
      refine ⟨23342670950363746197943439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15561780633575830798628959 23342670950363746197943439)
      ·
        refine ⟨35014006425545619296915159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23342670950363746197943439 35014006425545619296915159)
        ·
          refine ⟨52521009638318428945372739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35014006425545619296915159 52521009638318428945372739)
          ·
            refine ⟨78781514457477643418059109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52521009638318428945372739 78781514457477643418059109)
            ·
              refine ⟨14771533960777058140886083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78781514457477643418059109 14771533960777058140886083)
              ·
                refine ⟨22157300941165587211329125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771533960777058140886083 22157300941165587211329125)
                ·
                  refine ⟨4154493926468547602124211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22157300941165587211329125 4154493926468547602124211)
                  ·
                    refine ⟨6231740889702821403186317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154493926468547602124211 6231740889702821403186317)
                    ·
                      refine ⟨2336902833638558026194869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231740889702821403186317 2336902833638558026194869)
                      ·
                        rfl

theorem cell23_4551102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_4551102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551102 prefixEnd_4551102 := by exact prefixLift 4551102
  have htrace : WordTrace (prefixWord ++ tailWord_4551102) baseStart_4551102 baseEnd_4551102 := by
    simpa [prefixWord, tailWord_4551102, baseEnd_4551102] using wordTrace_append hprefix tailTrace_4551102
  have hstable : (prefixWord ++ tailWord_4551102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551102).length < 2 ^ (prefixWord ++ tailWord_4551102).sum := by decide
  have hdescent : baseEnd_4551102 < baseStart_4551102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551118 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_4551118 : Nat := 118140960795 + 4551118 * 2 ^ 59
def prefixEnd_4551118 : Nat := 4983230072969 + 3 ^ 40 * 4551118 * 2
def baseEnd_4551118 : Nat := 778970349776343321198265

theorem tailTrace_4551118 : CollatzResearch.WordTrace tailWord_4551118 prefixEnd_4551118 778970349776343321198265 := by
  unfold tailWord_4551118
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749113790760528739744751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110661940217389486611972005 20749113790760528739744751)
  ·
    refine ⟨31123670686140793109617127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749113790760528739744751 31123670686140793109617127)
    ·
      refine ⟨46685506029211189664425691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31123670686140793109617127 46685506029211189664425691)
      ·
        refine ⟨70028259043816784496638537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46685506029211189664425691 70028259043816784496638537)
        ·
          refine ⟨52521194282862588372478903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70028259043816784496638537 52521194282862588372478903)
          ·
            refine ⟨78781791424293882558718355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52521194282862588372478903 78781791424293882558718355)
            ·
              refine ⟨118172687136440823838077533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78781791424293882558718355 118172687136440823838077533)
              ·
                refine ⟨44314757676165308939279075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118172687136440823838077533 44314757676165308939279075)
                ·
                  refine ⟨66472136514247963408918613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44314757676165308939279075 66472136514247963408918613)
                  ·
                    refine ⟨778970349776343321198265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66472136514247963408918613 778970349776343321198265)
                    ·
                      rfl

theorem cell23_4551118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_4551118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551118 prefixEnd_4551118 := by exact prefixLift 4551118
  have htrace : WordTrace (prefixWord ++ tailWord_4551118) baseStart_4551118 baseEnd_4551118 := by
    simpa [prefixWord, tailWord_4551118, baseEnd_4551118] using wordTrace_append hprefix tailTrace_4551118
  have hstable : (prefixWord ++ tailWord_4551118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551118).length < 2 ^ (prefixWord ++ tailWord_4551118).sum := by decide
  have hdescent : baseEnd_4551118 < baseStart_4551118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551146 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_4551146 : Nat := 118140960795 + 4551146 * 2 ^ 59
def prefixEnd_4551146 : Nat := 4983230072969 + 3 ^ 40 * 4551146 * 2
def baseEnd_4551146 : Nat := 2336925426787355854044667

theorem tailTrace_4551146 : CollatzResearch.WordTrace tailWord_4551146 prefixEnd_4551146 2336925426787355854044667 := by
  unfold tailWord_4551146
  simp only [CollatzResearch.WordTrace]
  refine ⟨41498482892495697674994323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110662621046655193799984861 41498482892495697674994323)
  ·
    refine ⟨62247724338743546512491485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41498482892495697674994323 62247724338743546512491485)
    ·
      refine ⟨23342896627028829942184307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62247724338743546512491485 23342896627028829942184307)
      ·
        refine ⟨35014344940543244913276461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23342896627028829942184307 35014344940543244913276461)
        ·
          refine ⟨13130379352703716842478673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35014344940543244913276461 13130379352703716842478673)
          ·
            refine ⟨9847784514527787631859005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13130379352703716842478673 9847784514527787631859005)
            ·
              refine ⟨3692919192947920361947127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9847784514527787631859005 3692919192947920361947127)
              ·
                refine ⟨5539378789421880542920691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692919192947920361947127 5539378789421880542920691)
                ·
                  refine ⟨8309068184132820814381037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539378789421880542920691 8309068184132820814381037)
                  ·
                    refine ⟨3115900569049807805392889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8309068184132820814381037 3115900569049807805392889)
                    ·
                      refine ⟨2336925426787355854044667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115900569049807805392889 2336925426787355854044667)
                      ·
                        rfl

theorem cell23_4551146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_4551146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551146 prefixEnd_4551146 := by exact prefixLift 4551146
  have htrace : WordTrace (prefixWord ++ tailWord_4551146) baseStart_4551146 baseEnd_4551146 := by
    simpa [prefixWord, tailWord_4551146, baseEnd_4551146] using wordTrace_append hprefix tailTrace_4551146
  have hstable : (prefixWord ++ tailWord_4551146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551146).length < 2 ^ (prefixWord ++ tailWord_4551146).sum := by decide
  have hdescent : baseEnd_4551146 < baseStart_4551146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551172 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4551172 : Nat := 118140960795 + 4551172 * 2 ^ 59
def prefixEnd_4551172 : Nat := 4983230072969 + 3 ^ 40 * 4551172 * 2
def baseEnd_4551172 : Nat := 2336938777284372752319547

theorem tailTrace_4551172 : CollatzResearch.WordTrace tailWord_4551172 prefixEnd_4551172 2336938777284372752319547 := by
  unfold tailWord_4551172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82997439933944298570211885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110663253245259064760282513 82997439933944298570211885)
  ·
    refine ⟨31124039975229111963829457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82997439933944298570211885 31124039975229111963829457)
    ·
      refine ⟨23343029981421833972872093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31124039975229111963829457 23343029981421833972872093)
      ·
        refine ⟨8753636243033187739827035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23343029981421833972872093 8753636243033187739827035)
        ·
          refine ⟨13130454364549781609740553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753636243033187739827035 13130454364549781609740553)
          ·
            refine ⟨9847840773412336207305415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13130454364549781609740553 9847840773412336207305415)
            ·
              refine ⟨14771761160118504310958123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847840773412336207305415 14771761160118504310958123)
              ·
                refine ⟨22157641740177756466437185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771761160118504310958123 22157641740177756466437185)
                ·
                  refine ⟨16618231305133317349827889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22157641740177756466437185 16618231305133317349827889)
                  ·
                    refine ⟨12463673478849988012370917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16618231305133317349827889 12463673478849988012370917)
                    ·
                      refine ⟨2336938777284372752319547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12463673478849988012370917 2336938777284372752319547)
                      ·
                        rfl

theorem cell23_4551172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4551172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551172 prefixEnd_4551172 := by exact prefixLift 4551172
  have htrace : WordTrace (prefixWord ++ tailWord_4551172) baseStart_4551172 baseEnd_4551172 := by
    simpa [prefixWord, tailWord_4551172, baseEnd_4551172] using wordTrace_append hprefix tailTrace_4551172
  have hstable : (prefixWord ++ tailWord_4551172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551172).length < 2 ^ (prefixWord ++ tailWord_4551172).sum := by decide
  have hdescent : baseEnd_4551172 < baseStart_4551172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551232 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2]
def baseStart_4551232 : Nat := 118140960795 + 4551232 * 2 ^ 59
def prefixEnd_4551232 : Nat := 4983230072969 + 3 ^ 40 * 4551232 * 2
def baseEnd_4551232 : Nat := 2336969586123642517569271

theorem tailTrace_4551232 : CollatzResearch.WordTrace tailWord_4551232 prefixEnd_4551232 2336969586123642517569271 := by
  unfold tailWord_4551232
  simp only [CollatzResearch.WordTrace]
  refine ⟨82998534123835613693803975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110664712165114151591738633 82998534123835613693803975)
  ·
    refine ⟨124497801185753420540705963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82998534123835613693803975 124497801185753420540705963)
    ·
      refine ⟨186746701778630130811058945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124497801185753420540705963 186746701778630130811058945)
      ·
        refine ⟨140060026333972598108294209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186746701778630130811058945 140060026333972598108294209)
        ·
          refine ⟨105045019750479448581220657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140060026333972598108294209 105045019750479448581220657)
          ·
            refine ⟨78783764812859586435915493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105045019750479448581220657 78783764812859586435915493)
            ·
              refine ⟨14771955902411172456734155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78783764812859586435915493 14771955902411172456734155)
              ·
                refine ⟨22157933853616758685101233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771955902411172456734155 22157933853616758685101233)
                ·
                  refine ⟨16618450390212569013825925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22157933853616758685101233 16618450390212569013825925)
                  ·
                    refine ⟨3115959448164856690092361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16618450390212569013825925 3115959448164856690092361)
                    ·
                      refine ⟨2336969586123642517569271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3115959448164856690092361 2336969586123642517569271)
                      ·
                        rfl

theorem cell23_4551232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_4551232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551232 prefixEnd_4551232 := by exact prefixLift 4551232
  have htrace : WordTrace (prefixWord ++ tailWord_4551232) baseStart_4551232 baseEnd_4551232 := by
    simpa [prefixWord, tailWord_4551232, baseEnd_4551232] using wordTrace_append hprefix tailTrace_4551232
  have hstable : (prefixWord ++ tailWord_4551232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551232).length < 2 ^ (prefixWord ++ tailWord_4551232).sum := by decide
  have hdescent : baseEnd_4551232 < baseStart_4551232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551242 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_4551242 : Nat := 118140960795 + 4551242 * 2 ^ 59
def prefixEnd_4551242 : Nat := 4983230072969 + 3 ^ 40 * 4551242 * 2
def baseEnd_4551242 : Nat := 778991573643395826148075

theorem tailTrace_4551242 : CollatzResearch.WordTrace tailWord_4551242 prefixEnd_4551242 778991573643395826148075 := by
  unfold tailWord_4551242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499358244408749773867995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110664955318423332730314653 41499358244408749773867995)
  ·
    refine ⟨62249037366613124660801993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41499358244408749773867995 62249037366613124660801993)
    ·
      refine ⟨46686778024959843495601495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62249037366613124660801993 46686778024959843495601495)
      ·
        refine ⟨70030167037439765243402243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46686778024959843495601495 70030167037439765243402243)
        ·
          refine ⟨105045250556159647865103365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70030167037439765243402243 105045250556159647865103365)
          ·
            refine ⟨19695984479279933974706881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105045250556159647865103365 19695984479279933974706881)
            ·
              refine ⟨14771988359459950481030161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19695984479279933974706881 14771988359459950481030161)
              ·
                refine ⟨11078991269594962860772621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14771988359459950481030161 11078991269594962860772621)
                ·
                  refine ⟨4154621726098111072789733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11078991269594962860772621 4154621726098111072789733)
                  ·
                    refine ⟨778991573643395826148075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154621726098111072789733 778991573643395826148075)
                    ·
                      rfl

theorem cell23_4551242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_4551242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551242 prefixEnd_4551242 := by exact prefixLift 4551242
  have htrace : WordTrace (prefixWord ++ tailWord_4551242) baseStart_4551242 baseEnd_4551242 := by
    simpa [prefixWord, tailWord_4551242, baseEnd_4551242] using wordTrace_append hprefix tailTrace_4551242
  have hstable : (prefixWord ++ tailWord_4551242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551242).length < 2 ^ (prefixWord ++ tailWord_4551242).sum := by decide
  have hdescent : baseEnd_4551242 < baseStart_4551242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551252 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_4551252 : Nat := 118140960795 + 4551252 * 2 ^ 59
def prefixEnd_4551252 : Nat := 4983230072969 + 3 ^ 40 * 4551252 * 2
def baseEnd_4551252 : Nat := 2336979855736732439319179

theorem tailTrace_4551252 : CollatzResearch.WordTrace tailWord_4551252 prefixEnd_4551252 2336979855736732439319179 := by
  unfold tailWord_4551252
  simp only [CollatzResearch.WordTrace]
  refine ⟨82998898853799385401668005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110665198471732513868890673 82998898853799385401668005)
  ·
    refine ⟨15562293535087384762812751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82998898853799385401668005 15562293535087384762812751)
    ·
      refine ⟨23343440302631077144219127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15562293535087384762812751 23343440302631077144219127)
      ·
        refine ⟨35015160453946615716328691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23343440302631077144219127 35015160453946615716328691)
        ·
          refine ⟨52522740680919923574493037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35015160453946615716328691 52522740680919923574493037)
          ·
            refine ⟨19696027755344971340434889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52522740680919923574493037 19696027755344971340434889)
            ·
              refine ⟨14772020816508728505326167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19696027755344971340434889 14772020816508728505326167)
              ·
                refine ⟨22158031224763092757989251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14772020816508728505326167 22158031224763092757989251)
                ·
                  refine ⟨33237046837144639136983877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22158031224763092757989251 33237046837144639136983877)
                  ·
                    refine ⟨6231946281964619838184477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33237046837144639136983877 6231946281964619838184477)
                    ·
                      refine ⟨2336979855736732439319179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231946281964619838184477 2336979855736732439319179)
                      ·
                        rfl

theorem cell23_4551252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_4551252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551252 prefixEnd_4551252 := by exact prefixLift 4551252
  have htrace : WordTrace (prefixWord ++ tailWord_4551252) baseStart_4551252 baseEnd_4551252 := by
    simpa [prefixWord, tailWord_4551252, baseEnd_4551252] using wordTrace_append hprefix tailTrace_4551252
  have hstable : (prefixWord ++ tailWord_4551252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551252).length < 2 ^ (prefixWord ++ tailWord_4551252).sum := by decide
  have hdescent : baseEnd_4551252 < baseStart_4551252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551266 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4551266 : Nat := 118140960795 + 4551266 * 2 ^ 59
def prefixEnd_4551266 : Nat := 4983230072969 + 3 ^ 40 * 4551266 * 2
def baseEnd_4551266 : Nat := 2336987044465895384544115

theorem tailTrace_4551266 : CollatzResearch.WordTrace tailWord_4551266 prefixEnd_4551266 2336987044465895384544115 := by
  unfold tailWord_4551266
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499577082387012798586413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110665538886365367462897101 41499577082387012798586413)
  ·
    refine ⟨15562341405895129799469905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41499577082387012798586413 15562341405895129799469905)
    ·
      refine ⟨11671756054421347349602429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15562341405895129799469905 11671756054421347349602429)
      ·
        refine ⟨4376908520408005256100911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11671756054421347349602429 4376908520408005256100911)
        ·
          refine ⟨6565362780612007884151367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376908520408005256100911 6565362780612007884151367)
          ·
            refine ⟨9848044170918011826227051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565362780612007884151367 9848044170918011826227051)
            ·
              refine ⟨14772066256377017739340577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848044170918011826227051 14772066256377017739340577)
              ·
                refine ⟨11079049692282763304505433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14772066256377017739340577 11079049692282763304505433)
                ·
                  refine ⟨8309287269212072478379075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11079049692282763304505433 8309287269212072478379075)
                  ·
                    refine ⟨12463930903818108717568613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8309287269212072478379075 12463930903818108717568613)
                    ·
                      refine ⟨2336987044465895384544115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12463930903818108717568613 2336987044465895384544115)
                      ·
                        rfl

theorem cell23_4551266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4551266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551266 prefixEnd_4551266 := by exact prefixLift 4551266
  have htrace : WordTrace (prefixWord ++ tailWord_4551266) baseStart_4551266 baseEnd_4551266 := by
    simpa [prefixWord, tailWord_4551266, baseEnd_4551266] using wordTrace_append hprefix tailTrace_4551266
  have hstable : (prefixWord ++ tailWord_4551266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551266).length < 2 ^ (prefixWord ++ tailWord_4551266).sum := by decide
  have hdescent : baseEnd_4551266 < baseStart_4551266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551269 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_4551269 : Nat := 118140960795 + 4551269 * 2 ^ 59
def prefixEnd_4551269 : Nat := 4983230072969 + 3 ^ 40 * 4551269 * 2
def baseEnd_4551269 : Nat := 2336988584907858872806601

theorem tailTrace_4551269 : CollatzResearch.WordTrace tailWord_4551269 prefixEnd_4551269 2336988584907858872806601 := by
  unfold tailWord_4551269
  simp only [CollatzResearch.WordTrace]
  refine ⟨165998417748537182706704861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110665611832358121804469907 165998417748537182706704861)
  ·
    refine ⟨62249406655701443515014323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165998417748537182706704861 62249406655701443515014323)
    ·
      refine ⟨93374109983552165272521485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62249406655701443515014323 93374109983552165272521485)
      ·
        refine ⟨35015291243832061977195557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93374109983552165272521485 35015291243832061977195557)
        ·
          refine ⟨6565367108218511620724167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35015291243832061977195557 6565367108218511620724167)
          ·
            refine ⟨9848050662327767431086251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565367108218511620724167 9848050662327767431086251)
            ·
              refine ⟨14772075993491651146629377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848050662327767431086251 14772075993491651146629377)
              ·
                refine ⟨11079056995118738359972033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14772075993491651146629377 11079056995118738359972033)
                ·
                  refine ⟨8309292746339053769979025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11079056995118738359972033 8309292746339053769979025)
                  ·
                    refine ⟨6231969559754290327484269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8309292746339053769979025 6231969559754290327484269)
                    ·
                      refine ⟨2336988584907858872806601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6231969559754290327484269 2336988584907858872806601)
                      ·
                        rfl

theorem cell23_4551269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_4551269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551269 prefixEnd_4551269 := by exact prefixLift 4551269
  have htrace : WordTrace (prefixWord ++ tailWord_4551269) baseStart_4551269 baseEnd_4551269 := by
    simpa [prefixWord, tailWord_4551269, baseEnd_4551269] using wordTrace_append hprefix tailTrace_4551269
  have hstable : (prefixWord ++ tailWord_4551269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551269).length < 2 ^ (prefixWord ++ tailWord_4551269).sum := by decide
  have hdescent : baseEnd_4551269 < baseStart_4551269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551289 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 6]
def baseStart_4551289 : Nat := 118140960795 + 4551289 * 2 ^ 59
def prefixEnd_4551289 : Nat := 4983230072969 + 3 ^ 40 * 4551289 * 2
def baseEnd_4551289 : Nat := 259666539391216532728501

theorem tailTrace_4551289 : CollatzResearch.WordTrace tailWord_4551289 prefixEnd_4551289 259666539391216532728501 := by
  unfold tailWord_4551289
  simp only [CollatzResearch.WordTrace]
  refine ⟨165999147208464726122432921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110666098138976484081621947 165999147208464726122432921)
  ·
    refine ⟨124499360406348544591824691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165999147208464726122432921 124499360406348544591824691)
    ·
      refine ⟨186749040609522816887737037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124499360406348544591824691 186749040609522816887737037)
      ·
        refine ⟨70030890228571056332901389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186749040609522816887737037 70030890228571056332901389)
        ·
          refine ⟨26261583835714146124838021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70030890228571056332901389 26261583835714146124838021)
          ·
            refine ⟨4924046969196402398407129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26261583835714146124838021 4924046969196402398407129)
            ·
              refine ⟨3693035226897301798805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924046969196402398407129 3693035226897301798805347)
              ·
                refine ⟨5539552840345952698208021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693035226897301798805347 5539552840345952698208021)
                ·
                  refine ⟨259666539391216532728501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5539552840345952698208021 259666539391216532728501)
                  ·
                    rfl

theorem cell23_4551289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_4551289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551289 prefixEnd_4551289 := by exact prefixLift 4551289
  have htrace : WordTrace (prefixWord ++ tailWord_4551289) baseStart_4551289 baseEnd_4551289 := by
    simpa [prefixWord, tailWord_4551289, baseEnd_4551289] using wordTrace_append hprefix tailTrace_4551289
  have hstable : (prefixWord ++ tailWord_4551289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551289).length < 2 ^ (prefixWord ++ tailWord_4551289).sum := by decide
  have hdescent : baseEnd_4551289 < baseStart_4551289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551292 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_4551292 : Nat := 118140960795 + 4551292 * 2 ^ 59
def prefixEnd_4551292 : Nat := 4983230072969 + 3 ^ 40 * 4551292 * 2
def baseEnd_4551292 : Nat := 2337000394962912282818995

theorem tailTrace_4551292 : CollatzResearch.WordTrace tailWord_4551292 prefixEnd_4551292 2337000394962912282818995 := by
  unfold tailWord_4551292
  simp only [CollatzResearch.WordTrace]
  refine ⟨82999628313726928817396065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110666171084969238423194753 82999628313726928817396065)
  ·
    refine ⟨62249721235295196613047049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82999628313726928817396065 62249721235295196613047049)
    ·
      refine ⟨46687290926471397459785287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62249721235295196613047049 46687290926471397459785287)
      ·
        refine ⟨70030936389707096189677931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46687290926471397459785287 70030936389707096189677931)
        ·
          refine ⟨105046404584560644284516897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70030936389707096189677931 105046404584560644284516897)
          ·
            refine ⟨78784803438420483213387673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105046404584560644284516897 78784803438420483213387673)
            ·
              refine ⟨59088602578815362410040755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78784803438420483213387673 59088602578815362410040755)
              ·
                refine ⟨88632903868223043615061133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59088602578815362410040755 88632903868223043615061133)
                ·
                  refine ⟨33237338950583641355647925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88632903868223043615061133 33237338950583641355647925)
                  ·
                    refine ⟨3116000526617216377091993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33237338950583641355647925 3116000526617216377091993)
                    ·
                      refine ⟨2337000394962912282818995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116000526617216377091993 2337000394962912282818995)
                      ·
                        rfl

theorem cell23_4551292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_4551292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551292 prefixEnd_4551292 := by exact prefixLift 4551292
  have htrace : WordTrace (prefixWord ++ tailWord_4551292) baseStart_4551292 baseEnd_4551292 := by
    simpa [prefixWord, tailWord_4551292, baseEnd_4551292] using wordTrace_append hprefix tailTrace_4551292
  have hstable : (prefixWord ++ tailWord_4551292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551292).length < 2 ^ (prefixWord ++ tailWord_4551292).sum := by decide
  have hdescent : baseEnd_4551292 < baseStart_4551292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551315 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 6]
def baseStart_4551315 : Nat := 118140960795 + 4551315 * 2 ^ 59
def prefixEnd_4551315 : Nat := 4983230072969 + 3 ^ 40 * 4551315 * 2
def baseEnd_4551315 : Nat := 779004068339321897610463

theorem tailTrace_4551315 : CollatzResearch.WordTrace tailWord_4551315 prefixEnd_4551315 779004068339321897610463 := by
  unfold tailWord_4551315
  simp only [CollatzResearch.WordTrace]
  refine ⟨166000095506370532562879399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110666730337580355041919599 166000095506370532562879399)
  ·
    refine ⟨249000143259555798844319099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166000095506370532562879399 249000143259555798844319099)
    ·
      refine ⟨373500214889333698266478649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249000143259555798844319099 373500214889333698266478649)
      ·
        refine ⟨280125161167000273699858987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373500214889333698266478649 280125161167000273699858987)
        ·
          refine ⟨420187741750500410549788481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280125161167000273699858987 420187741750500410549788481)
          ·
            refine ⟨315140806312875307912341361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420187741750500410549788481 315140806312875307912341361)
            ·
              refine ⟨236355604734656480934256021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315140806312875307912341361 236355604734656480934256021)
              ·
                refine ⟨11079168971937022543793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236355604734656480934256021 11079168971937022543793251)
                ·
                  refine ⟨16618753457905533815689877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11079168971937022543793251 16618753457905533815689877)
                  ·
                    refine ⟨779004068339321897610463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16618753457905533815689877 779004068339321897610463)
                    ·
                      rfl

theorem cell23_4551315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_4551315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551315 prefixEnd_4551315 := by exact prefixLift 4551315
  have htrace : WordTrace (prefixWord ++ tailWord_4551315) baseStart_4551315 baseEnd_4551315 := by
    simpa [prefixWord, tailWord_4551315, baseEnd_4551315] using wordTrace_append hprefix tailTrace_4551315
  have hstable : (prefixWord ++ tailWord_4551315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551315).length < 2 ^ (prefixWord ++ tailWord_4551315).sum := by decide
  have hdescent : baseEnd_4551315 < baseStart_4551315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551319 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 1, 5]
def baseStart_4551319 : Nat := 118140960795 + 4551319 * 2 ^ 59
def prefixEnd_4551319 : Nat := 4983230072969 + 3 ^ 40 * 4551319 * 2
def baseEnd_4551319 : Nat := 779004752980194559060457

theorem tailTrace_4551319 : CollatzResearch.WordTrace tailWord_4551319 prefixEnd_4551319 779004752980194559060457 := by
  unfold tailWord_4551319
  simp only [CollatzResearch.WordTrace]
  refine ⟨166000241398356041246025011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110666827598904027497350007 166000241398356041246025011)
  ·
    refine ⟨249000362097534061869037517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166000241398356041246025011 249000362097534061869037517)
    ·
      refine ⟨93375135786575273200889069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249000362097534061869037517 93375135786575273200889069)
      ·
        refine ⟨35015675919965727450333401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93375135786575273200889069 35015675919965727450333401)
        ·
          refine ⟨26261756939974295587750051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35015675919965727450333401 26261756939974295587750051)
          ·
            refine ⟨39392635409961443381625077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26261756939974295587750051 39392635409961443381625077)
            ·
              refine ⟨3693059569683885317027351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39392635409961443381625077 3693059569683885317027351)
              ·
                refine ⟨5539589354525827975541027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693059569683885317027351 5539589354525827975541027)
                ·
                  refine ⟨8309384031788741963311541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539589354525827975541027 8309384031788741963311541)
                  ·
                    refine ⟨779004752980194559060457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8309384031788741963311541 779004752980194559060457)
                    ·
                      rfl

theorem cell23_4551319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_4551319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551319 prefixEnd_4551319 := by exact prefixLift 4551319
  have htrace : WordTrace (prefixWord ++ tailWord_4551319) baseStart_4551319 baseEnd_4551319 := by
    simpa [prefixWord, tailWord_4551319, baseEnd_4551319] using wordTrace_append hprefix tailTrace_4551319
  have hstable : (prefixWord ++ tailWord_4551319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551319).length < 2 ^ (prefixWord ++ tailWord_4551319).sum := by decide
  have hdescent : baseEnd_4551319 < baseStart_4551319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551326 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4551326 : Nat := 118140960795 + 4551326 * 2 ^ 59
def prefixEnd_4551326 : Nat := 4983230072969 + 3 ^ 40 * 4551326 * 2
def baseEnd_4551326 : Nat := 2337017853305165149793839

theorem tailTrace_4551326 : CollatzResearch.WordTrace tailWord_4551326 prefixEnd_4551326 2337017853305165149793839 := by
  unfold tailWord_4551326
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750062088666335180191229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110666997806220454294353221 20750062088666335180191229)
  ·
    refine ⟨7781273283249875692571711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20750062088666335180191229 7781273283249875692571711)
    ·
      refine ⟨11671909924874813538857567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7781273283249875692571711 11671909924874813538857567)
      ·
        refine ⟨17507864887312220308286351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11671909924874813538857567 17507864887312220308286351)
        ·
          refine ⟨26261797330968330462429527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17507864887312220308286351 26261797330968330462429527)
          ·
            refine ⟨39392695996452495693644291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26261797330968330462429527 39392695996452495693644291)
            ·
              refine ⟨59089043994678743540466437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39392695996452495693644291 59089043994678743540466437)
              ·
                refine ⟨11079195749002264413837457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59089043994678743540466437 11079195749002264413837457)
                ·
                  refine ⟨8309396811751698310378093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11079195749002264413837457 8309396811751698310378093)
                  ·
                    refine ⟨3116023804406886866391785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8309396811751698310378093 3116023804406886866391785)
                    ·
                      refine ⟨2337017853305165149793839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116023804406886866391785 2337017853305165149793839)
                      ·
                        rfl

theorem cell23_4551326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4551326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551326 prefixEnd_4551326 := by exact prefixLift 4551326
  have htrace : WordTrace (prefixWord ++ tailWord_4551326) baseStart_4551326 baseEnd_4551326 := by
    simpa [prefixWord, tailWord_4551326, baseEnd_4551326] using wordTrace_append hprefix tailTrace_4551326
  have hstable : (prefixWord ++ tailWord_4551326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551326).length < 2 ^ (prefixWord ++ tailWord_4551326).sum := by decide
  have hdescent : baseEnd_4551326 < baseStart_4551326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551349 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4551349 : Nat := 118140960795 + 4551349 * 2 ^ 59
def prefixEnd_4551349 : Nat := 4983230072969 + 3 ^ 40 * 4551349 * 2
def baseEnd_4551349 : Nat := 779009887786739519935411

theorem tailTrace_4551349 : CollatzResearch.WordTrace tailWord_4551349 prefixEnd_4551349 779009887786739519935411 := by
  unfold tailWord_4551349
  simp only [CollatzResearch.WordTrace]
  refine ⟨166001335588247356369617101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110667557058831570913078067 166001335588247356369617101)
  ·
    refine ⟨62250500845592758638606413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166001335588247356369617101 62250500845592758638606413)
    ·
      refine ⟨23343937817097284489477405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62250500845592758638606413 23343937817097284489477405)
      ·
        refine ⟨8753976681411481683554027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23343937817097284489477405 8753976681411481683554027)
        ·
          refine ⟨13130965022117222525331041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8753976681411481683554027 13130965022117222525331041)
          ·
            refine ⟨9848223766587916893998281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13130965022117222525331041 9848223766587916893998281)
            ·
              refine ⟨7386167824940937670498711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9848223766587916893998281 7386167824940937670498711)
              ·
                refine ⟨11079251737411406505748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7386167824940937670498711 11079251737411406505748067)
                ·
                  refine ⟨16618877606117109758622101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11079251737411406505748067 16618877606117109758622101)
                  ·
                    refine ⟨779009887786739519935411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16618877606117109758622101 779009887786739519935411)
                    ·
                      rfl

theorem cell23_4551349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4551349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551349 prefixEnd_4551349 := by exact prefixLift 4551349
  have htrace : WordTrace (prefixWord ++ tailWord_4551349) baseStart_4551349 baseEnd_4551349 := by
    simpa [prefixWord, tailWord_4551349, baseEnd_4551349] using wordTrace_append hprefix tailTrace_4551349
  have hstable : (prefixWord ++ tailWord_4551349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551349).length < 2 ^ (prefixWord ++ tailWord_4551349).sum := by decide
  have hdescent : baseEnd_4551349 < baseStart_4551349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551356 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4551356 : Nat := 118140960795 + 4551356 * 2 ^ 59
def prefixEnd_4551356 : Nat := 4983230072969 + 3 ^ 40 * 4551356 * 2
def baseEnd_4551356 : Nat := 2337033257724800032418701

theorem tailTrace_4551356 : CollatzResearch.WordTrace tailWord_4551356 prefixEnd_4551356 2337033257724800032418701 := by
  unfold tailWord_4551356
  simp only [CollatzResearch.WordTrace]
  refine ⟨83000795449610998282560961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110667727266147997710081281 83000795449610998282560961)
  ·
    refine ⟨62250596587208248711920721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83000795449610998282560961 62250596587208248711920721)
    ·
      refine ⟨46687947440406186533940541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62250596587208248711920721 46687947440406186533940541)
      ·
        refine ⟨17507980290152319950227703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46687947440406186533940541 17507980290152319950227703)
        ·
          refine ⟨26261970435228479925341555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17507980290152319950227703 26261970435228479925341555)
          ·
            refine ⟨39392955652842719888012333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26261970435228479925341555 39392955652842719888012333)
            ·
              refine ⟨14772358369816019958004625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39392955652842719888012333 14772358369816019958004625)
              ·
                refine ⟨11079268777362014968503469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14772358369816019958004625 11079268777362014968503469)
                ·
                  refine ⟨4154725791510755613188801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11079268777362014968503469 4154725791510755613188801)
                  ·
                    refine ⟨3116044343633066709891601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154725791510755613188801 3116044343633066709891601)
                    ·
                      refine ⟨2337033257724800032418701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116044343633066709891601 2337033257724800032418701)
                      ·
                        rfl

theorem cell23_4551356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4551356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551356 prefixEnd_4551356 := by exact prefixLift 4551356
  have htrace : WordTrace (prefixWord ++ tailWord_4551356) baseStart_4551356 baseEnd_4551356 := by
    simpa [prefixWord, tailWord_4551356, baseEnd_4551356] using wordTrace_append hprefix tailTrace_4551356
  have hstable : (prefixWord ++ tailWord_4551356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551356).length < 2 ^ (prefixWord ++ tailWord_4551356).sum := by decide
  have hdescent : baseEnd_4551356 < baseStart_4551356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551373 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4551373 : Nat := 118140960795 + 4551373 * 2 ^ 59
def prefixEnd_4551373 : Nat := 4983230072969 + 3 ^ 40 * 4551373 * 2
def baseEnd_4551373 : Nat := 2337041986895926465906123

theorem tailTrace_4551373 : CollatzResearch.WordTrace tailWord_4551373 prefixEnd_4551373 2337041986895926465906123 := by
  unfold tailWord_4551373
  simp only [CollatzResearch.WordTrace]
  refine ⟨166002210940160408468490773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110668140626773605645660515 166002210940160408468490773)
  ·
    refine ⟨7781353637820019146960505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166002210940160408468490773 7781353637820019146960505)
    ·
      refine ⟨5836015228365014360220379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7781353637820019146960505 5836015228365014360220379)
      ·
        refine ⟨8754022842547521540330569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836015228365014360220379 8754022842547521540330569)
        ·
          refine ⟨6565517131910641155247927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8754022842547521540330569 6565517131910641155247927)
          ·
            refine ⟨9848275697865961732871891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565517131910641155247927 9848275697865961732871891)
            ·
              refine ⟨14772413546798942599307837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848275697865961732871891 14772413546798942599307837)
              ·
                refine ⟨5539655080049603474740439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14772413546798942599307837 5539655080049603474740439)
                ·
                  refine ⟨8309482620074405212110659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539655080049603474740439 8309482620074405212110659)
                  ·
                    refine ⟨12464223930111607818165989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8309482620074405212110659 12464223930111607818165989)
                    ·
                      refine ⟨2337041986895926465906123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12464223930111607818165989 2337041986895926465906123)
                      ·
                        rfl

theorem cell23_4551373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4551373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551373 prefixEnd_4551373 := by exact prefixLift 4551373
  have htrace : WordTrace (prefixWord ++ tailWord_4551373) baseStart_4551373 baseEnd_4551373 := by
    simpa [prefixWord, tailWord_4551373, baseEnd_4551373] using wordTrace_append hprefix tailTrace_4551373
  have hstable : (prefixWord ++ tailWord_4551373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551373).length < 2 ^ (prefixWord ++ tailWord_4551373).sum := by decide
  have hdescent : baseEnd_4551373 < baseStart_4551373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551406 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_4551406 : Nat := 118140960795 + 4551406 * 2 ^ 59
def prefixEnd_4551406 : Nat := 4983230072969 + 3 ^ 40 * 4551406 * 2
def baseEnd_4551406 : Nat := 2337058931757524836793471

theorem tailTrace_4551406 : CollatzResearch.WordTrace tailWord_4551406 prefixEnd_4551406 2337058931757524836793471 := by
  unfold tailWord_4551406
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750426818630106888055259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110668943032693903402961381 20750426818630106888055259)
  ·
    refine ⟨31125640227945160332082889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20750426818630106888055259 31125640227945160332082889)
    ·
      refine ⟨23344230170958870249062167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31125640227945160332082889 23344230170958870249062167)
      ·
        refine ⟨35016345256438305373593251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23344230170958870249062167 35016345256438305373593251)
        ·
          refine ⟨52524517884657458060389877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35016345256438305373593251 52524517884657458060389877)
          ·
            refine ⟨4924173551686636693161551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52524517884657458060389877 4924173551686636693161551)
            ·
              refine ⟨7386260327529955039742327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4924173551686636693161551 7386260327529955039742327)
              ·
                refine ⟨11079390491294932559613491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7386260327529955039742327 11079390491294932559613491)
                ·
                  refine ⟨16619085736942398839420237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11079390491294932559613491 16619085736942398839420237)
                  ·
                    refine ⟨6232157151353399564782589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16619085736942398839420237 6232157151353399564782589)
                    ·
                      refine ⟨2337058931757524836793471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6232157151353399564782589 2337058931757524836793471)
                      ·
                        rfl

theorem cell23_4551406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_4551406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551406 prefixEnd_4551406 := by exact prefixLift 4551406
  have htrace : WordTrace (prefixWord ++ tailWord_4551406) baseStart_4551406 baseEnd_4551406 := by
    simpa [prefixWord, tailWord_4551406, baseEnd_4551406] using wordTrace_append hprefix tailTrace_4551406
  have hstable : (prefixWord ++ tailWord_4551406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551406).length < 2 ^ (prefixWord ++ tailWord_4551406).sum := by decide
  have hdescent : baseEnd_4551406 < baseStart_4551406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551416 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_4551416 : Nat := 118140960795 + 4551416 * 2 ^ 59
def prefixEnd_4551416 : Nat := 4983230072969 + 3 ^ 40 * 4551416 * 2
def baseEnd_4551416 : Nat := 2337064066564069797668425

theorem tailTrace_4551416 : CollatzResearch.WordTrace tailWord_4551416 prefixEnd_4551416 2337064066564069797668425 := by
  unfold tailWord_4551416
  simp only [CollatzResearch.WordTrace]
  refine ⟨83001889639502313406153051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110669186186003084541537401 83001889639502313406153051)
  ·
    refine ⟨124502834459253470109229577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83001889639502313406153051 124502834459253470109229577)
    ·
      refine ⟨93377125844440102581922183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124502834459253470109229577 93377125844440102581922183)
      ·
        refine ⟨140065688766660153872883275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93377125844440102581922183 140065688766660153872883275)
        ·
          refine ⟨210098533149990230809324913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140065688766660153872883275 210098533149990230809324913)
          ·
            refine ⟨157573899862492673106993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210098533149990230809324913 157573899862492673106993685)
            ·
              refine ⟨7386276556054344051890329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157573899862492673106993685 7386276556054344051890329)
              ·
                refine ⟨5539707417040758038917747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7386276556054344051890329 5539707417040758038917747)
                ·
                  refine ⟨8309561125561137058376621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539707417040758038917747 8309561125561137058376621)
                  ·
                    refine ⟨3116085422085426396891233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8309561125561137058376621 3116085422085426396891233)
                    ·
                      refine ⟨2337064066564069797668425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116085422085426396891233 2337064066564069797668425)
                      ·
                        rfl

theorem cell23_4551416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_4551416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551416 prefixEnd_4551416 := by exact prefixLift 4551416
  have htrace : WordTrace (prefixWord ++ tailWord_4551416) baseStart_4551416 baseEnd_4551416 := by
    simpa [prefixWord, tailWord_4551416, baseEnd_4551416] using wordTrace_append hprefix tailTrace_4551416
  have hstable : (prefixWord ++ tailWord_4551416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551416).length < 2 ^ (prefixWord ++ tailWord_4551416).sum := by decide
  have hdescent : baseEnd_4551416 < baseStart_4551416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551429 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_4551429 : Nat := 118140960795 + 4551429 * 2 ^ 59
def prefixEnd_4551429 : Nat := 4983230072969 + 3 ^ 40 * 4551429 * 2
def baseEnd_4551429 : Nat := 2337070741812578246805865

theorem tailTrace_4551429 : CollatzResearch.WordTrace tailWord_4551429 prefixEnd_4551429 2337070741812578246805865 := by
  unfold tailWord_4551429
  simp only [CollatzResearch.WordTrace]
  refine ⟨166004253427957530032529341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110669502285305020021686227 166004253427957530032529341)
  ·
    refine ⟨62251595035484073762198503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166004253427957530032529341 62251595035484073762198503)
    ·
      refine ⟨93377392553226110643297755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62251595035484073762198503 93377392553226110643297755)
      ·
        refine ⟨140066088829839165964946633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93377392553226110643297755 140066088829839165964946633)
        ·
          refine ⟨105049566622379374473709975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140066088829839165964946633 105049566622379374473709975)
          ·
            refine ⟨157574349933569061710564963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105049566622379374473709975 157574349933569061710564963)
            ·
              refine ⟨236361524900353592565847445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157574349933569061710564963 236361524900353592565847445)
              ·
                refine ⟨11079446479704074651524099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236361524900353592565847445 11079446479704074651524099)
                ·
                  refine ⟨16619169719556111977286149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11079446479704074651524099 16619169719556111977286149)
                  ·
                    refine ⟨3116094322416770995741153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16619169719556111977286149 3116094322416770995741153)
                    ·
                      refine ⟨2337070741812578246805865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116094322416770995741153 2337070741812578246805865)
                      ·
                        rfl

theorem cell23_4551429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_4551429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551429 prefixEnd_4551429 := by exact prefixLift 4551429
  have htrace : WordTrace (prefixWord ++ tailWord_4551429) baseStart_4551429 baseEnd_4551429 := by
    simpa [prefixWord, tailWord_4551429, baseEnd_4551429] using wordTrace_append hprefix tailTrace_4551429
  have hstable : (prefixWord ++ tailWord_4551429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551429).length < 2 ^ (prefixWord ++ tailWord_4551429).sum := by decide
  have hdescent : baseEnd_4551429 < baseStart_4551429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551432 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4551432 : Nat := 118140960795 + 4551432 * 2 ^ 59
def prefixEnd_4551432 : Nat := 4983230072969 + 3 ^ 40 * 4551432 * 2
def baseEnd_4551432 : Nat := 2337072282254541735068351

theorem tailTrace_4551432 : CollatzResearch.WordTrace tailWord_4551432 prefixEnd_4551432 2337072282254541735068351 := by
  unfold tailWord_4551432
  simp only [CollatzResearch.WordTrace]
  refine ⟨83002181423473330772444275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110669575231297774363259033 83002181423473330772444275)
  ·
    refine ⟨124503272135209996158666413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83002181423473330772444275 124503272135209996158666413)
    ·
      refine ⟨46688727050703748559499905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124503272135209996158666413 46688727050703748559499905)
      ·
        refine ⟨35016545288027811419624929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46688727050703748559499905 35016545288027811419624929)
        ·
          refine ⟨26262408966020858564718697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35016545288027811419624929 26262408966020858564718697)
          ·
            refine ⟨19696806724515643923539023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26262408966020858564718697 19696806724515643923539023)
            ·
              refine ⟨29545210086773465885308535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19696806724515643923539023 29545210086773465885308535)
              ·
                refine ⟨44317815130160198827962803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29545210086773465885308535 44317815130160198827962803)
                ·
                  refine ⟨66476722695240298241944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44317815130160198827962803 66476722695240298241944205)
                  ·
                    refine ⟨24928771010715111840729077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66476722695240298241944205 24928771010715111840729077)
                    ·
                      refine ⟨2337072282254541735068351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24928771010715111840729077 2337072282254541735068351)
                      ·
                        rfl

theorem cell23_4551432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4551432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551432 prefixEnd_4551432 := by exact prefixLift 4551432
  have htrace : WordTrace (prefixWord ++ tailWord_4551432) baseStart_4551432 baseEnd_4551432 := by
    simpa [prefixWord, tailWord_4551432, baseEnd_4551432] using wordTrace_append hprefix tailTrace_4551432
  have hstable : (prefixWord ++ tailWord_4551432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551432).length < 2 ^ (prefixWord ++ tailWord_4551432).sum := by decide
  have hdescent : baseEnd_4551432 < baseStart_4551432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551559 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 8]
def baseStart_4551559 : Nat := 118140960795 + 4551559 * 2 ^ 59
def prefixEnd_4551559 : Nat := 4983230072969 + 3 ^ 40 * 4551559 * 2
def baseEnd_4551559 : Nat := 259681943810851415353363

theorem tailTrace_4551559 : CollatzResearch.WordTrace tailWord_4551559 prefixEnd_4551559 259681943810851415353363 := by
  unfold tailWord_4551559
  simp only [CollatzResearch.WordTrace]
  refine ⟨166008994917486562234761731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110672663278324374823174487 166008994917486562234761731)
  ·
    refine ⟨249013492376229843352142597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166008994917486562234761731 249013492376229843352142597)
    ·
      refine ⟨46690029820543095628526737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249013492376229843352142597 46690029820543095628526737)
      ·
        refine ⟨35017522365407321721395053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46690029820543095628526737 35017522365407321721395053)
        ·
          refine ⟨13131570887027745645523145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35017522365407321721395053 13131570887027745645523145)
          ·
            refine ⟨9848678165270809234142359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13131570887027745645523145 9848678165270809234142359)
            ·
              refine ⟨14773017247906213851213539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848678165270809234142359 14773017247906213851213539)
              ·
                refine ⟨22159525871859320776820309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14773017247906213851213539 22159525871859320776820309)
                ·
                  refine ⟨259681943810851415353363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22159525871859320776820309 259681943810851415353363)
                  ·
                    rfl

theorem cell23_4551559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 8].length) (baseStart_4551559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551559 prefixEnd_4551559 := by exact prefixLift 4551559
  have htrace : WordTrace (prefixWord ++ tailWord_4551559) baseStart_4551559 baseEnd_4551559 := by
    simpa [prefixWord, tailWord_4551559, baseEnd_4551559] using wordTrace_append hprefix tailTrace_4551559
  have hstable : (prefixWord ++ tailWord_4551559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551559).length < 2 ^ (prefixWord ++ tailWord_4551559).sum := by decide
  have hdescent : baseEnd_4551559 < baseStart_4551559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 7, 1, 1, 3]
def baseStart_4551603 : Nat := 118140960795 + 4551603 * 2 ^ 59
def prefixEnd_4551603 : Nat := 4983230072969 + 3 ^ 40 * 4551603 * 2
def baseEnd_4551603 : Nat := 2337160087446460566030065

theorem tailTrace_4551603 : CollatzResearch.WordTrace tailWord_4551603 prefixEnd_4551603 2337160087446460566030065 := by
  unfold tailWord_4551603
  simp only [CollatzResearch.WordTrace]
  refine ⟨166010599729327157749363463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110673733152884771832908975 166010599729327157749363463)
  ·
    refine ⟨249015899593990736624045195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166010599729327157749363463 249015899593990736624045195)
    ·
      refine ⟨373523849390986104936067793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249015899593990736624045195 373523849390986104936067793)
      ·
        refine ⟨280142887043239578702050845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373523849390986104936067793 280142887043239578702050845)
        ·
          refine ⟨105053582641214842013269067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 280142887043239578702050845 105053582641214842013269067)
          ·
            refine ⟨157580373961822263019903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105053582641214842013269067 157580373961822263019903601)
            ·
              refine ⟨118185280471366697264927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157580373961822263019903601 118185280471366697264927701)
              ·
                refine ⟨2769967511047656967146743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118185280471366697264927701 2769967511047656967146743)
                ·
                  refine ⟨4154951266571485450720115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769967511047656967146743 4154951266571485450720115)
                  ·
                    refine ⟨6232426899857228176080173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4154951266571485450720115 6232426899857228176080173)
                    ·
                      refine ⟨2337160087446460566030065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6232426899857228176080173 2337160087446460566030065)
                      ·
                        rfl

theorem cell23_4551603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 1, 1, 3].length) (baseStart_4551603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551603 prefixEnd_4551603 := by exact prefixLift 4551603
  have htrace : WordTrace (prefixWord ++ tailWord_4551603) baseStart_4551603 baseEnd_4551603 := by
    simpa [prefixWord, tailWord_4551603, baseEnd_4551603] using wordTrace_append hprefix tailTrace_4551603
  have hstable : (prefixWord ++ tailWord_4551603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551603).length < 2 ^ (prefixWord ++ tailWord_4551603).sum := by decide
  have hdescent : baseEnd_4551603 < baseStart_4551603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551653 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_4551653 : Nat := 118140960795 + 4551653 * 2 ^ 59
def prefixEnd_4551653 : Nat := 4983230072969 + 3 ^ 40 * 4551653 * 2
def baseEnd_4551653 : Nat := 779061920493061790134945

theorem tailTrace_4551653 : CollatzResearch.WordTrace tailWord_4551653 prefixEnd_4551653 779061920493061790134945 := by
  unfold tailWord_4551653
  simp only [CollatzResearch.WordTrace]
  refine ⟨166012423379146016288683613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110674948919430677525789075 166012423379146016288683613)
  ·
    refine ⟨62254658767179756108256355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166012423379146016288683613 62254658767179756108256355)
    ·
      refine ⟨93381988150769634162384533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62254658767179756108256355 93381988150769634162384533)
      ·
        refine ⟨4377280694567326601361775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93381988150769634162384533 4377280694567326601361775)
        ·
          refine ⟨6565921041850989902042663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377280694567326601361775 6565921041850989902042663)
          ·
            refine ⟨9848881562776484853063995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565921041850989902042663 9848881562776484853063995)
            ·
              refine ⟨14773322344164727279595993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848881562776484853063995 14773322344164727279595993)
              ·
                refine ⟨11079991758123545459696995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14773322344164727279595993 11079991758123545459696995)
                ·
                  refine ⟨16619987637185318189545493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11079991758123545459696995 16619987637185318189545493)
                  ·
                    refine ⟨779061920493061790134945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16619987637185318189545493 779061920493061790134945)
                    ·
                      rfl

theorem cell23_4551653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_4551653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551653 prefixEnd_4551653 := by exact prefixLift 4551653
  have htrace : WordTrace (prefixWord ++ tailWord_4551653) baseStart_4551653 baseEnd_4551653 := by
    simpa [prefixWord, tailWord_4551653, baseEnd_4551653] using wordTrace_append hprefix tailTrace_4551653
  have hstable : (prefixWord ++ tailWord_4551653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551653).length < 2 ^ (prefixWord ++ tailWord_4551653).sum := by decide
  have hdescent : baseEnd_4551653 < baseStart_4551653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551666 : List Nat := [3, 2, 1, 5, 1, 11]
def baseStart_4551666 : Nat := 118140960795 + 4551666 * 2 ^ 59
def prefixEnd_4551666 : Nat := 4983230072969 + 3 ^ 40 * 4551666 * 2
def baseEnd_4551666 : Nat := 9618075871307381973425

theorem tailTrace_4551666 : CollatzResearch.WordTrace tailWord_4551666 prefixEnd_4551666 9618075871307381973425 := by
  unfold tailWord_4551666
  simp only [CollatzResearch.WordTrace]
  refine ⟨41503224382024729877226713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110675265018732613005937901 41503224382024729877226713)
  ·
    refine ⟨31127418286518547407920035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41503224382024729877226713 31127418286518547407920035)
    ·
      refine ⟨46691127429777821111880053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31127418286518547407920035 46691127429777821111880053)
      ·
        refine ⟨4377293196541670729238755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46691127429777821111880053 4377293196541670729238755)
        ·
          refine ⟨6565939794812506093858133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377293196541670729238755 6565939794812506093858133)
          ·
            refine ⟨9618075871307381973425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6565939794812506093858133 9618075871307381973425)
            ·
              rfl

theorem cell23_4551666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 11].length) (baseStart_4551666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551666 prefixEnd_4551666 := by exact prefixLift 4551666
  have htrace : WordTrace (prefixWord ++ tailWord_4551666) baseStart_4551666 baseEnd_4551666 := by
    simpa [prefixWord, tailWord_4551666, baseEnd_4551666] using wordTrace_append hprefix tailTrace_4551666
  have hstable : (prefixWord ++ tailWord_4551666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551666).length < 2 ^ (prefixWord ++ tailWord_4551666).sum := by decide
  have hdescent : baseEnd_4551666 < baseStart_4551666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551670 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4551670 : Nat := 118140960795 + 4551670 * 2 ^ 59
def prefixEnd_4551670 : Nat := 4983230072969 + 3 ^ 40 * 4551670 * 2
def baseEnd_4551670 : Nat := 779064830216770601297419

theorem tailTrace_4551670 : CollatzResearch.WordTrace tailWord_4551670 prefixEnd_4551670 779064830216770601297419 := by
  unfold tailWord_4551670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375815213755276762003279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110675362280056285461368309 10375815213755276762003279)
  ·
    refine ⟨15563722820632915143004919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10375815213755276762003279 15563722820632915143004919)
    ·
      refine ⟨23345584230949372714507379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15563722820632915143004919 23345584230949372714507379)
      ·
        refine ⟨35018376346424059071761069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23345584230949372714507379 35018376346424059071761069)
        ·
          refine ⟨13131891129909022151910401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35018376346424059071761069 13131891129909022151910401)
          ·
            refine ⟨9848918347431766613932801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13131891129909022151910401 9848918347431766613932801)
            ·
              refine ⟨7386688760573824960449601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9848918347431766613932801 7386688760573824960449601)
              ·
                refine ⟨5540016570430368720337201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7386688760573824960449601 5540016570430368720337201)
                ·
                  refine ⟨4155012427822776540252901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540016570430368720337201 4155012427822776540252901)
                  ·
                    refine ⟨779064830216770601297419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155012427822776540252901 779064830216770601297419)
                    ·
                      rfl

theorem cell23_4551670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4551670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551670 prefixEnd_4551670 := by exact prefixLift 4551670
  have htrace : WordTrace (prefixWord ++ tailWord_4551670) baseStart_4551670 baseEnd_4551670 := by
    simpa [prefixWord, tailWord_4551670, baseEnd_4551670] using wordTrace_append hprefix tailTrace_4551670
  have hstable : (prefixWord ++ tailWord_4551670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551670).length < 2 ^ (prefixWord ++ tailWord_4551670).sum := by decide
  have hdescent : baseEnd_4551670 < baseStart_4551670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551699 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_4551699 : Nat := 118140960795 + 4551699 * 2 ^ 59
def prefixEnd_4551699 : Nat := 4983230072969 + 3 ^ 40 * 4551699 * 2
def baseEnd_4551699 : Nat := 2337209381589292190429623

theorem tailTrace_4551699 : CollatzResearch.WordTrace tailWord_4551699 prefixEnd_4551699 2337209381589292190429623 := by
  unfold tailWord_4551699
  simp only [CollatzResearch.WordTrace]
  refine ⟨166014101136979366144858151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110676067424652910763238767 166014101136979366144858151)
  ·
    refine ⟨249021151705469049217287227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166014101136979366144858151 249021151705469049217287227)
    ·
      refine ⟨373531727558203573825930841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249021151705469049217287227 373531727558203573825930841)
      ·
        refine ⟨280148795668652680369448131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373531727558203573825930841 280148795668652680369448131)
        ·
          refine ⟨420223193502979020554172197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280148795668652680369448131 420223193502979020554172197)
          ·
            refine ⟨78791848781808566353907287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 420223193502979020554172197 78791848781808566353907287)
            ·
              refine ⟨118187773172712849530860931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78791848781808566353907287 118187773172712849530860931)
              ·
                refine ⟨177281659759069274296291397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118187773172712849530860931 177281659759069274296291397)
                ·
                  refine ⟨33240311204825488930554637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177281659759069274296291397 33240311204825488930554637)
                  ·
                    refine ⟨12465116701809558348957989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33240311204825488930554637 12465116701809558348957989)
                    ·
                      refine ⟨2337209381589292190429623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12465116701809558348957989 2337209381589292190429623)
                      ·
                        rfl

theorem cell23_4551699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_4551699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551699 prefixEnd_4551699 := by exact prefixLift 4551699
  have htrace : WordTrace (prefixWord ++ tailWord_4551699) baseStart_4551699 baseEnd_4551699 := by
    simpa [prefixWord, tailWord_4551699, baseEnd_4551699] using wordTrace_append hprefix tailTrace_4551699
  have hstable : (prefixWord ++ tailWord_4551699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551699).length < 2 ^ (prefixWord ++ tailWord_4551699).sum := by decide
  have hdescent : baseEnd_4551699 < baseStart_4551699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551726 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4551726 : Nat := 118140960795 + 4551726 * 2 ^ 59
def prefixEnd_4551726 : Nat := 4983230072969 + 3 ^ 40 * 4551726 * 2
def baseEnd_4551726 : Nat := 779074415188987861597333

theorem tailTrace_4551726 : CollatzResearch.WordTrace tailWord_4551726 prefixEnd_4551726 779074415188987861597333 := by
  unfold tailWord_4551726
  simp only [CollatzResearch.WordTrace]
  refine ⟨20751885738485193719511379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110676723938587699837394021 20751885738485193719511379)
  ·
    refine ⟨31127828607727790579267069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20751885738485193719511379 31127828607727790579267069)
    ·
      refine ⟨11672935727897921467225151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31127828607727790579267069 11672935727897921467225151)
      ·
        refine ⟨17509403591846882200837727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11672935727897921467225151 17509403591846882200837727)
        ·
          refine ⟨26264105387770323301256591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17509403591846882200837727 26264105387770323301256591)
          ·
            refine ⟨39396158081655484951884887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26264105387770323301256591 39396158081655484951884887)
            ·
              refine ⟨59094237122483227427827331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39396158081655484951884887 59094237122483227427827331)
              ·
                refine ⟨88641355683724841141740997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59094237122483227427827331 88641355683724841141740997)
                ·
                  refine ⟨16620254190698407714076437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88641355683724841141740997 16620254190698407714076437)
                  ·
                    refine ⟨779074415188987861597333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16620254190698407714076437 779074415188987861597333)
                    ·
                      rfl

theorem cell23_4551726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4551726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551726 prefixEnd_4551726 := by exact prefixLift 4551726
  have htrace : WordTrace (prefixWord ++ tailWord_4551726) baseStart_4551726 baseEnd_4551726 := by
    simpa [prefixWord, tailWord_4551726, baseEnd_4551726] using wordTrace_append hprefix tailTrace_4551726
  have hstable : (prefixWord ++ tailWord_4551726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551726).length < 2 ^ (prefixWord ++ tailWord_4551726).sum := by decide
  have hdescent : baseEnd_4551726 < baseStart_4551726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551801 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4551801 : Nat := 118140960795 + 4551801 * 2 ^ 59
def prefixEnd_4551801 : Nat := 4983230072969 + 3 ^ 40 * 4551801 * 2
def baseEnd_4551801 : Nat := 2337261756616050791354155

theorem tailTrace_4551801 : CollatzResearch.WordTrace tailWord_4551801 prefixEnd_4551801 2337261756616050791354155 := by
  unfold tailWord_4551801
  simp only [CollatzResearch.WordTrace]
  refine ⟨166017821382609837565071257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110678547588406558376714171 166017821382609837565071257)
  ·
    refine ⟨124513366036957378173803443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166017821382609837565071257 124513366036957378173803443)
    ·
      refine ⟨186770049055436067260705165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124513366036957378173803443 186770049055436067260705165)
      ·
        refine ⟨70038768395788525222764437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186770049055436067260705165 70038768395788525222764437)
        ·
          refine ⟨3283067268552587119817083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70038768395788525222764437 3283067268552587119817083)
          ·
            refine ⟨4924600902828880679725625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283067268552587119817083 4924600902828880679725625)
            ·
              refine ⟨3693450677121660509794219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924600902828880679725625 3693450677121660509794219)
              ·
                refine ⟨5540176015682490764691329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693450677121660509794219 5540176015682490764691329)
                ·
                  refine ⟨4155132011761868073518497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540176015682490764691329 4155132011761868073518497)
                  ·
                    refine ⟨3116349008821401055138873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155132011761868073518497 3116349008821401055138873)
                    ·
                      refine ⟨2337261756616050791354155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116349008821401055138873 2337261756616050791354155)
                      ·
                        rfl

theorem cell23_4551801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4551801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551801 prefixEnd_4551801 := by exact prefixLift 4551801
  have htrace : WordTrace (prefixWord ++ tailWord_4551801) baseStart_4551801 baseEnd_4551801 := by
    simpa [prefixWord, tailWord_4551801, baseEnd_4551801] using wordTrace_append hprefix tailTrace_4551801
  have hstable : (prefixWord ++ tailWord_4551801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551801).length < 2 ^ (prefixWord ++ tailWord_4551801).sum := by decide
  have hdescent : baseEnd_4551801 < baseStart_4551801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551890 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4551890 : Nat := 118140960795 + 4551890 * 2 ^ 59
def prefixEnd_4551890 : Nat := 4983230072969 + 3 ^ 40 * 4551890 * 2
def baseEnd_4551890 : Nat := 2337307456394300943141245

theorem tailTrace_4551890 : CollatzResearch.WordTrace tailWord_4551890 prefixEnd_4551890 2337307456394300943141245 := by
  unfold tailWord_4551890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505266869821851441265281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110680711652858270510040749 41505266869821851441265281)
  ·
    refine ⟨31128950152366388580948961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41505266869821851441265281 31128950152366388580948961)
    ·
      refine ⟨23346712614274791435711721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31128950152366388580948961 23346712614274791435711721)
      ·
        refine ⟨17510034460706093576783791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23346712614274791435711721 17510034460706093576783791)
        ·
          refine ⟨26265051691059140365175687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17510034460706093576783791 26265051691059140365175687)
          ·
            refine ⟨39397577536588710547763531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26265051691059140365175687 39397577536588710547763531)
            ·
              refine ⟨59096366304883065821645297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39397577536588710547763531 59096366304883065821645297)
              ·
                refine ⟨44322274728662299366233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59096366304883065821645297 44322274728662299366233973)
                ·
                  refine ⟨4155213255812090565584435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44322274728662299366233973 4155213255812090565584435)
                  ·
                    refine ⟨6232819883718135848376653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4155213255812090565584435 6232819883718135848376653)
                    ·
                      refine ⟨2337307456394300943141245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6232819883718135848376653 2337307456394300943141245)
                      ·
                        rfl

theorem cell23_4551890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4551890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551890 prefixEnd_4551890 := by exact prefixLift 4551890
  have htrace : WordTrace (prefixWord ++ tailWord_4551890) baseStart_4551890 baseEnd_4551890 := by
    simpa [prefixWord, tailWord_4551890, baseEnd_4551890] using wordTrace_append hprefix tailTrace_4551890
  have hstable : (prefixWord ++ tailWord_4551890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551890).length < 2 ^ (prefixWord ++ tailWord_4551890).sum := by decide
  have hdescent : baseEnd_4551890 < baseStart_4551890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551913 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 6, 2]
def baseStart_4551913 : Nat := 118140960795 + 4551913 * 2 ^ 59
def prefixEnd_4551913 : Nat := 4983230072969 + 3 ^ 40 * 4551913 * 2
def baseEnd_4551913 : Nat := 2337319266449354353153639

theorem tailTrace_4551913 : CollatzResearch.WordTrace tailWord_4551913 prefixEnd_4551913 2337319266449354353153639 := by
  unfold tailWord_4551913
  simp only [CollatzResearch.WordTrace]
  refine ⟨166021906358204080693148393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110681270905469387128765595 166021906358204080693148393)
  ·
    refine ⟨124516429768653060519861295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166021906358204080693148393 124516429768653060519861295)
    ·
      refine ⟨186774644652979590779791943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124516429768653060519861295 186774644652979590779791943)
      ·
        refine ⟨280161966979469386169687915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186774644652979590779791943 280161966979469386169687915)
        ·
          refine ⟨420242950469204079254531873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280161966979469386169687915 420242950469204079254531873)
          ·
            refine ⟨315182212851903059440898905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420242950469204079254531873 315182212851903059440898905)
            ·
              refine ⟨236386659638927294580674179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315182212851903059440898905 236386659638927294580674179)
              ·
                refine ⟨354579989458390941871011269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236386659638927294580674179 354579989458390941871011269)
                ·
                  refine ⟨66483748023448301600814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 354579989458390941871011269 66483748023448301600814613)
                  ·
                    refine ⟨3116425688599139137538185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66483748023448301600814613 3116425688599139137538185)
                    ·
                      refine ⟨2337319266449354353153639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116425688599139137538185 2337319266449354353153639)
                      ·
                        rfl

theorem cell23_4551913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6, 2].length) (baseStart_4551913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551913 prefixEnd_4551913 := by exact prefixLift 4551913
  have htrace : WordTrace (prefixWord ++ tailWord_4551913) baseStart_4551913 baseEnd_4551913 := by
    simpa [prefixWord, tailWord_4551913, baseEnd_4551913] using wordTrace_append hprefix tailTrace_4551913
  have hstable : (prefixWord ++ tailWord_4551913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551913).length < 2 ^ (prefixWord ++ tailWord_4551913).sum := by decide
  have hdescent : baseEnd_4551913 < baseStart_4551913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551923 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 6]
def baseStart_4551923 : Nat := 118140960795 + 4551923 * 2 ^ 59
def prefixEnd_4551923 : Nat := 4983230072969 + 3 ^ 40 * 4551923 * 2
def baseEnd_4551923 : Nat := 779108133751966438009531

theorem tailTrace_4551923 : CollatzResearch.WordTrace tailWord_4551923 prefixEnd_4551923 779108133751966438009531 := by
  unfold tailWord_4551923
  simp only [CollatzResearch.WordTrace]
  refine ⟨166022271088167852401012423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110681514058778568267341615 166022271088167852401012423)
  ·
    refine ⟨249033406632251778601518635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166022271088167852401012423 249033406632251778601518635)
    ·
      refine ⟨373550109948377667902277953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249033406632251778601518635 373550109948377667902277953)
      ·
        refine ⟨280162582461283250926708465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373550109948377667902277953 280162582461283250926708465)
        ·
          refine ⟨210121936845962438195031349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280162582461283250926708465 210121936845962438195031349)
          ·
            refine ⟨19698931579308978580784189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210121936845962438195031349 19698931579308978580784189)
            ·
              refine ⟨7387099342240866967794071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19698931579308978580784189 7387099342240866967794071)
              ·
                refine ⟨11080649013361300451691107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7387099342240866967794071 11080649013361300451691107)
                ·
                  refine ⟨16620973520041950677536661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11080649013361300451691107 16620973520041950677536661)
                  ·
                    refine ⟨779108133751966438009531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16620973520041950677536661 779108133751966438009531)
                    ·
                      rfl

theorem cell23_4551923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].length) (baseStart_4551923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551923 prefixEnd_4551923 := by exact prefixLift 4551923
  have htrace : WordTrace (prefixWord ++ tailWord_4551923) baseStart_4551923 baseEnd_4551923 := by
    simpa [prefixWord, tailWord_4551923, baseEnd_4551923] using wordTrace_append hprefix tailTrace_4551923
  have hstable : (prefixWord ++ tailWord_4551923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551923).length < 2 ^ (prefixWord ++ tailWord_4551923).sum := by decide
  have hdescent : baseEnd_4551923 < baseStart_4551923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551930 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_4551930 : Nat := 118140960795 + 4551930 * 2 ^ 59
def prefixEnd_4551930 : Nat := 4983230072969 + 3 ^ 40 * 4551930 * 2
def baseEnd_4551930 : Nat := 2337327995620480786641061

theorem tailTrace_4551930 : CollatzResearch.WordTrace tailWord_4551930 prefixEnd_4551930 2337327995620480786641061 := by
  unfold tailWord_4551930
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505631599785623149129311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110681684266094995064344829 41505631599785623149129311)
  ·
    refine ⟨62258447399678434723693967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41505631599785623149129311 62258447399678434723693967)
    ·
      refine ⟨93387671099517652085540951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62258447399678434723693967 93387671099517652085540951)
      ·
        refine ⟨140081506649276478128311427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93387671099517652085540951 140081506649276478128311427)
        ·
          refine ⟨210122259973914717192467141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140081506649276478128311427 210122259973914717192467141)
          ·
            refine ⟨39397923745109009473587589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210122259973914717192467141 39397923745109009473587589)
            ·
              refine ⟨7387110702207939276297673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39397923745109009473587589 7387110702207939276297673)
              ·
                refine ⟨5540333026655954457223255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7387110702207939276297673 5540333026655954457223255)
                ·
                  refine ⟨8310499539983931685834883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5540333026655954457223255 8310499539983931685834883)
                  ·
                    refine ⟨12465749309975897528752325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8310499539983931685834883 12465749309975897528752325)
                    ·
                      refine ⟨2337327995620480786641061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12465749309975897528752325 2337327995620480786641061)
                      ·
                        rfl

theorem cell23_4551930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_4551930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551930 prefixEnd_4551930 := by exact prefixLift 4551930
  have htrace : WordTrace (prefixWord ++ tailWord_4551930) baseStart_4551930 baseEnd_4551930 := by
    simpa [prefixWord, tailWord_4551930, baseEnd_4551930] using wordTrace_append hprefix tailTrace_4551930
  have hstable : (prefixWord ++ tailWord_4551930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551930).length < 2 ^ (prefixWord ++ tailWord_4551930).sum := by decide
  have hdescent : baseEnd_4551930 < baseStart_4551930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551940 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_4551940 : Nat := 118140960795 + 4551940 * 2 ^ 59
def prefixEnd_4551940 : Nat := 4983230072969 + 3 ^ 40 * 4551940 * 2
def baseEnd_4551940 : Nat := 779111043475675249172005

theorem tailTrace_4551940 : CollatzResearch.WordTrace tailWord_4551940 prefixEnd_4551940 779111043475675249172005 := by
  unfold tailWord_4551940
  simp only [CollatzResearch.WordTrace]
  refine ⟨83011445564553132152190637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110681927419404176202920849 83011445564553132152190637)
  ·
    refine ⟨31129292086707424557071489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83011445564553132152190637 31129292086707424557071489)
    ·
      refine ⟨23346969065030568417803617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31129292086707424557071489 23346969065030568417803617)
      ·
        refine ⟨17510226798772926313352713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23346969065030568417803617 17510226798772926313352713)
        ·
          refine ⟨13132670099079694735014535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17510226798772926313352713 13132670099079694735014535)
          ·
            refine ⟨19699005148619542102521803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13132670099079694735014535 19699005148619542102521803)
            ·
              refine ⟨29548507722929313153782705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19699005148619542102521803 29548507722929313153782705)
              ·
                refine ⟨22161380792196984865337029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29548507722929313153782705 22161380792196984865337029)
                ·
                  refine ⟨4155258898536934662250693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22161380792196984865337029 4155258898536934662250693)
                  ·
                    refine ⟨779111043475675249172005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155258898536934662250693 779111043475675249172005)
                    ·
                      rfl

theorem cell23_4551940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_4551940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551940 prefixEnd_4551940 := by exact prefixLift 4551940
  have htrace : WordTrace (prefixWord ++ tailWord_4551940) baseStart_4551940 baseEnd_4551940 := by
    simpa [prefixWord, tailWord_4551940, baseEnd_4551940] using wordTrace_append hprefix tailTrace_4551940
  have hstable : (prefixWord ++ tailWord_4551940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551940).length < 2 ^ (prefixWord ++ tailWord_4551940).sum := by decide
  have hdescent : baseEnd_4551940 < baseStart_4551940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551950 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4551950 : Nat := 118140960795 + 4551950 * 2 ^ 59
def prefixEnd_4551950 : Nat := 4983230072969 + 3 ^ 40 * 4551950 * 2
def baseEnd_4551950 : Nat := 2337338265233570708390969

theorem tailTrace_4551950 : CollatzResearch.WordTrace tailWord_4551950 prefixEnd_4551950 2337338265233570708390969 := by
  unfold tailWord_4551950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20752906982383754501530663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110682170572713357341496869 20752906982383754501530663)
  ·
    refine ⟨31129360473575631752295995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20752906982383754501530663 31129360473575631752295995)
    ·
      refine ⟨46694040710363447628443993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31129360473575631752295995 46694040710363447628443993)
      ·
        refine ⟨35020530532772585721332995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46694040710363447628443993 35020530532772585721332995)
        ·
          refine ⟨52530795799158878581999493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35020530532772585721332995 52530795799158878581999493)
          ·
            refine ⟨9849524212342289734124905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52530795799158878581999493 9849524212342289734124905)
            ·
              refine ⟨7387143159256717300593679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849524212342289734124905 7387143159256717300593679)
              ·
                refine ⟨11080714738885075950890519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7387143159256717300593679 11080714738885075950890519)
                ·
                  refine ⟨16621072108327613926335779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11080714738885075950890519 16621072108327613926335779)
                  ·
                    refine ⟨24931608162491420889503669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16621072108327613926335779 24931608162491420889503669)
                    ·
                      refine ⟨2337338265233570708390969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24931608162491420889503669 2337338265233570708390969)
                      ·
                        rfl

theorem cell23_4551950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4551950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551950 prefixEnd_4551950 := by exact prefixLift 4551950
  have htrace : WordTrace (prefixWord ++ tailWord_4551950) baseStart_4551950 baseEnd_4551950 := by
    simpa [prefixWord, tailWord_4551950, baseEnd_4551950] using wordTrace_append hprefix tailTrace_4551950
  have hstable : (prefixWord ++ tailWord_4551950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551950).length < 2 ^ (prefixWord ++ tailWord_4551950).sum := by decide
  have hdescent : baseEnd_4551950 < baseStart_4551950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551964 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4551964 : Nat := 118140960795 + 4551964 * 2 ^ 59
def prefixEnd_4551964 : Nat := 4983230072969 + 3 ^ 40 * 4551964 * 2
def baseEnd_4551964 : Nat := 2337345453962733653615905

theorem tailTrace_4551964 : CollatzResearch.WordTrace tailWord_4551964 prefixEnd_4551964 2337345453962733653615905 := by
  unfold tailWord_4551964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83011883240509658201627473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110682510987346210935503297 83011883240509658201627473)
  ·
    refine ⟨62258912430382243651220605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83011883240509658201627473 62258912430382243651220605)
    ·
      refine ⟨23347092161393341369207727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62258912430382243651220605 23347092161393341369207727)
      ·
        refine ⟨35020638242090012053811591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23347092161393341369207727 35020638242090012053811591)
        ·
          refine ⟨52530957363135018080717387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35020638242090012053811591 52530957363135018080717387)
          ·
            refine ⟨78796436044702527121076081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52530957363135018080717387 78796436044702527121076081)
            ·
              refine ⟨59097327033526895340807061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78796436044702527121076081 59097327033526895340807061)
              ·
                refine ⟨2770187204696573219100331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59097327033526895340807061 2770187204696573219100331)
                ·
                  refine ⟨4155280807044859828650497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770187204696573219100331 4155280807044859828650497)
                  ·
                    refine ⟨3116460605283644871487873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155280807044859828650497 3116460605283644871487873)
                    ·
                      refine ⟨2337345453962733653615905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116460605283644871487873 2337345453962733653615905)
                      ·
                        rfl

theorem cell23_4551964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4551964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551964 prefixEnd_4551964 := by exact prefixLift 4551964
  have htrace : WordTrace (prefixWord ++ tailWord_4551964) baseStart_4551964 baseEnd_4551964 := by
    simpa [prefixWord, tailWord_4551964, baseEnd_4551964] using wordTrace_append hprefix tailTrace_4551964
  have hstable : (prefixWord ++ tailWord_4551964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551964).length < 2 ^ (prefixWord ++ tailWord_4551964).sum := by decide
  have hdescent : baseEnd_4551964 < baseStart_4551964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4551970 : List Nat := [3, 3, 1, 1, 4, 1, 2, 8]
def baseStart_4551970 : Nat := 118140960795 + 4551970 * 2 ^ 59
def prefixEnd_4551970 : Nat := 4983230072969 + 3 ^ 40 * 4551970 * 2
def baseEnd_4551970 : Nat := 86568464253580023338551

theorem tailTrace_4551970 : CollatzResearch.WordTrace tailWord_4551970 prefixEnd_4551970 86568464253580023338551 := by
  unfold tailWord_4551970
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505996329749394856993341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110682656879331719618648909 41505996329749394856993341)
  ·
    refine ⟨15564748623656023071372503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41505996329749394856993341 15564748623656023071372503)
    ·
      refine ⟨23347122935484034607058755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15564748623656023071372503 23347122935484034607058755)
      ·
        refine ⟨35020684403226051910588133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23347122935484034607058755 35020684403226051910588133)
        ·
          refine ⟨6566378325604884733235275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35020684403226051910588133 6566378325604884733235275)
          ·
            refine ⟨9849567488407327099852913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566378325604884733235275 9849567488407327099852913)
            ·
              refine ⟨7387175616305495324889685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849567488407327099852913 7387175616305495324889685)
              ·
                refine ⟨86568464253580023338551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7387175616305495324889685 86568464253580023338551)
                ·
                  rfl

theorem cell23_4551970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_4551970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4551970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4551970 prefixEnd_4551970 := by exact prefixLift 4551970
  have htrace : WordTrace (prefixWord ++ tailWord_4551970) baseStart_4551970 baseEnd_4551970 := by
    simpa [prefixWord, tailWord_4551970, baseEnd_4551970] using wordTrace_append hprefix tailTrace_4551970
  have hstable : (prefixWord ++ tailWord_4551970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4551970).length < 2 ^ (prefixWord ++ tailWord_4551970).sum := by decide
  have hdescent : baseEnd_4551970 < baseStart_4551970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4551970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552037 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_4552037 : Nat := 118140960795 + 4552037 * 2 ^ 59
def prefixEnd_4552037 : Nat := 4983230072969 + 3 ^ 40 * 4552037 * 2
def baseEnd_4552037 : Nat := 2337382938050511868003069

theorem tailTrace_4552037 : CollatzResearch.WordTrace tailWord_4552037 prefixEnd_4552037 2337382938050511868003069 := by
  unfold tailWord_4552037
  simp only [CollatzResearch.WordTrace]
  refine ⟨166026429009754849870662365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110684286006503233247108243 166026429009754849870662365)
  ·
    refine ⟨62259910878658068701498387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166026429009754849870662365 62259910878658068701498387)
    ·
      refine ⟨93389866317987103052247581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62259910878658068701498387 93389866317987103052247581)
      ·
        refine ⟨35021199869245163644592843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93389866317987103052247581 35021199869245163644592843)
        ·
          refine ⟨52531799803867745466889265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35021199869245163644592843 52531799803867745466889265)
          ·
            refine ⟨39398849852900809100166949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52531799803867745466889265 39398849852900809100166949)
            ·
              refine ⟨7387284347418901706281303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39398849852900809100166949 7387284347418901706281303)
              ·
                refine ⟨11080926521128352559421955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7387284347418901706281303 11080926521128352559421955)
                ·
                  refine ⟨16621389781692528839132933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11080926521128352559421955 16621389781692528839132933)
                  ·
                    refine ⟨3116510584067349157337425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16621389781692528839132933 3116510584067349157337425)
                    ·
                      refine ⟨2337382938050511868003069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116510584067349157337425 2337382938050511868003069)
                      ·
                        rfl

theorem cell23_4552037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_4552037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552037 prefixEnd_4552037 := by exact prefixLift 4552037
  have htrace : WordTrace (prefixWord ++ tailWord_4552037) baseStart_4552037 baseEnd_4552037 := by
    simpa [prefixWord, tailWord_4552037, baseEnd_4552037] using wordTrace_append hprefix tailTrace_4552037
  have hstable : (prefixWord ++ tailWord_4552037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552037).length < 2 ^ (prefixWord ++ tailWord_4552037).sum := by decide
  have hdescent : baseEnd_4552037 < baseStart_4552037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552071 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_4552071 : Nat := 118140960795 + 4552071 * 2 ^ 59
def prefixEnd_4552071 : Nat := 4983230072969 + 3 ^ 40 * 4552071 * 2
def baseEnd_4552071 : Nat := 2337400396392764734977913

theorem tailTrace_4552071 : CollatzResearch.WordTrace tailWord_4552071 prefixEnd_4552071 2337400396392764734977913 := by
  unfold tailWord_4552071
  simp only [CollatzResearch.WordTrace]
  refine ⟨166027669091631673677400067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110685112727754449118266711 166027669091631673677400067)
  ·
    refine ⟨249041503637447510516100101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166027669091631673677400067 249041503637447510516100101)
    ·
      refine ⟨46695281932021408221768769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249041503637447510516100101 46695281932021408221768769)
      ·
        refine ⟨35021461449016056166326577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46695281932021408221768769 35021461449016056166326577)
        ·
          refine ⟨26266096086762042124744933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35021461449016056166326577 26266096086762042124744933)
          ·
            refine ⟨4924893016267882898389675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26266096086762042124744933 4924893016267882898389675)
            ·
              refine ⟨7387339524401824347584513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4924893016267882898389675 7387339524401824347584513)
              ·
                refine ⟨5540504643301368260688385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7387339524401824347584513 5540504643301368260688385)
                ·
                  refine ⟨4155378482476026195516289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540504643301368260688385 4155378482476026195516289)
                  ·
                    refine ⟨3116533861857019646637217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155378482476026195516289 3116533861857019646637217)
                    ·
                      refine ⟨2337400396392764734977913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116533861857019646637217 2337400396392764734977913)
                      ·
                        rfl

theorem cell23_4552071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_4552071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552071 prefixEnd_4552071 := by exact prefixLift 4552071
  have htrace : WordTrace (prefixWord ++ tailWord_4552071) baseStart_4552071 baseEnd_4552071 := by
    simpa [prefixWord, tailWord_4552071, baseEnd_4552071] using wordTrace_append hprefix tailTrace_4552071
  have hstable : (prefixWord ++ tailWord_4552071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552071).length < 2 ^ (prefixWord ++ tailWord_4552071).sum := by decide
  have hdescent : baseEnd_4552071 < baseStart_4552071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552088 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4552088 : Nat := 118140960795 + 4552088 * 2 ^ 59
def prefixEnd_4552088 : Nat := 4983230072969 + 3 ^ 40 * 4552088 * 2
def baseEnd_4552088 : Nat := 2337409125563891168465335

theorem tailTrace_4552088 : CollatzResearch.WordTrace tailWord_4552088 prefixEnd_4552088 2337409125563891168465335 := by
  unfold tailWord_4552088
  simp only [CollatzResearch.WordTrace]
  refine ⟨83014144566285042790384459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110685526088380057053845945 83014144566285042790384459)
  ·
    refine ⟨124521216849427564185576689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83014144566285042790384459 124521216849427564185576689)
    ·
      refine ⟨93390912637070673139182517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124521216849427564185576689 93390912637070673139182517)
      ·
        refine ⟨8755398059725375606798361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93390912637070673139182517 8755398059725375606798361)
        ·
          refine ⟨6566548544794031705098771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8755398059725375606798361 6566548544794031705098771)
          ·
            refine ⟨9849822817191047557648157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566548544794031705098771 9849822817191047557648157)
            ·
              refine ⟨3693683556446642834118059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9849822817191047557648157 3693683556446642834118059)
              ·
                refine ⟨5540525334669964251177089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693683556446642834118059 5540525334669964251177089)
                ·
                  refine ⟨4155394001002473188382817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540525334669964251177089 4155394001002473188382817)
                  ·
                    refine ⟨3116545500751854891287113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155394001002473188382817 3116545500751854891287113)
                    ·
                      refine ⟨2337409125563891168465335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116545500751854891287113 2337409125563891168465335)
                      ·
                        rfl

theorem cell23_4552088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4552088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552088 prefixEnd_4552088 := by exact prefixLift 4552088
  have htrace : WordTrace (prefixWord ++ tailWord_4552088) baseStart_4552088 baseEnd_4552088 := by
    simpa [prefixWord, tailWord_4552088, baseEnd_4552088] using wordTrace_append hprefix tailTrace_4552088
  have hstable : (prefixWord ++ tailWord_4552088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552088).length < 2 ^ (prefixWord ++ tailWord_4552088).sum := by decide
  have hdescent : baseEnd_4552088 < baseStart_4552088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552120 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_4552120 : Nat := 118140960795 + 4552120 * 2 ^ 59
def prefixEnd_4552120 : Nat := 4983230072969 + 3 ^ 40 * 4552120 * 2
def baseEnd_4552120 : Nat := 779141852314945014421729

theorem tailTrace_4552120 : CollatzResearch.WordTrace tailWord_4552120 prefixEnd_4552120 779141852314945014421729 := by
  unfold tailWord_4552120
  simp only [CollatzResearch.WordTrace]
  refine ⟨83014728134227077522966907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110686304178969436697289209 83014728134227077522966907)
  ·
    refine ⟨124522092201340616284450361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83014728134227077522966907 124522092201340616284450361)
    ·
      refine ⟨93391569151005462213337771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124522092201340616284450361 93391569151005462213337771)
      ·
        refine ⟨140087353726508193320006657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93391569151005462213337771 140087353726508193320006657)
        ·
          refine ⟨105065515294881144990004993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140087353726508193320006657 105065515294881144990004993)
          ·
            refine ⟨78799136471160858742503745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105065515294881144990004993 78799136471160858742503745)
            ·
              refine ⟨59099352353370644056877809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78799136471160858742503745 59099352353370644056877809)
              ·
                refine ⟨44324514265027983042658357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59099352353370644056877809 44324514265027983042658357)
                ·
                  refine ⟨4155423212346373410249221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44324514265027983042658357 4155423212346373410249221)
                  ·
                    refine ⟨779141852314945014421729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155423212346373410249221 779141852314945014421729)
                    ·
                      rfl

theorem cell23_4552120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_4552120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552120 prefixEnd_4552120 := by exact prefixLift 4552120
  have htrace : WordTrace (prefixWord ++ tailWord_4552120) baseStart_4552120 baseEnd_4552120 := by
    simpa [prefixWord, tailWord_4552120, baseEnd_4552120] using wordTrace_append hprefix tailTrace_4552120
  have hstable : (prefixWord ++ tailWord_4552120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552120).length < 2 ^ (prefixWord ++ tailWord_4552120).sum := by decide
  have hdescent : baseEnd_4552120 < baseStart_4552120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552222 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4552222 : Nat := 118140960795 + 4552222 * 2 ^ 59
def prefixEnd_4552222 : Nat := 4983230072969 + 3 ^ 40 * 4552222 * 2
def baseEnd_4552222 : Nat := 779159310657197881396573

theorem tailTrace_4552222 : CollatzResearch.WordTrace tailWord_4552222 prefixEnd_4552222 779159310657197881396573 := by
  unfold tailWord_4552222
  simp only [CollatzResearch.WordTrace]
  refine ⟨20754147064260578308268365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110688784342723084310764613 20754147064260578308268365)
  ·
    refine ⟨7782805149097716865600637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20754147064260578308268365 7782805149097716865600637)
    ·
      refine ⟨2918551930911643824600239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7782805149097716865600637 2918551930911643824600239)
      ·
        refine ⟨4377827896367465736900359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918551930911643824600239 4377827896367465736900359)
        ·
          refine ⟨6566741844551198605350539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377827896367465736900359 6566741844551198605350539)
          ·
            refine ⟨9850112766826797908025809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566741844551198605350539 9850112766826797908025809)
            ·
              refine ⟨7387584575120098431019357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9850112766826797908025809 7387584575120098431019357)
              ·
                refine ⟨2770344215670036911632259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7387584575120098431019357 2770344215670036911632259)
                ·
                  refine ⟨4155516323505055367448389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770344215670036911632259 4155516323505055367448389)
                  ·
                    refine ⟨779159310657197881396573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155516323505055367448389 779159310657197881396573)
                    ·
                      rfl

theorem cell23_4552222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4552222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552222 prefixEnd_4552222 := by exact prefixLift 4552222
  have htrace : WordTrace (prefixWord ++ tailWord_4552222) baseStart_4552222 baseEnd_4552222 := by
    simpa [prefixWord, tailWord_4552222, baseEnd_4552222] using wordTrace_append hprefix tailTrace_4552222
  have hstable : (prefixWord ++ tailWord_4552222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552222).length < 2 ^ (prefixWord ++ tailWord_4552222).sum := by decide
  have hdescent : baseEnd_4552222 < baseStart_4552222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552234 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4552234 : Nat := 118140960795 + 4552234 * 2 ^ 59
def prefixEnd_4552234 : Nat := 4983230072969 + 3 ^ 40 * 4552234 * 2
def baseEnd_4552234 : Nat := 2337484093739447597239663

theorem tailTrace_4552234 : CollatzResearch.WordTrace tailWord_4552234 prefixEnd_4552234 2337484093739447597239663 := by
  unfold tailWord_4552234
  simp only [CollatzResearch.WordTrace]
  refine ⟨41508403547510288128895939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110689076126694101677055837 41508403547510288128895939)
  ·
    refine ⟨62262605321265432193343909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41508403547510288128895939 62262605321265432193343909)
    ·
      refine ⟨11674238497737268536251983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62262605321265432193343909 11674238497737268536251983)
      ·
        refine ⟨17511357746605902804377975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11674238497737268536251983 17511357746605902804377975)
        ·
          refine ⟨26267036619908854206566963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17511357746605902804377975 26267036619908854206566963)
          ·
            refine ⟨39400554929863281309850445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26267036619908854206566963 39400554929863281309850445)
            ·
              refine ⟨14775208098698730491193917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39400554929863281309850445 14775208098698730491193917)
              ·
                refine ⟨5540703037012023934197719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14775208098698730491193917 5540703037012023934197719)
                ·
                  refine ⟨8311054555518035901296579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5540703037012023934197719 8311054555518035901296579)
                  ·
                    refine ⟨12466581833277053851944869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8311054555518035901296579 12466581833277053851944869)
                    ·
                      refine ⟨2337484093739447597239663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12466581833277053851944869 2337484093739447597239663)
                      ·
                        rfl

theorem cell23_4552234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4552234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552234 prefixEnd_4552234 := by exact prefixLift 4552234
  have htrace : WordTrace (prefixWord ++ tailWord_4552234) baseStart_4552234 baseEnd_4552234 := by
    simpa [prefixWord, tailWord_4552234, baseEnd_4552234] using wordTrace_append hprefix tailTrace_4552234
  have hstable : (prefixWord ++ tailWord_4552234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552234).length < 2 ^ (prefixWord ++ tailWord_4552234).sum := by decide
  have hdescent : baseEnd_4552234 < baseStart_4552234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552274 : List Nat := [3, 2, 2, 1, 2, 4, 2, 7]
def baseStart_4552274 : Nat := 118140960795 + 4552274 * 2 ^ 59
def prefixEnd_4552274 : Nat := 4983230072969 + 3 ^ 40 * 4552274 * 2
def baseEnd_4552274 : Nat := 86574245665393608916277

theorem tailTrace_4552274 : CollatzResearch.WordTrace tailWord_4552274 prefixEnd_4552274 86574245665393608916277 := by
  unfold tailWord_4552274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41508768277474059836759969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110690048739930826231359917 41508768277474059836759969)
  ·
    refine ⟨31131576208105544877569977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41508768277474059836759969 31131576208105544877569977)
    ·
      refine ⟨23348682156079158658177483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31131576208105544877569977 23348682156079158658177483)
      ·
        refine ⟨35023023234118737987266225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23348682156079158658177483 35023023234118737987266225)
        ·
          refine ⟨26267267425589053490449669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35023023234118737987266225 26267267425589053490449669)
          ·
            refine ⟨4925112642297947529459313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26267267425589053490449669 4925112642297947529459313)
            ·
              refine ⟨3693834481723460647094485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925112642297947529459313 3693834481723460647094485)
              ·
                refine ⟨86574245665393608916277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3693834481723460647094485 86574245665393608916277)
                ·
                  rfl

theorem cell23_4552274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_4552274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552274 prefixEnd_4552274 := by exact prefixLift 4552274
  have htrace : WordTrace (prefixWord ++ tailWord_4552274) baseStart_4552274 baseEnd_4552274 := by
    simpa [prefixWord, tailWord_4552274, baseEnd_4552274] using wordTrace_append hprefix tailTrace_4552274
  have hstable : (prefixWord ++ tailWord_4552274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552274).length < 2 ^ (prefixWord ++ tailWord_4552274).sum := by decide
  have hdescent : baseEnd_4552274 < baseStart_4552274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552302 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4552302 : Nat := 118140960795 + 4552302 * 2 ^ 59
def prefixEnd_4552302 : Nat := 4983230072969 + 3 ^ 40 * 4552302 * 2
def baseEnd_4552302 : Nat := 2337519010423953331189351

theorem tailTrace_4552302 : CollatzResearch.WordTrace tailWord_4552302 prefixEnd_4552302 2337519010423953331189351 := by
  unfold tailWord_4552302
  simp only [CollatzResearch.WordTrace]
  refine ⟨20754511794224350016132395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110690729569196533419372773 20754511794224350016132395)
  ·
    refine ⟨31131767691336525024198593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20754511794224350016132395 31131767691336525024198593)
    ·
      refine ⟨23348825768502393768148945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31131767691336525024198593 23348825768502393768148945)
      ·
        refine ⟨17511619326376795326111709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23348825768502393768148945 17511619326376795326111709)
        ·
          refine ⟨6566857247391298247291891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17511619326376795326111709 6566857247391298247291891)
          ·
            refine ⟨9850285871086947370937837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566857247391298247291891 9850285871086947370937837)
            ·
              refine ⟨3693857201657605264101689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9850285871086947370937837 3693857201657605264101689)
              ·
                refine ⟨2770392901243203948076267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693857201657605264101689 2770392901243203948076267)
                ·
                  refine ⟨4155589351864805922114401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770392901243203948076267 4155589351864805922114401)
                  ·
                    refine ⟨3116692013898604441585801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155589351864805922114401 3116692013898604441585801)
                    ·
                      refine ⟨2337519010423953331189351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116692013898604441585801 2337519010423953331189351)
                      ·
                        rfl

theorem cell23_4552302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4552302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552302 prefixEnd_4552302 := by exact prefixLift 4552302
  have htrace : WordTrace (prefixWord ++ tailWord_4552302) baseStart_4552302 baseEnd_4552302 := by
    simpa [prefixWord, tailWord_4552302, baseEnd_4552302] using wordTrace_append hprefix tailTrace_4552302
  have hstable : (prefixWord ++ tailWord_4552302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552302).length < 2 ^ (prefixWord ++ tailWord_4552302).sum := by decide
  have hdescent : baseEnd_4552302 < baseStart_4552302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552327 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4552327 : Nat := 118140960795 + 4552327 * 2 ^ 59
def prefixEnd_4552327 : Nat := 4983230072969 + 3 ^ 40 * 4552327 * 2
def baseEnd_4552327 : Nat := 2337531847440315733376735

theorem tailTrace_4552327 : CollatzResearch.WordTrace tailWord_4552327 prefixEnd_4552327 2337531847440315733376735 := by
  unfold tailWord_4552327
  simp only [CollatzResearch.WordTrace]
  refine ⟨166037006178704229398719235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110691337452469486265812823 166037006178704229398719235)
  ·
    refine ⟨249055509268056344098078853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166037006178704229398719235 249055509268056344098078853)
    ·
      refine ⟨46697907987760564518389785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249055509268056344098078853 46697907987760564518389785)
      ·
        refine ⟨35023430990820423388792339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46697907987760564518389785 35023430990820423388792339)
        ·
          refine ⟨52535146486230635083188509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35023430990820423388792339 52535146486230635083188509)
          ·
            refine ⟨19700679932336488156195691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52535146486230635083188509 19700679932336488156195691)
            ·
              refine ⟨29551019898504732234293537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19700679932336488156195691 29551019898504732234293537)
              ·
                refine ⟨22163264923878549175720153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29551019898504732234293537 22163264923878549175720153)
                ·
                  refine ⟨16622448692908911881790115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22163264923878549175720153 16622448692908911881790115)
                  ·
                    refine ⟨24933673039363367822685173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16622448692908911881790115 24933673039363367822685173)
                    ·
                      refine ⟨2337531847440315733376735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24933673039363367822685173 2337531847440315733376735)
                      ·
                        rfl

theorem cell23_4552327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4552327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552327 prefixEnd_4552327 := by exact prefixLift 4552327
  have htrace : WordTrace (prefixWord ++ tailWord_4552327) baseStart_4552327 baseEnd_4552327 := by
    simpa [prefixWord, tailWord_4552327, baseEnd_4552327] using wordTrace_append hprefix tailTrace_4552327
  have hstable : (prefixWord ++ tailWord_4552327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552327).length < 2 ^ (prefixWord ++ tailWord_4552327).sum := by decide
  have hdescent : baseEnd_4552327 < baseStart_4552327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552328 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4552328 : Nat := 118140960795 + 4552328 * 2 ^ 59
def prefixEnd_4552328 : Nat := 4983230072969 + 3 ^ 40 * 4552328 * 2
def baseEnd_4552328 : Nat := 2337532360920970229464231

theorem tailTrace_4552328 : CollatzResearch.WordTrace tailWord_4552328 prefixEnd_4552328 2337532360920970229464231 := by
  unfold tailWord_4552328
  simp only [CollatzResearch.WordTrace]
  refine ⟨83018521325850303284752819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110691361767800404379670425 83018521325850303284752819)
  ·
    refine ⟨124527781988775454927129229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83018521325850303284752819 124527781988775454927129229)
    ·
      refine ⟨46697918245790795597673461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124527781988775454927129229 46697918245790795597673461)
      ·
        refine ⟨4377929835542887087281887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46697918245790795597673461 4377929835542887087281887)
        ·
          refine ⟨6566894753314330630922831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377929835542887087281887 6566894753314330630922831)
          ·
            refine ⟨9850342129971495946384247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566894753314330630922831 9850342129971495946384247)
            ·
              refine ⟨14775513194957243919576371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850342129971495946384247 14775513194957243919576371)
              ·
                refine ⟨22163269792435865879364557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14775513194957243919576371 22163269792435865879364557)
                ·
                  refine ⟨8311226172163449704761709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22163269792435865879364557 8311226172163449704761709)
                  ·
                    refine ⟨3116709814561293639285641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8311226172163449704761709 3116709814561293639285641)
                    ·
                      refine ⟨2337532360920970229464231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116709814561293639285641 2337532360920970229464231)
                      ·
                        rfl

theorem cell23_4552328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4552328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552328 prefixEnd_4552328 := by exact prefixLift 4552328
  have htrace : WordTrace (prefixWord ++ tailWord_4552328) baseStart_4552328 baseEnd_4552328 := by
    simpa [prefixWord, tailWord_4552328, baseEnd_4552328] using wordTrace_append hprefix tailTrace_4552328
  have hstable : (prefixWord ++ tailWord_4552328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552328).length < 2 ^ (prefixWord ++ tailWord_4552328).sum := by decide
  have hdescent : baseEnd_4552328 < baseStart_4552328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552377 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_4552377 : Nat := 118140960795 + 4552377 * 2 ^ 59
def prefixEnd_4552377 : Nat := 4983230072969 + 3 ^ 40 * 4552377 * 2
def baseEnd_4552377 : Nat := 779185840491013512583835

theorem tailTrace_4552377 : CollatzResearch.WordTrace tailWord_4552377 prefixEnd_4552377 779185840491013512583835 := by
  unfold tailWord_4552377
  simp only [CollatzResearch.WordTrace]
  refine ⟨166038829828523087938039385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110692553219015391958692923 166038829828523087938039385)
  ·
    refine ⟨124529122371392315953529539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166038829828523087938039385 124529122371392315953529539)
    ·
      refine ⟨186793683557088473930294309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124529122371392315953529539 186793683557088473930294309)
      ·
        refine ⟨35023815666954088861930183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186793683557088473930294309 35023815666954088861930183)
        ·
          refine ⟨52535723500431133292895275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35023815666954088861930183 52535723500431133292895275)
          ·
            refine ⟨78803585250646699939342913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52535723500431133292895275 78803585250646699939342913)
            ·
              refine ⟨59102688937985024954507185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78803585250646699939342913 59102688937985024954507185)
              ·
                refine ⟨44327016703488768715880389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59102688937985024954507185 44327016703488768715880389)
                ·
                  refine ⟨8311315631904144134227573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44327016703488768715880389 8311315631904144134227573)
                  ·
                    refine ⟨779185840491013512583835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8311315631904144134227573 779185840491013512583835)
                    ·
                      rfl

theorem cell23_4552377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_4552377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552377 prefixEnd_4552377 := by exact prefixLift 4552377
  have htrace : WordTrace (prefixWord ++ tailWord_4552377) baseStart_4552377 baseEnd_4552377 := by
    simpa [prefixWord, tailWord_4552377, baseEnd_4552377] using wordTrace_append hprefix tailTrace_4552377
  have hstable : (prefixWord ++ tailWord_4552377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552377).length < 2 ^ (prefixWord ++ tailWord_4552377).sum := by decide
  have hdescent : baseEnd_4552377 < baseStart_4552377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552384 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2]
def baseStart_4552384 : Nat := 118140960795 + 4552384 * 2 ^ 59
def prefixEnd_4552384 : Nat := 4983230072969 + 3 ^ 40 * 4552384 * 2
def baseEnd_4552384 : Nat := 2337561115837622010363973

theorem tailTrace_4552384 : CollatzResearch.WordTrace tailWord_4552384 prefixEnd_4552384 2337561115837622010363973 := by
  unfold tailWord_4552384
  simp only [CollatzResearch.WordTrace]
  refine ⟨83019542569748864066772103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110692723426331818755696137 83019542569748864066772103)
  ·
    refine ⟨124529313854623296100158155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83019542569748864066772103 124529313854623296100158155)
    ·
      refine ⟨186793970781934944150237233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124529313854623296100158155 186793970781934944150237233)
      ·
        refine ⟨140095478086451208112677925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186793970781934944150237233 140095478086451208112677925)
        ·
          refine ⟨26267902141209601521127111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140095478086451208112677925 26267902141209601521127111)
          ·
            refine ⟨39401853211814402281690667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26267902141209601521127111 39401853211814402281690667)
            ·
              refine ⟨59102779817721603422536001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39401853211814402281690667 59102779817721603422536001)
              ·
                refine ⟨44327084863291202566902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59102779817721603422536001 44327084863291202566902001)
                ·
                  refine ⟨33245313647468401925176501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44327084863291202566902001 33245313647468401925176501)
                  ·
                    refine ⟨3116748154450162680485297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33245313647468401925176501 3116748154450162680485297)
                    ·
                      refine ⟨2337561115837622010363973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116748154450162680485297 2337561115837622010363973)
                      ·
                        rfl

theorem cell23_4552384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_4552384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552384 prefixEnd_4552384 := by exact prefixLift 4552384
  have htrace : WordTrace (prefixWord ++ tailWord_4552384) baseStart_4552384 baseEnd_4552384 := by
    simpa [prefixWord, tailWord_4552384, baseEnd_4552384] using wordTrace_append hprefix tailTrace_4552384
  have hstable : (prefixWord ++ tailWord_4552384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552384).length < 2 ^ (prefixWord ++ tailWord_4552384).sum := by decide
  have hdescent : baseEnd_4552384 < baseStart_4552384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552394 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_4552394 : Nat := 118140960795 + 4552394 * 2 ^ 59
def prefixEnd_4552394 : Nat := 4983230072969 + 3 ^ 40 * 4552394 * 2
def baseEnd_4552394 : Nat := 779188750214722323746309

theorem tailTrace_4552394 : CollatzResearch.WordTrace tailWord_4552394 prefixEnd_4552394 779188750214722323746309 := by
  unfold tailWord_4552394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41509862467365374960352059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110692966579640999894272157 41509862467365374960352059)
  ·
    refine ⟨62264793701048062440528089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41509862467365374960352059 62264793701048062440528089)
    ·
      refine ⟨46698595275786046830396067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62264793701048062440528089 46698595275786046830396067)
      ·
        refine ⟨70047892913679070245594101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46698595275786046830396067 70047892913679070245594101)
        ·
          refine ⟨6566989960657412835524447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70047892913679070245594101 6566989960657412835524447)
          ·
            refine ⟨9850484940986119253286671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566989960657412835524447 9850484940986119253286671)
            ·
              refine ⟨14775727411479178879930007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850484940986119253286671 14775727411479178879930007)
              ·
                refine ⟨22163591117218768319895011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14775727411479178879930007 22163591117218768319895011)
                ·
                  refine ⟨33245386675828152479842517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22163591117218768319895011 33245386675828152479842517)
                  ·
                    refine ⟨779188750214722323746309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33245386675828152479842517 779188750214722323746309)
                    ·
                      rfl

theorem cell23_4552394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_4552394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552394 prefixEnd_4552394 := by exact prefixLift 4552394
  have htrace : WordTrace (prefixWord ++ tailWord_4552394) baseStart_4552394 baseEnd_4552394 := by
    simpa [prefixWord, tailWord_4552394, baseEnd_4552394] using wordTrace_append hprefix tailTrace_4552394
  have hstable : (prefixWord ++ tailWord_4552394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552394).length < 2 ^ (prefixWord ++ tailWord_4552394).sum := by decide
  have hdescent : baseEnd_4552394 < baseStart_4552394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552434 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_4552434 : Nat := 118140960795 + 4552434 * 2 ^ 59
def prefixEnd_4552434 : Nat := 4983230072969 + 3 ^ 40 * 4552434 * 2
def baseEnd_4552434 : Nat := 2337586789870346814738743

theorem tailTrace_4552434 : CollatzResearch.WordTrace tailWord_4552434 prefixEnd_4552434 2337586789870346814738743 := by
  unfold tailWord_4552434
  simp only [CollatzResearch.WordTrace]
  refine ⟨41510227197329146668216089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110693939192877724448576237 41510227197329146668216089)
  ·
    refine ⟨31132670397996860001162067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41510227197329146668216089 31132670397996860001162067)
    ·
      refine ⟨46699005596995290001743101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31132670397996860001162067 46699005596995290001743101)
      ·
        refine ⟨17512127098873233750653663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46699005596995290001743101 17512127098873233750653663)
        ·
          refine ⟨26268190648309850625980495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17512127098873233750653663 26268190648309850625980495)
          ·
            refine ⟨39402285972464775938970743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26268190648309850625980495 39402285972464775938970743)
            ·
              refine ⟨59103428958697163908456115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39402285972464775938970743 59103428958697163908456115)
              ·
                refine ⟨88655143438045745862684173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59103428958697163908456115 88655143438045745862684173)
                ·
                  refine ⟨33245678789267154698506565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88655143438045745862684173 33245678789267154698506565)
                  ·
                    refine ⟨6233564772987591505969981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33245678789267154698506565 6233564772987591505969981)
                    ·
                      refine ⟨2337586789870346814738743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6233564772987591505969981 2337586789870346814738743)
                      ·
                        rfl

theorem cell23_4552434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_4552434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552434 prefixEnd_4552434 := by exact prefixLift 4552434
  have htrace : WordTrace (prefixWord ++ tailWord_4552434) baseStart_4552434 baseEnd_4552434 := by
    simpa [prefixWord, tailWord_4552434, baseEnd_4552434] using wordTrace_append hprefix tailTrace_4552434
  have hstable : (prefixWord ++ tailWord_4552434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552434).length < 2 ^ (prefixWord ++ tailWord_4552434).sum := by decide
  have hdescent : baseEnd_4552434 < baseStart_4552434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552458 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_4552458 : Nat := 118140960795 + 4552458 * 2 ^ 59
def prefixEnd_4552458 : Nat := 4983230072969 + 3 ^ 40 * 4552458 * 2
def baseEnd_4552458 : Nat := 779199704468684906946211

theorem tailTrace_4552458 : CollatzResearch.WordTrace tailWord_4552458 prefixEnd_4552458 779199704468684906946211 := by
  unfold tailWord_4552458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41510446035307409692934507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110694522760819759181158685 41510446035307409692934507)
  ·
    refine ⟨62265669052961114539401761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41510446035307409692934507 62265669052961114539401761)
    ·
      refine ⟨46699251789720835904551321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62265669052961114539401761 46699251789720835904551321)
      ·
        refine ⟨35024438842290626928413491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46699251789720835904551321 35024438842290626928413491)
        ·
          refine ⟨52536658263435940392620237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35024438842290626928413491 52536658263435940392620237)
          ·
            refine ⟨19701246848788477647232589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52536658263435940392620237 19701246848788477647232589)
            ·
              refine ⟨7387967568295679117712221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19701246848788477647232589 7387967568295679117712221)
              ·
                refine ⟨2770487838110879669142083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7387967568295679117712221 2770487838110879669142083)
                ·
                  refine ⟨4155731757166319503713125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770487838110879669142083 4155731757166319503713125)
                  ·
                    refine ⟨779199704468684906946211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155731757166319503713125 779199704468684906946211)
                    ·
                      rfl

theorem cell23_4552458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_4552458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552458 prefixEnd_4552458 := by exact prefixLift 4552458
  have htrace : WordTrace (prefixWord ++ tailWord_4552458) baseStart_4552458 baseEnd_4552458 := by
    simpa [prefixWord, tailWord_4552458, baseEnd_4552458] using wordTrace_append hprefix tailTrace_4552458
  have hstable : (prefixWord ++ tailWord_4552458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552458).length < 2 ^ (prefixWord ++ tailWord_4552458).sum := by decide
  have hdescent : baseEnd_4552458 < baseStart_4552458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552488 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 6]
def baseStart_4552488 : Nat := 118140960795 + 4552488 * 2 ^ 59
def prefixEnd_4552488 : Nat := 4983230072969 + 3 ^ 40 * 4552488 * 2
def baseEnd_4552488 : Nat := 259734946425076622607055

theorem tailTrace_4552488 : CollatzResearch.WordTrace tailWord_4552488 prefixEnd_4552488 259734946425076622607055 := by
  unfold tailWord_4552488
  simp only [CollatzResearch.WordTrace]
  refine ⟨83021439165560476947665059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110695252220747302596886745 83021439165560476947665059)
  ·
    refine ⟨124532158748340715421497589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83021439165560476947665059 124532158748340715421497589)
    ·
      refine ⟨11674889882656942070765399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124532158748340715421497589 11674889882656942070765399)
      ·
        refine ⟨17512334823985413106148099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11674889882656942070765399 17512334823985413106148099)
        ·
          refine ⟨26268502235978119659222149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17512334823985413106148099 26268502235978119659222149)
          ·
            refine ⟨4925344169245897436104153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26268502235978119659222149 4925344169245897436104153)
            ·
              refine ⟨3694008126934423077078115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925344169245897436104153 3694008126934423077078115)
              ·
                refine ⟨5541012190401634615617173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694008126934423077078115 5541012190401634615617173)
                ·
                  refine ⟨259734946425076622607055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5541012190401634615617173 259734946425076622607055)
                  ·
                    rfl

theorem cell23_4552488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_4552488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552488 prefixEnd_4552488 := by exact prefixLift 4552488
  have htrace : WordTrace (prefixWord ++ tailWord_4552488) baseStart_4552488 baseEnd_4552488 := by
    simpa [prefixWord, tailWord_4552488, baseEnd_4552488] using wordTrace_append hprefix tailTrace_4552488
  have hstable : (prefixWord ++ tailWord_4552488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552488).length < 2 ^ (prefixWord ++ tailWord_4552488).sum := by decide
  have hdescent : baseEnd_4552488 < baseStart_4552488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552501 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4552501 : Nat := 118140960795 + 4552501 * 2 ^ 59
def prefixEnd_4552501 : Nat := 4983230072969 + 3 ^ 40 * 4552501 * 2
def baseEnd_4552501 : Nat := 779207064358066017533645

theorem tailTrace_4552501 : CollatzResearch.WordTrace tailWord_4552501 prefixEnd_4552501 779207064358066017533645 := by
  unfold tailWord_4552501
  simp only [CollatzResearch.WordTrace]
  refine ⟨166043352480073857115553357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110695568320049238077035571 166043352480073857115553357)
  ·
    refine ⟨62266257180027696418332509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166043352480073857115553357 62266257180027696418332509)
    ·
      refine ⟨23349846442510386156874691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62266257180027696418332509 23349846442510386156874691)
      ·
        refine ⟨35024769663765579235312037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23349846442510386156874691 35024769663765579235312037)
        ·
          refine ⟨6567144311956046106621007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35024769663765579235312037 6567144311956046106621007)
          ·
            refine ⟨9850716467934069159931511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567144311956046106621007 9850716467934069159931511)
            ·
              refine ⟨14776074701901103739897267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9850716467934069159931511 14776074701901103739897267)
              ·
                refine ⟨22164112052851655609845901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776074701901103739897267 22164112052851655609845901)
                ·
                  refine ⟨8311542019819370853692213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22164112052851655609845901 8311542019819370853692213)
                  ·
                    refine ⟨779207064358066017533645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8311542019819370853692213 779207064358066017533645)
                    ·
                      rfl

theorem cell23_4552501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4552501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552501 prefixEnd_4552501 := by exact prefixLift 4552501
  have htrace : WordTrace (prefixWord ++ tailWord_4552501) baseStart_4552501 baseEnd_4552501 := by
    simpa [prefixWord, tailWord_4552501, baseEnd_4552501] using wordTrace_append hprefix tailTrace_4552501
  have hstable : (prefixWord ++ tailWord_4552501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552501).length < 2 ^ (prefixWord ++ tailWord_4552501).sum := by decide
  have hdescent : baseEnd_4552501 < baseStart_4552501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552525 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4552525 : Nat := 118140960795 + 4552525 * 2 ^ 59
def prefixEnd_4552525 : Nat := 4983230072969 + 3 ^ 40 * 4552525 * 2
def baseEnd_4552525 : Nat := 2337633516609905958700825

theorem tailTrace_4552525 : CollatzResearch.WordTrace tailWord_4552525 prefixEnd_4552525 2337633516609905958700825 := by
  unfold tailWord_4552525
  simp only [CollatzResearch.WordTrace]
  refine ⟨166044227831986909214427029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110696151887991272809618019 166044227831986909214427029)
  ·
    refine ⟨7783323179624386369426267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166044227831986909214427029 7783323179624386369426267)
    ·
      refine ⟨11674984769436579554139401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783323179624386369426267 11674984769436579554139401)
      ·
        refine ⟨8756238577077434665604551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11674984769436579554139401 8756238577077434665604551)
        ·
          refine ⟨13134357865616151998406827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756238577077434665604551 13134357865616151998406827)
          ·
            refine ⟨19701536798424227997610241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134357865616151998406827 19701536798424227997610241)
            ·
              refine ⟨14776152598818170998207681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701536798424227997610241 14776152598818170998207681)
              ·
                refine ⟨11082114449113628248655761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14776152598818170998207681 11082114449113628248655761)
                ·
                  refine ⟨8311585836835221186491821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11082114449113628248655761 8311585836835221186491821)
                  ·
                    refine ⟨3116844688813207944934433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8311585836835221186491821 3116844688813207944934433)
                    ·
                      refine ⟨2337633516609905958700825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116844688813207944934433 2337633516609905958700825)
                      ·
                        rfl

theorem cell23_4552525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4552525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552525 prefixEnd_4552525 := by exact prefixLift 4552525
  have htrace : WordTrace (prefixWord ++ tailWord_4552525) baseStart_4552525 baseEnd_4552525 := by
    simpa [prefixWord, tailWord_4552525, baseEnd_4552525] using wordTrace_append hprefix tailTrace_4552525
  have hstable : (prefixWord ++ tailWord_4552525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552525).length < 2 ^ (prefixWord ++ tailWord_4552525).sum := by decide
  have hdescent : baseEnd_4552525 < baseStart_4552525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552532 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_4552532 : Nat := 118140960795 + 4552532 * 2 ^ 59
def prefixEnd_4552532 : Nat := 4983230072969 + 3 ^ 40 * 4552532 * 2
def baseEnd_4552532 : Nat := 2337637110974487431313293

theorem tailTrace_4552532 : CollatzResearch.WordTrace tailWord_4552532 prefixEnd_4552532 2337637110974487431313293 := by
  unfold tailWord_4552532
  simp only [CollatzResearch.WordTrace]
  refine ⟨83022241571480774704965925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110696322095307699606621233 83022241571480774704965925)
  ·
    refine ⟨15566670294652645257181111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83022241571480774704965925 15566670294652645257181111)
    ·
      refine ⟨23350005441978967885771667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15566670294652645257181111 23350005441978967885771667)
      ·
        refine ⟨35025008162968451828657501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23350005441978967885771667 35025008162968451828657501)
        ·
          refine ⟨13134378061113169435746563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35025008162968451828657501 13134378061113169435746563)
          ·
            refine ⟨19701567091669754153619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134378061113169435746563 19701567091669754153619845)
            ·
              refine ⟨3694043829688078903803721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19701567091669754153619845 3694043829688078903803721)
              ·
                refine ⟨2770532872266059177852791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694043829688078903803721 2770532872266059177852791)
                ·
                  refine ⟨4155799308399088766779187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770532872266059177852791 4155799308399088766779187)
                  ·
                    refine ⟨6233698962598633150168781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4155799308399088766779187 6233698962598633150168781)
                    ·
                      refine ⟨2337637110974487431313293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6233698962598633150168781 2337637110974487431313293)
                      ·
                        rfl

theorem cell23_4552532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_4552532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552532 prefixEnd_4552532 := by exact prefixLift 4552532
  have htrace : WordTrace (prefixWord ++ tailWord_4552532) baseStart_4552532 baseEnd_4552532 := by
    simpa [prefixWord, tailWord_4552532, baseEnd_4552532] using wordTrace_append hprefix tailTrace_4552532
  have hstable : (prefixWord ++ tailWord_4552532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552532).length < 2 ^ (prefixWord ++ tailWord_4552532).sum := by decide
  have hdescent : baseEnd_4552532 < baseStart_4552532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552538 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_4552538 : Nat := 118140960795 + 4552538 * 2 ^ 59
def prefixEnd_4552538 : Nat := 4983230072969 + 3 ^ 40 * 4552538 * 2
def baseEnd_4552538 : Nat := 2337640191858414407838265

theorem tailTrace_4552538 : CollatzResearch.WordTrace tailWord_4552538 prefixEnd_4552538 2337640191858414407838265 := by
  unfold tailWord_4552538
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511175495234953108662567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110696467987293208289766845 41511175495234953108662567)
  ·
    refine ⟨62266763242852429662993851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41511175495234953108662567 62266763242852429662993851)
    ·
      refine ⟨93400144864278644494490777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62266763242852429662993851 93400144864278644494490777)
      ·
        refine ⟨70050108648208983370868083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93400144864278644494490777 70050108648208983370868083)
        ·
          refine ⟨105075162972313475056302125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70050108648208983370868083 105075162972313475056302125)
          ·
            refine ⟨39403186114617553146113297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105075162972313475056302125 39403186114617553146113297)
            ·
              refine ⟨29552389585963164859584973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39403186114617553146113297 29552389585963164859584973)
              ·
                refine ⟨11082146094736186822344365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29552389585963164859584973 11082146094736186822344365)
                ·
                  refine ⟨4155804785526070058379137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11082146094736186822344365 4155804785526070058379137)
                  ·
                    refine ⟨3116853589144552543784353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4155804785526070058379137 3116853589144552543784353)
                    ·
                      refine ⟨2337640191858414407838265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116853589144552543784353 2337640191858414407838265)
                      ·
                        rfl

theorem cell23_4552538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_4552538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552538 prefixEnd_4552538 := by exact prefixLift 4552538
  have htrace : WordTrace (prefixWord ++ tailWord_4552538) baseStart_4552538 baseEnd_4552538 := by
    simpa [prefixWord, tailWord_4552538, baseEnd_4552538] using wordTrace_append hprefix tailTrace_4552538
  have hstable : (prefixWord ++ tailWord_4552538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552538).length < 2 ^ (prefixWord ++ tailWord_4552538).sum := by decide
  have hdescent : baseEnd_4552538 < baseStart_4552538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552544 : List Nat := [2, 1, 1, 3, 3, 2, 3, 8]
def baseStart_4552544 : Nat := 118140960795 + 4552544 * 2 ^ 59
def prefixEnd_4552544 : Nat := 4983230072969 + 3 ^ 40 * 4552544 * 2
def baseEnd_4552544 : Nat := 86579380471938569791231

theorem tailTrace_4552544 : CollatzResearch.WordTrace tailWord_4552544 prefixEnd_4552544 86579380471938569791231 := by
  unfold tailWord_4552544
  simp only [CollatzResearch.WordTrace]
  refine ⟨83022460409459037729684343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110696613879278716972912457 83022460409459037729684343)
  ·
    refine ⟨124533690614188556594526515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83022460409459037729684343 124533690614188556594526515)
    ·
      refine ⟨186800535921282834891789773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124533690614188556594526515 186800535921282834891789773)
      ·
        refine ⟨70050200970481063084421165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186800535921282834891789773 70050200970481063084421165)
        ·
          refine ⟨26268825363930398656657937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70050200970481063084421165 26268825363930398656657937)
          ·
            refine ⟨19701619022947798992493453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26268825363930398656657937 19701619022947798992493453)
            ·
              refine ⟨7388107133605424622185045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19701619022947798992493453 7388107133605424622185045)
              ·
                refine ⟨86579380471938569791231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7388107133605424622185045 86579380471938569791231)
                ·
                  rfl

theorem cell23_4552544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_4552544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552544 prefixEnd_4552544 := by exact prefixLift 4552544
  have htrace : WordTrace (prefixWord ++ tailWord_4552544) baseStart_4552544 baseEnd_4552544 := by
    simpa [prefixWord, tailWord_4552544, baseEnd_4552544] using wordTrace_append hprefix tailTrace_4552544
  have hstable : (prefixWord ++ tailWord_4552544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552544).length < 2 ^ (prefixWord ++ tailWord_4552544).sum := by decide
  have hdescent : baseEnd_4552544 < baseStart_4552544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552551 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_4552551 : Nat := 118140960795 + 4552551 * 2 ^ 59
def prefixEnd_4552551 : Nat := 4983230072969 + 3 ^ 40 * 4552551 * 2
def baseEnd_4552551 : Nat := 2337646867106922856975705

theorem tailTrace_4552551 : CollatzResearch.WordTrace tailWord_4552551 prefixEnd_4552551 2337646867106922856975705 := by
  unfold tailWord_4552551
  simp only [CollatzResearch.WordTrace]
  refine ⟨166045176129892715654873507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110696784086595143769915671 166045176129892715654873507)
  ·
    refine ⟨249067764194839073482310261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166045176129892715654873507 249067764194839073482310261)
    ·
      refine ⟨23350102893266163138966587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 249067764194839073482310261 23350102893266163138966587)
      ·
        refine ⟨35025154339899244708449881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23350102893266163138966587 35025154339899244708449881)
        ·
          refine ⟨26268865754924433531337411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35025154339899244708449881 26268865754924433531337411)
          ·
            refine ⟨39403298632386650297006117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26268865754924433531337411 39403298632386650297006117)
            ·
              refine ⟨7388118493572496930688647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39403298632386650297006117 7388118493572496930688647)
              ·
                refine ⟨11082177740358745396032971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388118493572496930688647 11082177740358745396032971)
                ·
                  refine ⟨16623266610538118094049457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082177740358745396032971 16623266610538118094049457)
                  ·
                    refine ⟨12467449957903588570537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16623266610538118094049457 12467449957903588570537093)
                    ·
                      refine ⟨2337646867106922856975705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12467449957903588570537093 2337646867106922856975705)
                      ·
                        rfl

theorem cell23_4552551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_4552551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552551 prefixEnd_4552551 := by exact prefixLift 4552551
  have htrace : WordTrace (prefixWord ++ tailWord_4552551) baseStart_4552551 baseEnd_4552551 := by
    simpa [prefixWord, tailWord_4552551, baseEnd_4552551] using wordTrace_append hprefix tailTrace_4552551
  have hstable : (prefixWord ++ tailWord_4552551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552551).length < 2 ^ (prefixWord ++ tailWord_4552551).sum := by decide
  have hdescent : baseEnd_4552551 < baseStart_4552551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552558 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4552558 : Nat := 118140960795 + 4552558 * 2 ^ 59
def prefixEnd_4552558 : Nat := 4983230072969 + 3 ^ 40 * 4552558 * 2
def baseEnd_4552558 : Nat := 2337650461471504329588173

theorem tailTrace_4552558 : CollatzResearch.WordTrace tailWord_4552558 prefixEnd_4552558 2337650461471504329588173 := by
  unfold tailWord_4552558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20755678930108419481297291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110696954293911570566918885 20755678930108419481297291)
  ·
    refine ⟨31133518395162629221945937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20755678930108419481297291 31133518395162629221945937)
    ·
      refine ⟨23350138796371971916459453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31133518395162629221945937 23350138796371971916459453)
      ·
        refine ⟨8756302048639489468672295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23350138796371971916459453 8756302048639489468672295)
        ·
          refine ⟨13134453072959234203008443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756302048639489468672295 13134453072959234203008443)
          ·
            refine ⟨19701679609438851304512665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134453072959234203008443 19701679609438851304512665)
            ·
              refine ⟨14776259707079138478384499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701679609438851304512665 14776259707079138478384499)
              ·
                refine ⟨22164389560618707717576749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776259707079138478384499 22164389560618707717576749)
                ·
                  refine ⟨8311646085232015394091281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22164389560618707717576749 8311646085232015394091281)
                  ·
                    refine ⟨6233734563924011545568461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8311646085232015394091281 6233734563924011545568461)
                    ·
                      refine ⟨2337650461471504329588173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6233734563924011545568461 2337650461471504329588173)
                      ·
                        rfl

theorem cell23_4552558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4552558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552558 prefixEnd_4552558 := by exact prefixLift 4552558
  have htrace : WordTrace (prefixWord ++ tailWord_4552558) baseStart_4552558 baseEnd_4552558 := by
    simpa [prefixWord, tailWord_4552558, baseEnd_4552558] using wordTrace_append hprefix tailTrace_4552558
  have hstable : (prefixWord ++ tailWord_4552558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552558).length < 2 ^ (prefixWord ++ tailWord_4552558).sum := by decide
  have hdescent : baseEnd_4552558 < baseStart_4552558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552571 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 3]
def baseStart_4552571 : Nat := 118140960795 + 4552571 * 2 ^ 59
def prefixEnd_4552571 : Nat := 4983230072969 + 3 ^ 40 * 4552571 * 2
def baseEnd_4552571 : Nat := 2337657136720012778725613

theorem tailTrace_4552571 : CollatzResearch.WordTrace tailWord_4552571 prefixEnd_4552571 2337657136720012778725613 := by
  unfold tailWord_4552571
  simp only [CollatzResearch.WordTrace]
  refine ⟨166045905589820259070601567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110697270393213506047067711 166045905589820259070601567)
  ·
    refine ⟨249068858384730388605902351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166045905589820259070601567 249068858384730388605902351)
    ·
      refine ⟨373603287577095582908853527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249068858384730388605902351 373603287577095582908853527)
      ·
        refine ⟨560404931365643374363280291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373603287577095582908853527 560404931365643374363280291)
        ·
          refine ⟨840607397048465061544920437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560404931365643374363280291 840607397048465061544920437)
          ·
            refine ⟨78806943473293599519836291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 840607397048465061544920437 78806943473293599519836291)
            ·
              refine ⟨118210415209940399279754437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78806943473293599519836291 118210415209940399279754437)
              ·
                refine ⟨22164452851863824864953957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118210415209940399279754437 22164452851863824864953957)
                ·
                  refine ⟨4155834909724467162178867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22164452851863824864953957 4155834909724467162178867)
                  ·
                    refine ⟨6233752364586700743268301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4155834909724467162178867 6233752364586700743268301)
                    ·
                      refine ⟨2337657136720012778725613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6233752364586700743268301 2337657136720012778725613)
                      ·
                        rfl

theorem cell23_4552571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 3].length) (baseStart_4552571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552571 prefixEnd_4552571 := by exact prefixLift 4552571
  have htrace : WordTrace (prefixWord ++ tailWord_4552571) baseStart_4552571 baseEnd_4552571 := by
    simpa [prefixWord, tailWord_4552571, baseEnd_4552571] using wordTrace_append hprefix tailTrace_4552571
  have hstable : (prefixWord ++ tailWord_4552571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552571).length < 2 ^ (prefixWord ++ tailWord_4552571).sum := by decide
  have hdescent : baseEnd_4552571 < baseStart_4552571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552615 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4552615 : Nat := 118140960795 + 4552615 * 2 ^ 59
def prefixEnd_4552615 : Nat := 4983230072969 + 3 ^ 40 * 4552615 * 2
def baseEnd_4552615 : Nat := 2337679729868810606575411

theorem tailTrace_4552615 : CollatzResearch.WordTrace tailWord_4552615 prefixEnd_4552615 2337679729868810606575411 := by
  unfold tailWord_4552615
  simp only [CollatzResearch.WordTrace]
  refine ⟨166047510401660854585203299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110698340267773903056802199 166047510401660854585203299)
  ·
    refine ⟨249071265602491281877804949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166047510401660854585203299 249071265602491281877804949)
    ·
      refine ⟨11675215575116778838022107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 249071265602491281877804949 11675215575116778838022107)
      ·
        refine ⟨17512823362675168257033161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675215575116778838022107 17512823362675168257033161)
        ·
          refine ⟨13134617522006376192774871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17512823362675168257033161 13134617522006376192774871)
          ·
            refine ⟨19701926283009564289162307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134617522006376192774871 19701926283009564289162307)
            ·
              refine ⟨29552889424514346433743461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19701926283009564289162307 29552889424514346433743461)
              ·
                refine ⟨5541166767096439956326899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29552889424514346433743461 5541166767096439956326899)
                ·
                  refine ⟨8311750150644659934490349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541166767096439956326899 8311750150644659934490349)
                  ·
                    refine ⟨3116906306491747475433881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8311750150644659934490349 3116906306491747475433881)
                    ·
                      refine ⟨2337679729868810606575411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3116906306491747475433881 2337679729868810606575411)
                      ·
                        rfl

theorem cell23_4552615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4552615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552615 prefixEnd_4552615 := by exact prefixLift 4552615
  have htrace : WordTrace (prefixWord ++ tailWord_4552615) baseStart_4552615 baseEnd_4552615 := by
    simpa [prefixWord, tailWord_4552615, baseEnd_4552615] using wordTrace_append hprefix tailTrace_4552615
  have hstable : (prefixWord ++ tailWord_4552615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552615).length < 2 ^ (prefixWord ++ tailWord_4552615).sum := by decide
  have hdescent : baseEnd_4552615 < baseStart_4552615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552702 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4552702 : Nat := 118140960795 + 4552702 * 2 ^ 59
def prefixEnd_4552702 : Nat := 4983230072969 + 3 ^ 40 * 4552702 * 2
def baseEnd_4552702 : Nat := 259747155853972418465279

theorem tailTrace_4552702 : CollatzResearch.WordTrace tailWord_4552702 prefixEnd_4552702 259747155853972418465279 := by
  unfold tailWord_4552702
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756335444043208555452545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110700455701563778962413573 20756335444043208555452545)
  ·
    refine ⟨15567251583032406416589409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20756335444043208555452545 15567251583032406416589409)
    ·
      refine ⟨11675438687274304812442057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15567251583032406416589409 11675438687274304812442057)
      ·
        refine ⟨8756579015455728609331543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11675438687274304812442057 8756579015455728609331543)
        ·
          refine ⟨13134868523183592913997315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756579015455728609331543 13134868523183592913997315)
          ·
            refine ⟨19702302784775389370995973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134868523183592913997315 19702302784775389370995973)
            ·
              refine ⟨3694181772145385507061745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19702302784775389370995973 3694181772145385507061745)
              ·
                refine ⟨2770636329109039130296309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694181772145385507061745 2770636329109039130296309)
                ·
                  refine ⟨259747155853972418465279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2770636329109039130296309 259747155853972418465279)
                  ·
                    rfl

theorem cell23_4552702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4552702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552702 prefixEnd_4552702 := by exact prefixLift 4552702
  have htrace : WordTrace (prefixWord ++ tailWord_4552702) baseStart_4552702 baseEnd_4552702 := by
    simpa [prefixWord, tailWord_4552702, baseEnd_4552702] using wordTrace_append hprefix tailTrace_4552702
  have hstable : (prefixWord ++ tailWord_4552702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552702).length < 2 ^ (prefixWord ++ tailWord_4552702).sum := by decide
  have hdescent : baseEnd_4552702 < baseStart_4552702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552728 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_4552728 : Nat := 118140960795 + 4552728 * 2 ^ 59
def prefixEnd_4552728 : Nat := 4983230072969 + 3 ^ 40 * 4552728 * 2
def baseEnd_4552728 : Nat := 779245917727589554820797

theorem tailTrace_4552728 : CollatzResearch.WordTrace tailWord_4552728 prefixEnd_4552728 779245917727589554820797 := by
  unfold tailWord_4552728
  simp only [CollatzResearch.WordTrace]
  refine ⟨83025815925125737442033419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110701087900167649922711225 83025815925125737442033419)
  ·
    refine ⟨124538723887688606163050129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83025815925125737442033419 124538723887688606163050129)
    ·
      refine ⟨93404042915766454622287597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124538723887688606163050129 93404042915766454622287597)
      ·
        refine ⟨35026516093412420483357849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93404042915766454622287597 35026516093412420483357849)
        ·
          refine ⟨26269887070059315362518387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35026516093412420483357849 26269887070059315362518387)
          ·
            refine ⟨39404830605088973043777581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26269887070059315362518387 39404830605088973043777581)
            ·
              refine ⟨14776811476908364891416593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39404830605088973043777581 14776811476908364891416593)
              ·
                refine ⟨11082608607681273668562445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14776811476908364891416593 11082608607681273668562445)
                ·
                  refine ⟨4155978227880477625710917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11082608607681273668562445 4155978227880477625710917)
                  ·
                    refine ⟨779245917727589554820797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155978227880477625710917 779245917727589554820797)
                    ·
                      rfl

theorem cell23_4552728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_4552728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552728 prefixEnd_4552728 := by exact prefixLift 4552728
  have htrace : WordTrace (prefixWord ++ tailWord_4552728) baseStart_4552728 baseEnd_4552728 := by
    simpa [prefixWord, tailWord_4552728, baseEnd_4552728] using wordTrace_append hprefix tailTrace_4552728
  have hstable : (prefixWord ++ tailWord_4552728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552728).length < 2 ^ (prefixWord ++ tailWord_4552728).sum := by decide
  have hdescent : baseEnd_4552728 < baseStart_4552728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552738 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_4552738 : Nat := 118140960795 + 4552738 * 2 ^ 59
def prefixEnd_4552738 : Nat := 4983230072969 + 3 ^ 40 * 4552738 * 2
def baseEnd_4552738 : Nat := 2337742887989313625337345

theorem tailTrace_4552738 : CollatzResearch.WordTrace tailWord_4552738 prefixEnd_4552738 2337742887989313625337345 := by
  unfold tailWord_4552738
  simp only [CollatzResearch.WordTrace]
  refine ⟨41512999145053811647982717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110701331053476831061287245 41512999145053811647982717)
  ·
    refine ⟨15567374679395179367993519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41512999145053811647982717 15567374679395179367993519)
    ·
      refine ⟨23351062019092769051990279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15567374679395179367993519 23351062019092769051990279)
      ·
        refine ⟨35026593028639153577985419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23351062019092769051990279 35026593028639153577985419)
        ·
          refine ⟨52539889542958730366978129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35026593028639153577985419 52539889542958730366978129)
          ·
            refine ⟨39404917157219047775233597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52539889542958730366978129 39404917157219047775233597)
            ·
              refine ⟨14776843933957142915712599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39404917157219047775233597 14776843933957142915712599)
              ·
                refine ⟨22165265900935714373568899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776843933957142915712599 22165265900935714373568899)
                ·
                  refine ⟨33247898851403571560353349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22165265900935714373568899 33247898851403571560353349)
                  ·
                    refine ⟨6233981034638169667566253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33247898851403571560353349 6233981034638169667566253)
                    ·
                      refine ⟨2337742887989313625337345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6233981034638169667566253 2337742887989313625337345)
                      ·
                        rfl

theorem cell23_4552738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_4552738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552738 prefixEnd_4552738 := by exact prefixLift 4552738
  have htrace : WordTrace (prefixWord ++ tailWord_4552738) baseStart_4552738 baseEnd_4552738 := by
    simpa [prefixWord, tailWord_4552738, baseEnd_4552738] using wordTrace_append hprefix tailTrace_4552738
  have hstable : (prefixWord ++ tailWord_4552738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552738).length < 2 ^ (prefixWord ++ tailWord_4552738).sum := by decide
  have hdescent : baseEnd_4552738 < baseStart_4552738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552758 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_4552758 : Nat := 118140960795 + 4552758 * 2 ^ 59
def prefixEnd_4552758 : Nat := 4983230072969 + 3 ^ 40 * 4552758 * 2
def baseEnd_4552758 : Nat := 259750350844711505231917

theorem tailTrace_4552758 : CollatzResearch.WordTrace tailWord_4552758 prefixEnd_4552758 259750350844711505231917 := by
  unfold tailWord_4552758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378295377508924375478683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110701817360095193338439285 10378295377508924375478683)
  ·
    refine ⟨15567443066263386563218025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10378295377508924375478683 15567443066263386563218025)
    ·
      refine ⟨11675582299697539922413519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15567443066263386563218025 11675582299697539922413519)
      ·
        refine ⟨17513373449546309883620279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675582299697539922413519 17513373449546309883620279)
        ·
          refine ⟨26270060174319464825430419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17513373449546309883620279 26270060174319464825430419)
          ·
            refine ⟨39405090261479197238145629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26270060174319464825430419 39405090261479197238145629)
            ·
              refine ⟨14776908848054698964304611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39405090261479197238145629 14776908848054698964304611)
              ·
                refine ⟨22165363272082048446456917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776908848054698964304611 22165363272082048446456917)
                ·
                  refine ⟨259750350844711505231917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22165363272082048446456917 259750350844711505231917)
                  ·
                    rfl

theorem cell23_4552758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_4552758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552758 prefixEnd_4552758 := by exact prefixLift 4552758
  have htrace : WordTrace (prefixWord ++ tailWord_4552758) baseStart_4552758 baseEnd_4552758 := by
    simpa [prefixWord, tailWord_4552758, baseEnd_4552758] using wordTrace_append hprefix tailTrace_4552758
  have hstable : (prefixWord ++ tailWord_4552758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552758).length < 2 ^ (prefixWord ++ tailWord_4552758).sum := by decide
  have hdescent : baseEnd_4552758 < baseStart_4552758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552771 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 3, 5]
def baseStart_4552771 : Nat := 118140960795 + 4552771 * 2 ^ 59
def prefixEnd_4552771 : Nat := 4983230072969 + 3 ^ 40 * 4552771 * 2
def baseEnd_4552771 : Nat := 779253277616970665408231

theorem tailTrace_4552771 : CollatzResearch.WordTrace tailWord_4552771 prefixEnd_4552771 779253277616970665408231 := by
  unfold tailWord_4552771
  simp only [CollatzResearch.WordTrace]
  refine ⟨166053200189095693227882167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110702133459397128818588111 166053200189095693227882167)
  ·
    refine ⟨249079800283643539841823251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166053200189095693227882167 249079800283643539841823251)
    ·
      refine ⟨373619700425465309762734877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249079800283643539841823251 373619700425465309762734877)
      ·
        refine ⟨140107387659549491161025579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373619700425465309762734877 140107387659549491161025579)
        ·
          refine ⟨210161081489324236741538369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140107387659549491161025579 210161081489324236741538369)
          ·
            refine ⟨157620811116993177556153777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210161081489324236741538369 157620811116993177556153777)
            ·
              refine ⟨118215608337744883167115333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157620811116993177556153777 118215608337744883167115333)
              ·
                refine ⟨22165426563327165593834125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118215608337744883167115333 22165426563327165593834125)
                ·
                  refine ⟨8312034961247687097687797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22165426563327165593834125 8312034961247687097687797)
                  ·
                    refine ⟨779253277616970665408231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8312034961247687097687797 779253277616970665408231)
                    ·
                      rfl

theorem cell23_4552771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].length) (baseStart_4552771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552771 prefixEnd_4552771 := by exact prefixLift 4552771
  have htrace : WordTrace (prefixWord ++ tailWord_4552771) baseStart_4552771 baseEnd_4552771 := by
    simpa [prefixWord, tailWord_4552771, baseEnd_4552771] using wordTrace_append hprefix tailTrace_4552771
  have hstable : (prefixWord ++ tailWord_4552771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552771).length < 2 ^ (prefixWord ++ tailWord_4552771).sum := by decide
  have hdescent : baseEnd_4552771 < baseStart_4552771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552801 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_4552801 : Nat := 118140960795 + 4552801 * 2 ^ 59
def prefixEnd_4552801 : Nat := 4983230072969 + 3 ^ 40 * 4552801 * 2
def baseEnd_4552801 : Nat := 779258412423515626283185

theorem tailTrace_4552801 : CollatzResearch.WordTrace tailWord_4552801 prefixEnd_4552801 779258412423515626283185 := by
  unfold tailWord_4552801
  simp only [CollatzResearch.WordTrace]
  refine ⟨166054294378987008351474257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110702862919324672234316171 166054294378987008351474257)
  ·
    refine ⟨124540720784240256263605693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166054294378987008351474257 124540720784240256263605693)
    ·
      refine ⟨46702770294090096098852135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124540720784240256263605693 46702770294090096098852135)
      ·
        refine ⟨70054155441135144148278203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46702770294090096098852135 70054155441135144148278203)
        ·
          refine ⟨105081233161702716222417305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70054155441135144148278203 105081233161702716222417305)
          ·
            refine ⟨78810924871277037166812979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105081233161702716222417305 78810924871277037166812979)
            ·
              refine ⟨118216387306915555750219469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78810924871277037166812979 118216387306915555750219469)
              ·
                refine ⟨44331145240093333406332301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118216387306915555750219469 44331145240093333406332301)
                ·
                  refine ⟨16624179465035000027374613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44331145240093333406332301 16624179465035000027374613)
                  ·
                    refine ⟨779258412423515626283185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16624179465035000027374613 779258412423515626283185)
                    ·
                      rfl

theorem cell23_4552801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_4552801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552801 prefixEnd_4552801 := by exact prefixLift 4552801
  have htrace : WordTrace (prefixWord ++ tailWord_4552801) baseStart_4552801 baseEnd_4552801 := by
    simpa [prefixWord, tailWord_4552801, baseEnd_4552801] using wordTrace_append hprefix tailTrace_4552801
  have hstable : (prefixWord ++ tailWord_4552801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552801).length < 2 ^ (prefixWord ++ tailWord_4552801).sum := by decide
  have hdescent : baseEnd_4552801 < baseStart_4552801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552828 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_4552828 : Nat := 118140960795 + 4552828 * 2 ^ 59
def prefixEnd_4552828 : Nat := 4983230072969 + 3 ^ 40 * 4552828 * 2
def baseEnd_4552828 : Nat := 2337789101248218273211931

theorem tailTrace_4552828 : CollatzResearch.WordTrace tailWord_4552828 prefixEnd_4552828 2337789101248218273211931 := by
  unfold tailWord_4552828
  simp only [CollatzResearch.WordTrace]
  refine ⟨83027639574944595981353569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110703519433259461308471425 83027639574944595981353569)
  ·
    refine ⟨62270729681208446986015177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83027639574944595981353569 62270729681208446986015177)
    ·
      refine ⟨46703047260906335239511383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62270729681208446986015177 46703047260906335239511383)
      ·
        refine ⟨70054570891359502859267075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46703047260906335239511383 70054570891359502859267075)
        ·
          refine ⟨105081856337039254288900613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70054570891359502859267075 105081856337039254288900613)
          ·
            refine ⟨19702848063194860179168865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105081856337039254288900613 19702848063194860179168865)
            ·
              refine ⟨14777136047396145134376649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19702848063194860179168865 14777136047396145134376649)
              ·
                refine ⟨11082852035547108850782487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14777136047396145134376649 11082852035547108850782487)
                ·
                  refine ⟨16624278053320663276173731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082852035547108850782487 16624278053320663276173731)
                  ·
                    refine ⟨24936417079980994914260597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16624278053320663276173731 24936417079980994914260597)
                    ·
                      refine ⟨2337789101248218273211931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24936417079980994914260597 2337789101248218273211931)
                      ·
                        rfl

theorem cell23_4552828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_4552828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552828 prefixEnd_4552828 := by exact prefixLift 4552828
  have htrace : WordTrace (prefixWord ++ tailWord_4552828) baseStart_4552828 baseEnd_4552828 := by
    simpa [prefixWord, tailWord_4552828, baseEnd_4552828] using wordTrace_append hprefix tailTrace_4552828
  have hstable : (prefixWord ++ tailWord_4552828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552828).length < 2 ^ (prefixWord ++ tailWord_4552828).sum := by decide
  have hdescent : baseEnd_4552828 < baseStart_4552828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552835 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 2, 4]
def baseStart_4552835 : Nat := 118140960795 + 4552835 * 2 ^ 59
def prefixEnd_4552835 : Nat := 4983230072969 + 3 ^ 40 * 4552835 * 2
def baseEnd_4552835 : Nat := 779264231870933248608133

theorem tailTrace_4552835 : CollatzResearch.WordTrace tailWord_4552835 prefixEnd_4552835 779264231870933248608133 := by
  unfold tailWord_4552835
  simp only [CollatzResearch.WordTrace]
  refine ⟨166055534460863832158211959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110703689640575888105474639 166055534460863832158211959)
  ·
    refine ⟨249083301691295748237317939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166055534460863832158211959 249083301691295748237317939)
    ·
      refine ⟨373624952536943622355976909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249083301691295748237317939 373624952536943622355976909)
      ·
        refine ⟨140109357201353858383491341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373624952536943622355976909 140109357201353858383491341)
        ·
          refine ⟨52541008950507696893809253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140109357201353858383491341 52541008950507696893809253)
          ·
            refine ⟨9851439178220193167589235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52541008950507696893809253 9851439178220193167589235)
            ·
              refine ⟨14777158767330289751383853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851439178220193167589235 14777158767330289751383853)
              ·
                refine ⟨5541434537748858656768945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14777158767330289751383853 5541434537748858656768945)
                ·
                  refine ⟨4156075903311643992576709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541434537748858656768945 4156075903311643992576709)
                  ·
                    refine ⟨779264231870933248608133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156075903311643992576709 779264231870933248608133)
                    ·
                      rfl

theorem cell23_4552835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 4].length) (baseStart_4552835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552835 prefixEnd_4552835 := by exact prefixLift 4552835
  have htrace : WordTrace (prefixWord ++ tailWord_4552835) baseStart_4552835 baseEnd_4552835 := by
    simpa [prefixWord, tailWord_4552835, baseEnd_4552835] using wordTrace_append hprefix tailTrace_4552835
  have hstable : (prefixWord ++ tailWord_4552835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552835).length < 2 ^ (prefixWord ++ tailWord_4552835).sum := by decide
  have hdescent : baseEnd_4552835 < baseStart_4552835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552842 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4552842 : Nat := 118140960795 + 4552842 * 2 ^ 59
def prefixEnd_4552842 : Nat := 4983230072969 + 3 ^ 40 * 4552842 * 2
def baseEnd_4552842 : Nat := 2337796289977381218436867

theorem tailTrace_4552842 : CollatzResearch.WordTrace tailWord_4552842 prefixEnd_4552842 2337796289977381218436867 := by
  unfold tailWord_4552842
  simp only [CollatzResearch.WordTrace]
  refine ⟨41513947442959618088429195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110703859847892314902477853 41513947442959618088429195)
  ·
    refine ⟨62270921164439427132643793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41513947442959618088429195 62270921164439427132643793)
    ·
      refine ⟨46703190873329570349482845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62270921164439427132643793 46703190873329570349482845)
      ·
        refine ⟨17513696577498588881056067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46703190873329570349482845 17513696577498588881056067)
        ·
          refine ⟨26270544866247883321584101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17513696577498588881056067 26270544866247883321584101)
          ·
            refine ⟨4925727162421478122797019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26270544866247883321584101 4925727162421478122797019)
            ·
              refine ⟨7388590743632217184195529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925727162421478122797019 7388590743632217184195529)
              ·
                refine ⟨5541443057724162888146647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7388590743632217184195529 5541443057724162888146647)
                ·
                  refine ⟨8312164586586244332219971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541443057724162888146647 8312164586586244332219971)
                  ·
                    refine ⟨12468246879879366498329957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8312164586586244332219971 12468246879879366498329957)
                    ·
                      refine ⟨2337796289977381218436867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12468246879879366498329957 2337796289977381218436867)
                      ·
                        rfl

theorem cell23_4552842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4552842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552842 prefixEnd_4552842 := by exact prefixLift 4552842
  have htrace : WordTrace (prefixWord ++ tailWord_4552842) baseStart_4552842 baseEnd_4552842 := by
    simpa [prefixWord, tailWord_4552842, baseEnd_4552842] using wordTrace_append hprefix tailTrace_4552842
  have hstable : (prefixWord ++ tailWord_4552842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552842).length < 2 ^ (prefixWord ++ tailWord_4552842).sum := by decide
  have hdescent : baseEnd_4552842 < baseStart_4552842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552852 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4552852 : Nat := 118140960795 + 4552852 * 2 ^ 59
def prefixEnd_4552852 : Nat := 4983230072969 + 3 ^ 40 * 4552852 * 2
def baseEnd_4552852 : Nat := 779267141594642059770607

theorem tailTrace_4552852 : CollatzResearch.WordTrace tailWord_4552852 prefixEnd_4552852 779267141594642059770607 := by
  unfold tailWord_4552852
  simp only [CollatzResearch.WordTrace]
  refine ⟨83028077250901122030790405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110704103001201496041053873 83028077250901122030790405)
  ·
    refine ⟨15567764484543960380773201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83028077250901122030790405 15567764484543960380773201)
    ·
      refine ⟨11675823363407970285579901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15567764484543960380773201 11675823363407970285579901)
      ·
        refine ⟨4378433761277988857092463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11675823363407970285579901 4378433761277988857092463)
        ·
          refine ⟨6567650641916983285638695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378433761277988857092463 6567650641916983285638695)
          ·
            refine ⟨9851475962875474928458043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567650641916983285638695 9851475962875474928458043)
            ·
              refine ⟨14777213944313212392687065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851475962875474928458043 14777213944313212392687065)
              ·
                refine ⟨11082910458234909294515299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14777213944313212392687065 11082910458234909294515299)
                ·
                  refine ⟨16624365687352363941772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082910458234909294515299 16624365687352363941772949)
                  ·
                    refine ⟨779267141594642059770607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16624365687352363941772949 779267141594642059770607)
                    ·
                      rfl

theorem cell23_4552852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4552852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552852 prefixEnd_4552852 := by exact prefixLift 4552852
  have htrace : WordTrace (prefixWord ++ tailWord_4552852) baseStart_4552852 baseEnd_4552852 := by
    simpa [prefixWord, tailWord_4552852, baseEnd_4552852] using wordTrace_append hprefix tailTrace_4552852
  have hstable : (prefixWord ++ tailWord_4552852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552852).length < 2 ^ (prefixWord ++ tailWord_4552852).sum := by decide
  have hdescent : baseEnd_4552852 < baseStart_4552852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552855 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_4552855 : Nat := 118140960795 + 4552855 * 2 ^ 59
def prefixEnd_4552855 : Nat := 4983230072969 + 3 ^ 40 * 4552855 * 2
def baseEnd_4552855 : Nat := 2337802965225889667574307

theorem tailTrace_4552855 : CollatzResearch.WordTrace tailWord_4552855 prefixEnd_4552855 2337802965225889667574307 := by
  unfold tailWord_4552855
  simp only [CollatzResearch.WordTrace]
  refine ⟨166056263920791375573940019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110704175947194250382626679 166056263920791375573940019)
  ·
    refine ⟨249084395881187063360910029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166056263920791375573940019 249084395881187063360910029)
    ·
      refine ⟨93406648455445148760341261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249084395881187063360910029 93406648455445148760341261)
      ·
        refine ⟨35027493170791930785127973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93406648455445148760341261 35027493170791930785127973)
        ·
          refine ⟨6567654969523487022211495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35027493170791930785127973 6567654969523487022211495)
          ·
            refine ⟨9851482454285230533317243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567654969523487022211495 9851482454285230533317243)
            ·
              refine ⟨14777223681427845799975865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851482454285230533317243 14777223681427845799975865)
              ·
                refine ⟨11082917761070884349981899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14777223681427845799975865 11082917761070884349981899)
                ·
                  refine ⟨16624376641606326524972849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11082917761070884349981899 16624376641606326524972849)
                  ·
                    refine ⟨12468282481204744893729637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16624376641606326524972849 12468282481204744893729637)
                    ·
                      refine ⟨2337802965225889667574307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12468282481204744893729637 2337802965225889667574307)
                      ·
                        rfl

theorem cell23_4552855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_4552855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552855 prefixEnd_4552855 := by exact prefixLift 4552855
  have htrace : WordTrace (prefixWord ++ tailWord_4552855) baseStart_4552855 baseEnd_4552855 := by
    simpa [prefixWord, tailWord_4552855, baseEnd_4552855] using wordTrace_append hprefix tailTrace_4552855
  have hstable : (prefixWord ++ tailWord_4552855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552855).length < 2 ^ (prefixWord ++ tailWord_4552855).sum := by decide
  have hdescent : baseEnd_4552855 < baseStart_4552855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552892 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4552892 : Nat := 118140960795 + 4552892 * 2 ^ 59
def prefixEnd_4552892 : Nat := 4983230072969 + 3 ^ 40 * 4552892 * 2
def baseEnd_4552892 : Nat := 2337821964010106022811637

theorem tailTrace_4552892 : CollatzResearch.WordTrace tailWord_4552892 prefixEnd_4552892 2337821964010106022811637 := by
  unfold tailWord_4552892
  simp only [CollatzResearch.WordTrace]
  refine ⟨83028806710828665446518465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110705075614438220595357953 83028806710828665446518465)
  ·
    refine ⟨62271605033121499084888849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83028806710828665446518465 62271605033121499084888849)
    ·
      refine ⟨46703703774841124313666637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62271605033121499084888849 46703703774841124313666637)
      ·
        refine ⟨17513888915565421617624989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46703703774841124313666637 17513888915565421617624989)
        ·
          refine ⟨6567708343337033106609371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17513888915565421617624989 6567708343337033106609371)
          ·
            refine ⟨9851562515005549659914057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567708343337033106609371 9851562515005549659914057)
            ·
              refine ⟨7388671886254162244935543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851562515005549659914057 7388671886254162244935543)
              ·
                refine ⟨11083007829381243367403315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388671886254162244935543 11083007829381243367403315)
                ·
                  refine ⟨16624511744071865051104973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11083007829381243367403315 16624511744071865051104973)
                  ·
                    refine ⟨6234191904026949394164365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16624511744071865051104973 6234191904026949394164365)
                    ·
                      refine ⟨2337821964010106022811637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234191904026949394164365 2337821964010106022811637)
                      ·
                        rfl

theorem cell23_4552892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4552892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552892 prefixEnd_4552892 := by exact prefixLift 4552892
  have htrace : WordTrace (prefixWord ++ tailWord_4552892) baseStart_4552892 baseEnd_4552892 := by
    simpa [prefixWord, tailWord_4552892, baseEnd_4552892] using wordTrace_append hprefix tailTrace_4552892
  have hstable : (prefixWord ++ tailWord_4552892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552892).length < 2 ^ (prefixWord ++ tailWord_4552892).sum := by decide
  have hdescent : baseEnd_4552892 < baseStart_4552892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552925 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4552925 : Nat := 118140960795 + 4552925 * 2 ^ 59
def prefixEnd_4552925 : Nat := 4983230072969 + 3 ^ 40 * 4552925 * 2
def baseEnd_4552925 : Nat := 779279636290568131232995

theorem tailTrace_4552925 : CollatzResearch.WordTrace tailWord_4552925 prefixEnd_4552925 779279636290568131232995 := by
  unfold tailWord_4552925
  simp only [CollatzResearch.WordTrace]
  refine ⟨166058817030537777528988229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110705878020358518352658819 166058817030537777528988229)
  ·
    refine ⟨31136028193225833286685293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166058817030537777528988229 31136028193225833286685293)
    ·
      refine ⟨11676010572459687482506985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31136028193225833286685293 11676010572459687482506985)
      ·
        refine ⟨8757007929344765611880239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11676010572459687482506985 8757007929344765611880239)
        ·
          refine ⟨13135511894017148417820359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757007929344765611880239 13135511894017148417820359)
          ·
            refine ⟨19703267841025722626730539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13135511894017148417820359 19703267841025722626730539)
            ·
              refine ⟨29554901761538583940095809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19703267841025722626730539 29554901761538583940095809)
              ·
                refine ⟨22166176321153937955071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29554901761538583940095809 22166176321153937955071857)
                ·
                  refine ⟨16624632240865453466303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22166176321153937955071857 16624632240865453466303893)
                  ·
                    refine ⟨779279636290568131232995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16624632240865453466303893 779279636290568131232995)
                    ·
                      rfl

theorem cell23_4552925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4552925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552925 prefixEnd_4552925 := by exact prefixLift 4552925
  have htrace : WordTrace (prefixWord ++ tailWord_4552925) baseStart_4552925 baseEnd_4552925 := by
    simpa [prefixWord, tailWord_4552925, baseEnd_4552925] using wordTrace_append hprefix tailTrace_4552925
  have hstable : (prefixWord ++ tailWord_4552925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552925).length < 2 ^ (prefixWord ++ tailWord_4552925).sum := by decide
  have hdescent : baseEnd_4552925 < baseStart_4552925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552928 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_4552928 : Nat := 118140960795 + 4552928 * 2 ^ 59
def prefixEnd_4552928 : Nat := 4983230072969 + 3 ^ 40 * 4552928 * 2
def baseEnd_4552928 : Nat := 2337840449313667881961471

theorem tailTrace_4552928 : CollatzResearch.WordTrace tailWord_4552928 prefixEnd_4552928 2337840449313667881961471 := by
  unfold tailWord_4552928
  simp only [CollatzResearch.WordTrace]
  refine ⟨83029463224763454520673719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110705950966351272694231625 83029463224763454520673719)
  ·
    refine ⟨124544194837145181781010579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83029463224763454520673719 124544194837145181781010579)
    ·
      refine ⟨186816292255717772671515869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124544194837145181781010579 186816292255717772671515869)
      ·
        refine ⟨70056109595894164751818451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186816292255717772671515869 70056109595894164751818451)
        ·
          refine ⟨105084164393841247127727677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70056109595894164751818451 105084164393841247127727677)
          ·
            refine ⟨39406561647690467672897879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105084164393841247127727677 39406561647690467672897879)
            ·
              refine ⟨59109842471535701509346819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39406561647690467672897879 59109842471535701509346819)
              ·
                refine ⟨88664763707303552264020229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59109842471535701509346819 88664763707303552264020229)
                ·
                  refine ⟨16624643195119416049503793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88664763707303552264020229 16624643195119416049503793)
                  ·
                    refine ⟨12468482396339562037127845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16624643195119416049503793 12468482396339562037127845)
                    ·
                      refine ⟨2337840449313667881961471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12468482396339562037127845 2337840449313667881961471)
                      ·
                        rfl

theorem cell23_4552928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_4552928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552928 prefixEnd_4552928 := by exact prefixLift 4552928
  have htrace : WordTrace (prefixWord ++ tailWord_4552928) baseStart_4552928 baseEnd_4552928 := by
    simpa [prefixWord, tailWord_4552928, baseEnd_4552928] using wordTrace_append hprefix tailTrace_4552928
  have hstable : (prefixWord ++ tailWord_4552928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552928).length < 2 ^ (prefixWord ++ tailWord_4552928).sum := by decide
  have hdescent : baseEnd_4552928 < baseStart_4552928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4552989 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 7]
def baseStart_4552989 : Nat := 118140960795 + 4552989 * 2 ^ 59
def prefixEnd_4552989 : Nat := 4983230072969 + 3 ^ 40 * 4552989 * 2
def baseEnd_4552989 : Nat := 259763530181510238144299

theorem tailTrace_4552989 : CollatzResearch.WordTrace tailWord_4552989 prefixEnd_4552989 259763530181510238144299 := by
  unfold tailWord_4552989
  simp only [CollatzResearch.WordTrace]
  refine ⟨166061151302305916459318021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110707434201537277639545347 166061151302305916459318021)
  ·
    refine ⟨31136465869182359336122129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166061151302305916459318021 31136465869182359336122129)
    ·
      refine ⟨23352349401886769502091597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31136465869182359336122129 23352349401886769502091597)
      ·
        refine ⟨8757131025707538563284349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23352349401886769502091597 8757131025707538563284349)
        ·
          refine ⟨3283924134640326961231631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8757131025707538563284349 3283924134640326961231631)
          ·
            refine ⟨4925886201960490441847447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283924134640326961231631 4925886201960490441847447)
            ·
              refine ⟨7388829302940735662771171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4925886201960490441847447 7388829302940735662771171)
              ·
                refine ⟨11083243954411103494156757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388829302940735662771171 11083243954411103494156757)
                ·
                  refine ⟨259763530181510238144299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11083243954411103494156757 259763530181510238144299)
                  ·
                    rfl

theorem cell23_4552989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_4552989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4552989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4552989 prefixEnd_4552989 := by exact prefixLift 4552989
  have htrace : WordTrace (prefixWord ++ tailWord_4552989) baseStart_4552989 baseEnd_4552989 := by
    simpa [prefixWord, tailWord_4552989, baseEnd_4552989] using wordTrace_append hprefix tailTrace_4552989
  have hstable : (prefixWord ++ tailWord_4552989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4552989).length < 2 ^ (prefixWord ++ tailWord_4552989).sum := by decide
  have hdescent : baseEnd_4552989 < baseStart_4552989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4552989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553000 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4553000 : Nat := 118140960795 + 4553000 * 2 ^ 59
def prefixEnd_4553000 : Nat := 4983230072969 + 3 ^ 40 * 4553000 * 2
def baseEnd_4553000 : Nat := 2337877419920791600261141

theorem tailTrace_4553000 : CollatzResearch.WordTrace tailWord_4553000 prefixEnd_4553000 2337877419920791600261141 := by
  unfold tailWord_4553000
  simp only [CollatzResearch.WordTrace]
  refine ⟨83030776252633032668984227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110707701670177376891978969 83030776252633032668984227)
  ·
    refine ⟨124546164378949549003476341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83030776252633032668984227 124546164378949549003476341)
    ·
      refine ⟨11676202910526520219075907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124546164378949549003476341 11676202910526520219075907)
      ·
        refine ⟨17514304365789780328613861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11676202910526520219075907 17514304365789780328613861)
        ·
          refine ⟨3283932068585583811615099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17514304365789780328613861 3283932068585583811615099)
          ·
            refine ⟨4925898102878375717422649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283932068585583811615099 4925898102878375717422649)
            ·
              refine ⟨3694423577158781788066987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925898102878375717422649 3694423577158781788066987)
              ·
                refine ⟨5541635365738172682100481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694423577158781788066987 5541635365738172682100481)
                ·
                  refine ⟨4156226524303629511575361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541635365738172682100481 4156226524303629511575361)
                  ·
                    refine ⟨3117169893227722133681521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4156226524303629511575361 3117169893227722133681521)
                    ·
                      refine ⟨2337877419920791600261141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117169893227722133681521 2337877419920791600261141)
                      ·
                        rfl

theorem cell23_4553000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4553000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553000 prefixEnd_4553000 := by exact prefixLift 4553000
  have htrace : WordTrace (prefixWord ++ tailWord_4553000) baseStart_4553000 baseEnd_4553000 := by
    simpa [prefixWord, tailWord_4553000, baseEnd_4553000] using wordTrace_append hprefix tailTrace_4553000
  have hstable : (prefixWord ++ tailWord_4553000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553000).length < 2 ^ (prefixWord ++ tailWord_4553000).sum := by decide
  have hdescent : baseEnd_4553000 < baseStart_4553000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553015 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 3, 4]
def baseStart_4553015 : Nat := 118140960795 + 4553015 * 2 ^ 59
def prefixEnd_4553015 : Nat := 4983230072969 + 3 ^ 40 * 4553015 * 2
def baseEnd_4553015 : Nat := 779295040710203013857857

theorem tailTrace_4553015 : CollatzResearch.WordTrace tailWord_4553015 prefixEnd_4553015 779295040710203013857857 := by
  unfold tailWord_4553015
  simp only [CollatzResearch.WordTrace]
  refine ⟨166062099600211722899764499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110708066400141148599842999 166062099600211722899764499)
  ·
    refine ⟨249093149400317584349646749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166062099600211722899764499 249093149400317584349646749)
    ·
      refine ⟨93409931025119094131117531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249093149400317584349646749 93409931025119094131117531)
      ·
        refine ⟨140114896537678641196676297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93409931025119094131117531 140114896537678641196676297)
        ·
          refine ⟨105086172403258980897507223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140114896537678641196676297 105086172403258980897507223)
          ·
            refine ⟨157629258604888471346260835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105086172403258980897507223 157629258604888471346260835)
            ·
              refine ⟨236443887907332707019391253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157629258604888471346260835 236443887907332707019391253)
              ·
                refine ⟨11083307245656220641533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236443887907332707019391253 11083307245656220641533965)
                ·
                  refine ⟨4156240217121082740575237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11083307245656220641533965 4156240217121082740575237)
                  ·
                    refine ⟨779295040710203013857857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156240217121082740575237 779295040710203013857857)
                    ·
                      rfl

theorem cell23_4553015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_4553015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553015 prefixEnd_4553015 := by exact prefixLift 4553015
  have htrace : WordTrace (prefixWord ++ tailWord_4553015) baseStart_4553015 baseEnd_4553015 := by
    simpa [prefixWord, tailWord_4553015, baseEnd_4553015] using wordTrace_append hprefix tailTrace_4553015
  have hstable : (prefixWord ++ tailWord_4553015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553015).length < 2 ^ (prefixWord ++ tailWord_4553015).sum := by decide
  have hdescent : baseEnd_4553015 < baseStart_4553015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553022 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4553022 : Nat := 118140960795 + 4553022 * 2 ^ 59
def prefixEnd_4553022 : Nat := 4983230072969 + 3 ^ 40 * 4553022 * 2
def baseEnd_4553022 : Nat := 2337888716495190514186039

theorem tailTrace_4553022 : CollatzResearch.WordTrace tailWord_4553022 prefixEnd_4553022 2337888716495190514186039 := by
  unfold tailWord_4553022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20757794363898295386908665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110708236607457575396846213 20757794363898295386908665)
  ·
    refine ⟨15568345772923721540181499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20757794363898295386908665 15568345772923721540181499)
    ·
      refine ⟨23352518659385582310272249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15568345772923721540181499 23352518659385582310272249)
      ·
        refine ⟨17514388994539186732704187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23352518659385582310272249 17514388994539186732704187)
        ·
          refine ⟨26271583491808780099056281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17514388994539186732704187 26271583491808780099056281)
          ·
            refine ⟨19703687618856585074292211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26271583491808780099056281 19703687618856585074292211)
            ·
              refine ⟨29555531428284877611438317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19703687618856585074292211 29555531428284877611438317)
              ·
                refine ⟨11083324285606829104289369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29555531428284877611438317 11083324285606829104289369)
                ·
                  refine ⟨8312493214205121828217027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11083324285606829104289369 8312493214205121828217027)
                  ·
                    refine ⟨12468739821307682742325541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8312493214205121828217027 12468739821307682742325541)
                    ·
                      refine ⟨2337888716495190514186039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12468739821307682742325541 2337888716495190514186039)
                      ·
                        rfl

theorem cell23_4553022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4553022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553022 prefixEnd_4553022 := by exact prefixLift 4553022
  have htrace : WordTrace (prefixWord ++ tailWord_4553022) baseStart_4553022 baseEnd_4553022 := by
    simpa [prefixWord, tailWord_4553022, baseEnd_4553022] using wordTrace_append hprefix tailTrace_4553022
  have hstable : (prefixWord ++ tailWord_4553022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553022).length < 2 ^ (prefixWord ++ tailWord_4553022).sum := by decide
  have hdescent : baseEnd_4553022 < baseStart_4553022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553042 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_4553042 : Nat := 118140960795 + 4553042 * 2 ^ 59
def prefixEnd_4553042 : Nat := 4983230072969 + 3 ^ 40 * 4553042 * 2
def baseEnd_4553042 : Nat := 2337898986108280435935947

theorem tailTrace_4553042 : CollatzResearch.WordTrace tailWord_4553042 prefixEnd_4553042 2337898986108280435935947 := by
  unfold tailWord_4553042
  simp only [CollatzResearch.WordTrace]
  refine ⟨41515771092778476627749345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110708722914075937673998253 41515771092778476627749345)
  ·
    refine ⟨31136828319583857470812009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41515771092778476627749345 31136828319583857470812009)
    ·
      refine ⟨23352621239687893103109007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31136828319583857470812009 23352621239687893103109007)
      ·
        refine ⟨35028931859531839654663511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23352621239687893103109007 35028931859531839654663511)
        ·
          refine ⟨52543397789297759481995267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35028931859531839654663511 52543397789297759481995267)
          ·
            refine ⟨78815096683946639222992901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52543397789297759481995267 78815096683946639222992901)
            ·
              refine ⟨14777830628239994854311169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78815096683946639222992901 14777830628239994854311169)
              ·
                refine ⟨11083372971179996140733377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14777830628239994854311169 11083372971179996140733377)
                ·
                  refine ⟨8312529728384997105550033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11083372971179996140733377 8312529728384997105550033)
                  ·
                    refine ⟨6234397296288747829162525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8312529728384997105550033 6234397296288747829162525)
                    ·
                      refine ⟨2337898986108280435935947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234397296288747829162525 2337898986108280435935947)
                      ·
                        rfl

theorem cell23_4553042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_4553042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553042 prefixEnd_4553042 := by exact prefixLift 4553042
  have htrace : WordTrace (prefixWord ++ tailWord_4553042) baseStart_4553042 baseEnd_4553042 := by
    simpa [prefixWord, tailWord_4553042, baseEnd_4553042] using wordTrace_append hprefix tailTrace_4553042
  have hstable : (prefixWord ++ tailWord_4553042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553042).length < 2 ^ (prefixWord ++ tailWord_4553042).sum := by decide
  have hdescent : baseEnd_4553042 < baseStart_4553042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553072 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_4553072 : Nat := 118140960795 + 4553072 * 2 ^ 59
def prefixEnd_4553072 : Nat := 4983230072969 + 3 ^ 40 * 4553072 * 2
def baseEnd_4553072 : Nat := 2337914390527915318560809

theorem tailTrace_4553072 : CollatzResearch.WordTrace tailWord_4553072 prefixEnd_4553072 2337914390527915318560809 := by
  unfold tailWord_4553072
  simp only [CollatzResearch.WordTrace]
  refine ⟨83032089280502610817294735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110709452374003481089726313 83032089280502610817294735)
  ·
    refine ⟨124548133920753916225942103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83032089280502610817294735 124548133920753916225942103)
    ·
      refine ⟨186822200881130874338913155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124548133920753916225942103 186822200881130874338913155)
      ·
        refine ⟨280233301321696311508369733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186822200881130874338913155 280233301321696311508369733)
        ·
          refine ⟨52543743997818058407819325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 280233301321696311508369733 52543743997818058407819325)
          ·
            refine ⟨19703903999181771902932247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52543743997818058407819325 19703903999181771902932247)
            ·
              refine ⟨29555855998772657854398371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19703903999181771902932247 29555855998772657854398371)
              ·
                refine ⟨44333783998158986781597557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29555855998772657854398371 44333783998158986781597557)
                ·
                  refine ⟨4156292249827405010774771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44333783998158986781597557 4156292249827405010774771)
                  ·
                    refine ⟨6234438374741107516162157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4156292249827405010774771 6234438374741107516162157)
                    ·
                      refine ⟨2337914390527915318560809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234438374741107516162157 2337914390527915318560809)
                      ·
                        rfl

theorem cell23_4553072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_4553072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553072 prefixEnd_4553072 := by exact prefixLift 4553072
  have htrace : WordTrace (prefixWord ++ tailWord_4553072) baseStart_4553072 baseEnd_4553072 := by
    simpa [prefixWord, tailWord_4553072, baseEnd_4553072] using wordTrace_append hprefix tailTrace_4553072
  have hstable : (prefixWord ++ tailWord_4553072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553072).length < 2 ^ (prefixWord ++ tailWord_4553072).sum := by decide
  have hdescent : baseEnd_4553072 < baseStart_4553072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553092 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_4553092 : Nat := 118140960795 + 4553092 * 2 ^ 59
def prefixEnd_4553092 : Nat := 4983230072969 + 3 ^ 40 * 4553092 * 2
def baseEnd_4553092 : Nat := 779308220047001746770239

theorem tailTrace_4553092 : CollatzResearch.WordTrace tailWord_4553092 prefixEnd_4553092 779308220047001746770239 := by
  unfold tailWord_4553092
  simp only [CollatzResearch.WordTrace]
  refine ⟨83032454010466382525158765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110709938680621843366878353 83032454010466382525158765)
  ·
    refine ⟨31137170253924893446934537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83032454010466382525158765 31137170253924893446934537)
    ·
      refine ⟨23352877690443670085200903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31137170253924893446934537 23352877690443670085200903)
      ·
        refine ⟨35029316535665505127801355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23352877690443670085200903 35029316535665505127801355)
        ·
          refine ⟨52543974803498257691702033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35029316535665505127801355 52543974803498257691702033)
          ·
            refine ⟨39407981102623693268776525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52543974803498257691702033 39407981102623693268776525)
            ·
              refine ⟨14777992913483884975791197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39407981102623693268776525 14777992913483884975791197)
              ·
                refine ⟨5541747342556456865921699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14777992913483884975791197 5541747342556456865921699)
                ·
                  refine ⟨8312621013834685298882549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541747342556456865921699 8312621013834685298882549)
                  ·
                    refine ⟨779308220047001746770239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8312621013834685298882549 779308220047001746770239)
                    ·
                      rfl

theorem cell23_4553092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_4553092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553092 prefixEnd_4553092 := by exact prefixLift 4553092
  have htrace : WordTrace (prefixWord ++ tailWord_4553092) baseStart_4553092 baseEnd_4553092 := by
    simpa [prefixWord, tailWord_4553092, baseEnd_4553092] using wordTrace_append hprefix tailTrace_4553092
  have hstable : (prefixWord ++ tailWord_4553092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553092).length < 2 ^ (prefixWord ++ tailWord_4553092).sum := by decide
  have hdescent : baseEnd_4553092 < baseStart_4553092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553125 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_4553125 : Nat := 118140960795 + 4553125 * 2 ^ 59
def prefixEnd_4553125 : Nat := 4983230072969 + 3 ^ 40 * 4553125 * 2
def baseEnd_4553125 : Nat := 2337941605002603611198065

theorem tailTrace_4553125 : CollatzResearch.WordTrace tailWord_4553125 prefixEnd_4553125 2337941605002603611198065 := by
  unfold tailWord_4553125
  simp only [CollatzResearch.WordTrace]
  refine ⟨166066111629813211686268829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110710741086542141124179219 166066111629813211686268829)
  ·
    refine ⟨62274791861179954382350811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166066111629813211686268829 62274791861179954382350811)
    ·
      refine ⟨93412187791769931573526217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62274791861179954382350811 93412187791769931573526217)
      ·
        refine ⟨70059140843827448680144663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93412187791769931573526217 70059140843827448680144663)
        ·
          refine ⟨105088711265741173020216995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70059140843827448680144663 105088711265741173020216995)
          ·
            refine ⟨157633066898611759530325493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105088711265741173020216995 157633066898611759530325493)
            ·
              refine ⟨14778100021744852455968015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157633066898611759530325493 14778100021744852455968015)
              ·
                refine ⟨22167150032617278683952023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14778100021744852455968015 22167150032617278683952023)
                ·
                  refine ⟨33250725048925918025928035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22167150032617278683952023 33250725048925918025928035)
                  ·
                    refine ⟨49876087573388877038892053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33250725048925918025928035 49876087573388877038892053)
                    ·
                      refine ⟨2337941605002603611198065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49876087573388877038892053 2337941605002603611198065)
                      ·
                        rfl

theorem cell23_4553125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_4553125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553125 prefixEnd_4553125 := by exact prefixLift 4553125
  have htrace : WordTrace (prefixWord ++ tailWord_4553125) baseStart_4553125 baseEnd_4553125 := by
    simpa [prefixWord, tailWord_4553125, baseEnd_4553125] using wordTrace_append hprefix tailTrace_4553125
  have hstable : (prefixWord ++ tailWord_4553125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553125).length < 2 ^ (prefixWord ++ tailWord_4553125).sum := by decide
  have hdescent : baseEnd_4553125 < baseStart_4553125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553149 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_4553149 : Nat := 118140960795 + 4553149 * 2 ^ 59
def prefixEnd_4553149 : Nat := 4983230072969 + 3 ^ 40 * 4553149 * 2
def baseEnd_4553149 : Nat := 2337953928538311517297955

theorem tailTrace_4553149 : CollatzResearch.WordTrace tailWord_4553149 prefixEnd_4553149 2337953928538311517297955 := by
  unfold tailWord_4553149
  simp only [CollatzResearch.WordTrace]
  refine ⟨166066986981726263785142501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110711324654484175856761667 166066986981726263785142501)
  ·
    refine ⟨31137560059073674459714219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166066986981726263785142501 31137560059073674459714219)
    ·
      refine ⟨46706340088610511689571329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31137560059073674459714219 46706340088610511689571329)
      ·
        refine ⟨35029755066457883767178497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46706340088610511689571329 35029755066457883767178497)
        ·
          refine ⟨26272316299843412825383873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35029755066457883767178497 26272316299843412825383873)
          ·
            refine ⟨19704237224882559619037905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26272316299843412825383873 19704237224882559619037905)
            ·
              refine ⟨14778177918661919714278429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19704237224882559619037905 14778177918661919714278429)
              ·
                refine ⟨5541816719498219892854411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14778177918661919714278429 5541816719498219892854411)
                ·
                  refine ⟨8312725079247329839281617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5541816719498219892854411 8312725079247329839281617)
                  ·
                    refine ⟨6234543809435497379461213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8312725079247329839281617 6234543809435497379461213)
                    ·
                      refine ⟨2337953928538311517297955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234543809435497379461213 2337953928538311517297955)
                      ·
                        rfl

theorem cell23_4553149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_4553149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553149 prefixEnd_4553149 := by exact prefixLift 4553149
  have htrace : WordTrace (prefixWord ++ tailWord_4553149) baseStart_4553149 baseEnd_4553149 := by
    simpa [prefixWord, tailWord_4553149, baseEnd_4553149] using wordTrace_append hprefix tailTrace_4553149
  have hstable : (prefixWord ++ tailWord_4553149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553149).length < 2 ^ (prefixWord ++ tailWord_4553149).sum := by decide
  have hdescent : baseEnd_4553149 < baseStart_4553149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553270 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4553270 : Nat := 118140960795 + 4553270 * 2 ^ 59
def prefixEnd_4553270 : Nat := 4983230072969 + 3 ^ 40 * 4553270 * 2
def baseEnd_4553270 : Nat := 2338016059697505543884899

theorem tailTrace_4553270 : CollatzResearch.WordTrace tailWord_4553270 prefixEnd_4553270 2338016059697505543884899 := by
  unfold tailWord_4553270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379462513392993840643579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110714266809525267633531509 10379462513392993840643579)
  ·
    refine ⟨15569193770089490760965369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10379462513392993840643579 15569193770089490760965369)
    ·
      refine ⟨11676895327567118070724027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15569193770089490760965369 11676895327567118070724027)
      ·
        refine ⟨17515342991350677106086041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11676895327567118070724027 17515342991350677106086041)
        ·
          refine ⟨13136507243513007829564531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17515342991350677106086041 13136507243513007829564531)
          ·
            refine ⟨19704760865269511744346797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13136507243513007829564531 19704760865269511744346797)
            ·
              refine ⟨7389285324476066904130049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19704760865269511744346797 7389285324476066904130049)
              ·
                refine ⟨5541963993357050178097537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389285324476066904130049 5541963993357050178097537)
                ·
                  refine ⟨4156472995017787633573153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5541963993357050178097537 4156472995017787633573153)
                  ·
                    refine ⟨3117354746263340725179865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4156472995017787633573153 3117354746263340725179865)
                    ·
                      refine ⟨2338016059697505543884899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117354746263340725179865 2338016059697505543884899)
                      ·
                        rfl

theorem cell23_4553270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4553270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553270 prefixEnd_4553270 := by exact prefixLift 4553270
  have htrace : WordTrace (prefixWord ++ tailWord_4553270) baseStart_4553270 baseEnd_4553270 := by
    simpa [prefixWord, tailWord_4553270, baseEnd_4553270] using wordTrace_append hprefix tailTrace_4553270
  have hstable : (prefixWord ++ tailWord_4553270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553270).length < 2 ^ (prefixWord ++ tailWord_4553270).sum := by decide
  have hdescent : baseEnd_4553270 < baseStart_4553270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553272 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_4553272 : Nat := 118140960795 + 4553272 * 2 ^ 59
def prefixEnd_4553272 : Nat := 4983230072969 + 3 ^ 40 * 4553272 * 2
def baseEnd_4553272 : Nat := 779339028886271512019963

theorem tailTrace_4553272 : CollatzResearch.WordTrace tailWord_4553272 prefixEnd_4553272 779339028886271512019963 := by
  unfold tailWord_4553272
  simp only [CollatzResearch.WordTrace]
  refine ⟨83035736580140327895935035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110714315440187103861246713 83035736580140327895935035)
  ·
    refine ⟨124553604870210491843902553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83035736580140327895935035 124553604870210491843902553)
    ·
      refine ⟨93415203652657868882926915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124553604870210491843902553 93415203652657868882926915)
      ·
        refine ⟨140122805478986803324390373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93415203652657868882926915 140122805478986803324390373)
        ·
          refine ⟨26273026027310025623323195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140122805478986803324390373 26273026027310025623323195)
          ·
            refine ⟨39409539040965038434984793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26273026027310025623323195 39409539040965038434984793)
            ·
              refine ⟨29557154280723778826238595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39409539040965038434984793 29557154280723778826238595)
              ·
                refine ⟨44335731421085668239357893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29557154280723778826238595 44335731421085668239357893)
                ·
                  refine ⟨8312949641453562794879605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44335731421085668239357893 8312949641453562794879605)
                  ·
                    refine ⟨779339028886271512019963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8312949641453562794879605 779339028886271512019963)
                    ·
                      rfl

theorem cell23_4553272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_4553272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553272 prefixEnd_4553272 := by exact prefixLift 4553272
  have htrace : WordTrace (prefixWord ++ tailWord_4553272) baseStart_4553272 baseEnd_4553272 := by
    simpa [prefixWord, tailWord_4553272, baseEnd_4553272] using wordTrace_append hprefix tailTrace_4553272
  have hstable : (prefixWord ++ tailWord_4553272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553272).length < 2 ^ (prefixWord ++ tailWord_4553272).sum := by decide
  have hdescent : baseEnd_4553272 < baseStart_4553272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553292 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4553292 : Nat := 118140960795 + 4553292 * 2 ^ 59
def prefixEnd_4553292 : Nat := 4983230072969 + 3 ^ 40 * 4553292 * 2
def baseEnd_4553292 : Nat := 2338027356271904457809797

theorem tailTrace_4553292 : CollatzResearch.WordTrace tailWord_4553292 prefixEnd_4553292 2338027356271904457809797 := by
  unfold tailWord_4553292
  simp only [CollatzResearch.WordTrace]
  refine ⟨83036101310104099603799065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110714801746805466138398753 83036101310104099603799065)
  ·
    refine ⟨62277075982578074702849299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83036101310104099603799065 62277075982578074702849299)
    ·
      refine ⟨93415613973867112054273949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62277075982578074702849299 93415613973867112054273949)
      ·
        refine ⟨35030855240200167020352731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93415613973867112054273949 35030855240200167020352731)
        ·
          refine ⟨52546282860300250530529097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35030855240200167020352731 52546282860300250530529097)
          ·
            refine ⟨39409712145225187897896823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52546282860300250530529097 39409712145225187897896823)
            ·
              refine ⟨59114568217837781846845235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39409712145225187897896823 59114568217837781846845235)
              ·
                refine ⟨88671852326756672770267853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59114568217837781846845235 88671852326756672770267853)
                ·
                  refine ⟨33251944622533752288850445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88671852326756672770267853 33251944622533752288850445)
                  ·
                    refine ⟨12469479233450157108318917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33251944622533752288850445 12469479233450157108318917)
                    ·
                      refine ⟨2338027356271904457809797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12469479233450157108318917 2338027356271904457809797)
                      ·
                        rfl

theorem cell23_4553292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4553292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553292 prefixEnd_4553292 := by exact prefixLift 4553292
  have htrace : WordTrace (prefixWord ++ tailWord_4553292) baseStart_4553292 baseEnd_4553292 := by
    simpa [prefixWord, tailWord_4553292, baseEnd_4553292] using wordTrace_append hprefix tailTrace_4553292
  have hstable : (prefixWord ++ tailWord_4553292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553292).length < 2 ^ (prefixWord ++ tailWord_4553292).sum := by decide
  have hdescent : baseEnd_4553292 < baseStart_4553292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553326 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4553326 : Nat := 118140960795 + 4553326 * 2 ^ 59
def prefixEnd_4553326 : Nat := 4983230072969 + 3 ^ 40 * 4553326 * 2
def baseEnd_4553326 : Nat := 2338044814614157324784641

theorem tailTrace_4553326 : CollatzResearch.WordTrace tailWord_4553326 prefixEnd_4553326 2338044814614157324784641 := by
  unfold tailWord_4553326
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759180337760627876791979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110715628468056682009557221 20759180337760627876791979)
  ·
    refine ⟨31138770506640941815187969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20759180337760627876791979 31138770506640941815187969)
    ·
      refine ⟨23354077879980706361390977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31138770506640941815187969 23354077879980706361390977)
      ·
        refine ⟨17515558409985529771043233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23354077879980706361390977 17515558409985529771043233)
        ·
          refine ⟨13136668807489147328282425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17515558409985529771043233 13136668807489147328282425)
          ·
            refine ⟨9852501605616860496211819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13136668807489147328282425 9852501605616860496211819)
            ·
              refine ⟨14778752408425290744317729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9852501605616860496211819 14778752408425290744317729)
              ·
                refine ⟨11084064306318968058238297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14778752408425290744317729 11084064306318968058238297)
                ·
                  refine ⟨8313048229739226043678723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11084064306318968058238297 8313048229739226043678723)
                  ·
                    refine ⟨12469572344608839065518085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8313048229739226043678723 12469572344608839065518085)
                    ·
                      refine ⟨2338044814614157324784641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12469572344608839065518085 2338044814614157324784641)
                      ·
                        rfl

theorem cell23_4553326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4553326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553326 prefixEnd_4553326 := by exact prefixLift 4553326
  have htrace : WordTrace (prefixWord ++ tailWord_4553326) baseStart_4553326 baseEnd_4553326 := by
    simpa [prefixWord, tailWord_4553326, baseEnd_4553326] using wordTrace_append hprefix tailTrace_4553326
  have hstable : (prefixWord ++ tailWord_4553326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553326).length < 2 ^ (prefixWord ++ tailWord_4553326).sum := by decide
  have hdescent : baseEnd_4553326 < baseStart_4553326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553349 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 6]
def baseStart_4553349 : Nat := 118140960795 + 4553349 * 2 ^ 59
def prefixEnd_4553349 : Nat := 4983230072969 + 3 ^ 40 * 4553349 * 2
def baseEnd_4553349 : Nat := 259784069407690081644115

theorem tailTrace_4553349 : CollatzResearch.WordTrace tailWord_4553349 prefixEnd_4553349 259784069407690081644115 := by
  unfold tailWord_4553349
  simp only [CollatzResearch.WordTrace]
  refine ⟨166074281581001697942423101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110716187720667798628282067 166074281581001697942423101)
  ·
    refine ⟨62277855592875636728408663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166074281581001697942423101 62277855592875636728408663)
    ·
      refine ⟨93416783389313455092612995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62277855592875636728408663 93416783389313455092612995)
      ·
        refine ⟨140125175083970182638919493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93416783389313455092612995 140125175083970182638919493)
        ·
          refine ⟨26273470328244409244797405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140125175083970182638919493 26273470328244409244797405)
          ·
            refine ⟨9852551373091653466799027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26273470328244409244797405 9852551373091653466799027)
            ·
              refine ⟨14778827059637480200198541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9852551373091653466799027 14778827059637480200198541)
              ·
                refine ⟨5542060147364055075074453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14778827059637480200198541 5542060147364055075074453)
                ·
                  refine ⟨259784069407690081644115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5542060147364055075074453 259784069407690081644115)
                  ·
                    rfl

theorem cell23_4553349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_4553349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553349 prefixEnd_4553349 := by exact prefixLift 4553349
  have htrace : WordTrace (prefixWord ++ tailWord_4553349) baseStart_4553349 baseEnd_4553349 := by
    simpa [prefixWord, tailWord_4553349, baseEnd_4553349] using wordTrace_append hprefix tailTrace_4553349
  have hstable : (prefixWord ++ tailWord_4553349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553349).length < 2 ^ (prefixWord ++ tailWord_4553349).sum := by decide
  have hdescent : baseEnd_4553349 < baseStart_4553349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553383 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 6]
def baseStart_4553383 : Nat := 118140960795 + 4553383 * 2 ^ 59
def prefixEnd_4553383 : Nat := 4983230072969 + 3 ^ 40 * 4553383 * 2
def baseEnd_4553383 : Nat := 259786009223495955752431

theorem tailTrace_4553383 : CollatzResearch.WordTrace tailWord_4553383 prefixEnd_4553383 259786009223495955752431 := by
  unfold tailWord_4553383
  simp only [CollatzResearch.WordTrace]
  refine ⟨166075521662878521749160803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110717014441919014499440535 166075521662878521749160803)
  ·
    refine ⟨249113282494317782623741205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166075521662878521749160803 249113282494317782623741205)
    ·
      refine ⟨11677185116921146060487869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 249113282494317782623741205 11677185116921146060487869)
      ·
        refine ⟨4378944418845429772682951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11677185116921146060487869 4378944418845429772682951)
        ·
          refine ⟨6568416628268144659024427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378944418845429772682951 6568416628268144659024427)
          ·
            refine ⟨9852624942402216988536641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568416628268144659024427 9852624942402216988536641)
            ·
              refine ⟨7389468706801662741402481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9852624942402216988536641 7389468706801662741402481)
              ·
                refine ⟨5542101530101247056051861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389468706801662741402481 5542101530101247056051861)
                ·
                  refine ⟨259786009223495955752431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5542101530101247056051861 259786009223495955752431)
                  ·
                    rfl

theorem cell23_4553383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 6].length) (baseStart_4553383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553383 prefixEnd_4553383 := by exact prefixLift 4553383
  have htrace : WordTrace (prefixWord ++ tailWord_4553383) baseStart_4553383 baseEnd_4553383 := by
    simpa [prefixWord, tailWord_4553383, baseEnd_4553383] using wordTrace_append hprefix tailTrace_4553383
  have hstable : (prefixWord ++ tailWord_4553383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553383).length < 2 ^ (prefixWord ++ tailWord_4553383).sum := by decide
  have hdescent : baseEnd_4553383 < baseStart_4553383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553392 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_4553392 : Nat := 118140960795 + 4553392 * 2 ^ 59
def prefixEnd_4553392 : Nat := 4983230072969 + 3 ^ 40 * 4553392 * 2
def baseEnd_4553392 : Nat := 779359568112451355519779

theorem tailTrace_4553392 : CollatzResearch.WordTrace tailWord_4553392 prefixEnd_4553392 779359568112451355519779 := by
  unfold tailWord_4553392
  simp only [CollatzResearch.WordTrace]
  refine ⟨83037924959922958143119215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110717233279897277524158953 83037924959922958143119215)
  ·
    refine ⟨124556887439884437214678823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83037924959922958143119215 124556887439884437214678823)
    ·
      refine ⟨186835331159826655822018235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124556887439884437214678823 186835331159826655822018235)
      ·
        refine ⟨280252996739739983733027353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186835331159826655822018235 280252996739739983733027353)
        ·
          refine ⟨210189747554804987799770515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280252996739739983733027353 210189747554804987799770515)
          ·
            refine ⟨315284621332207481699655773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210189747554804987799770515 315284621332207481699655773)
            ·
              refine ⟨118231732999577805637370915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 315284621332207481699655773 118231732999577805637370915)
              ·
                refine ⟨177347599499366708456056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118231732999577805637370915 177347599499366708456056373)
                ·
                  refine ⟨16626337453065628917755285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177347599499366708456056373 16626337453065628917755285)
                  ·
                    refine ⟨779359568112451355519779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16626337453065628917755285 779359568112451355519779)
                    ·
                      rfl

theorem cell23_4553392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_4553392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553392 prefixEnd_4553392 := by exact prefixLift 4553392
  have htrace : WordTrace (prefixWord ++ tailWord_4553392) baseStart_4553392 baseEnd_4553392 := by
    simpa [prefixWord, tailWord_4553392, baseEnd_4553392] using wordTrace_append hprefix tailTrace_4553392
  have hstable : (prefixWord ++ tailWord_4553392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553392).length < 2 ^ (prefixWord ++ tailWord_4553392).sum := by decide
  have hdescent : baseEnd_4553392 < baseStart_4553392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553414 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4553414 : Nat := 118140960795 + 4553414 * 2 ^ 59
def prefixEnd_4553414 : Nat := 4983230072969 + 3 ^ 40 * 4553414 * 2
def baseEnd_4553414 : Nat := 2338090000911752980484237

theorem tailTrace_4553414 : CollatzResearch.WordTrace tailWord_4553414 prefixEnd_4553414 2338090000911752980484237 := by
  unfold tailWord_4553414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189895385180194188860603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110717768217177476029026197 5189895385180194188860603)
  ·
    refine ⟨7784843077770291283290905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189895385180194188860603 7784843077770291283290905)
    ·
      refine ⟨5838632308327718462468179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7784843077770291283290905 5838632308327718462468179)
      ·
        refine ⟨8757948462491577693702269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838632308327718462468179 8757948462491577693702269)
        ·
          refine ⟨3284230673434341635138351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8757948462491577693702269 3284230673434341635138351)
          ·
            refine ⟨4926346010151512452707527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284230673434341635138351 4926346010151512452707527)
            ·
              refine ⟨7389519015227268679061291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926346010151512452707527 7389519015227268679061291)
              ·
                refine ⟨11084278522840903018591937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389519015227268679061291 11084278522840903018591937)
                ·
                  refine ⟨8313208892130677263943953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11084278522840903018591937 8313208892130677263943953)
                  ·
                    refine ⟨6234906669098007947957965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8313208892130677263943953 6234906669098007947957965)
                    ·
                      refine ⟨2338090000911752980484237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234906669098007947957965 2338090000911752980484237)
                      ·
                        rfl

theorem cell23_4553414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4553414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553414 prefixEnd_4553414 := by exact prefixLift 4553414
  have htrace : WordTrace (prefixWord ++ tailWord_4553414) baseStart_4553414 baseEnd_4553414 := by
    simpa [prefixWord, tailWord_4553414, baseEnd_4553414] using wordTrace_append hprefix tailTrace_4553414
  have hstable : (prefixWord ++ tailWord_4553414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553414).length < 2 ^ (prefixWord ++ tailWord_4553414).sum := by decide
  have hdescent : baseEnd_4553414 < baseStart_4553414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553420 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4553420 : Nat := 118140960795 + 4553420 * 2 ^ 59
def prefixEnd_4553420 : Nat := 4983230072969 + 3 ^ 40 * 4553420 * 2
def baseEnd_4553420 : Nat := 2338093081795679957009209

theorem tailTrace_4553420 : CollatzResearch.WordTrace tailWord_4553420 prefixEnd_4553420 2338093081795679957009209 := by
  unfold tailWord_4553420
  simp only [CollatzResearch.WordTrace]
  refine ⟨83038435581872238534128857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110717914109162984712171809 83038435581872238534128857)
  ·
    refine ⟨62278826686404178900596643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83038435581872238534128857 62278826686404178900596643)
    ·
      refine ⟨93418240029606268350894965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62278826686404178900596643 93418240029606268350894965)
      ·
        refine ⟨8757960002775587657896403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93418240029606268350894965 8757960002775587657896403)
        ·
          refine ⟨13136940004163381486844605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757960002775587657896403 13136940004163381486844605)
          ·
            refine ⟨4926352501561268057566727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13136940004163381486844605 4926352501561268057566727)
            ·
              refine ⟨7389528752341902086350091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926352501561268057566727 7389528752341902086350091)
              ·
                refine ⟨11084293128512853129525137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389528752341902086350091 11084293128512853129525137)
                ·
                  refine ⟨8313219846384639847143853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11084293128512853129525137 8313219846384639847143853)
                  ·
                    refine ⟨3117457442394239942678945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8313219846384639847143853 3117457442394239942678945)
                    ·
                      refine ⟨2338093081795679957009209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117457442394239942678945 2338093081795679957009209)
                      ·
                        rfl

theorem cell23_4553420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4553420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553420 prefixEnd_4553420 := by exact prefixLift 4553420
  have htrace : WordTrace (prefixWord ++ tailWord_4553420) baseStart_4553420 baseEnd_4553420 := by
    simpa [prefixWord, tailWord_4553420, baseEnd_4553420] using wordTrace_append hprefix tailTrace_4553420
  have hstable : (prefixWord ++ tailWord_4553420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553420).length < 2 ^ (prefixWord ++ tailWord_4553420).sum := by decide
  have hdescent : baseEnd_4553420 < baseStart_4553420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553443 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 2, 4]
def baseStart_4553443 : Nat := 118140960795 + 4553443 * 2 ^ 59
def prefixEnd_4553443 : Nat := 4983230072969 + 3 ^ 40 * 4553443 * 2
def baseEnd_4553443 : Nat := 779368297283577789007201

theorem tailTrace_4553443 : CollatzResearch.WordTrace tailWord_4553443 prefixEnd_4553443 779368297283577789007201 := by
  unfold tailWord_4553443
  simp only [CollatzResearch.WordTrace]
  refine ⟨166077710042661151996344983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110718473361774101330896655 166077710042661151996344983)
  ·
    refine ⟨249116565063991727994517475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166077710042661151996344983 249116565063991727994517475)
    ·
      refine ⟨373674847595987591991776213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249116565063991727994517475 373674847595987591991776213)
      ·
        refine ⟨8758004240530959187307255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 373674847595987591991776213 8758004240530959187307255)
        ·
          refine ⟨13137006360796438780960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8758004240530959187307255 13137006360796438780960883)
          ·
            refine ⟨19705509541194658171441325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13137006360796438780960883 19705509541194658171441325)
            ·
              refine ⟨7389566077947996814290497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19705509541194658171441325 7389566077947996814290497)
              ·
                refine ⟨5542174558460997610717873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389566077947996814290497 5542174558460997610717873)
                ·
                  refine ⟨4156630918845748208038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5542174558460997610717873 4156630918845748208038405)
                  ·
                    refine ⟨779368297283577789007201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156630918845748208038405 779368297283577789007201)
                    ·
                      rfl

theorem cell23_4553443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 4].length) (baseStart_4553443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553443 prefixEnd_4553443 := by exact prefixLift 4553443
  have htrace : WordTrace (prefixWord ++ tailWord_4553443) baseStart_4553443 baseEnd_4553443 := by
    simpa [prefixWord, tailWord_4553443, baseEnd_4553443] using wordTrace_append hprefix tailTrace_4553443
  have hstable : (prefixWord ++ tailWord_4553443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553443).length < 2 ^ (prefixWord ++ tailWord_4553443).sum := by decide
  have hdescent : baseEnd_4553443 < baseStart_4553443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553449 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_4553449 : Nat := 118140960795 + 4553449 * 2 ^ 59
def prefixEnd_4553449 : Nat := 4983230072969 + 3 ^ 40 * 4553449 * 2
def baseEnd_4553449 : Nat := 2338107972734660343546575

theorem tailTrace_4553449 : CollatzResearch.WordTrace tailWord_4553449 prefixEnd_4553449 2338107972734660343546575 := by
  unfold tailWord_4553449
  simp only [CollatzResearch.WordTrace]
  refine ⟨166077928880639415021063401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110718619253759610014042267 166077928880639415021063401)
  ·
    refine ⟨124558446660479561265797551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166077928880639415021063401 124558446660479561265797551)
    ·
      refine ⟨186837669990719341898696327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124558446660479561265797551 186837669990719341898696327)
      ·
        refine ⟨280256504986079012848044491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186837669990719341898696327 280256504986079012848044491)
        ·
          refine ⟨420384757479118519272066737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280256504986079012848044491 420384757479118519272066737)
          ·
            refine ⟨315288568109338889454050053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420384757479118519272066737 315288568109338889454050053)
            ·
              refine ⟨59116606520501041772634385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315288568109338889454050053 59116606520501041772634385)
              ·
                refine ⟨44337454890375781329475789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59116606520501041772634385 44337454890375781329475789)
                ·
                  refine ⟨16626545583890917998553421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44337454890375781329475789 16626545583890917998553421)
                  ·
                    refine ⟨6234954593959094249457533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16626545583890917998553421 6234954593959094249457533)
                    ·
                      refine ⟨2338107972734660343546575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234954593959094249457533 2338107972734660343546575)
                      ·
                        rfl

theorem cell23_4553449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_4553449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553449 prefixEnd_4553449 := by exact prefixLift 4553449
  have htrace : WordTrace (prefixWord ++ tailWord_4553449) baseStart_4553449 baseEnd_4553449 := by
    simpa [prefixWord, tailWord_4553449, baseEnd_4553449] using wordTrace_append hprefix tailTrace_4553449
  have hstable : (prefixWord ++ tailWord_4553449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553449).length < 2 ^ (prefixWord ++ tailWord_4553449).sum := by decide
  have hdescent : baseEnd_4553449 < baseStart_4553449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553466 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_4553466 : Nat := 118140960795 + 4553466 * 2 ^ 59
def prefixEnd_4553466 : Nat := 4983230072969 + 3 ^ 40 * 4553466 * 2
def baseEnd_4553466 : Nat := 2338116701905786777033997

theorem tailTrace_4553466 : CollatzResearch.WordTrace tailWord_4553466 prefixEnd_4553466 2338116701905786777033997 := by
  unfold tailWord_4553466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41519637230394456731108063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110719032614385217949621501 41519637230394456731108063)
  ·
    refine ⟨62279455845591685096662095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41519637230394456731108063 62279455845591685096662095)
    ·
      refine ⟨93419183768387527644993143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62279455845591685096662095 93419183768387527644993143)
      ·
        refine ⟨140128775652581291467489715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93419183768387527644993143 140128775652581291467489715)
        ·
          refine ⟨210193163478871937201234573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140128775652581291467489715 210193163478871937201234573)
          ·
            refine ⟨78822436304576976450462965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210193163478871937201234573 78822436304576976450462965)
            ·
              refine ⟨7389603403554091542230903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78822436304576976450462965 7389603403554091542230903)
              ·
                refine ⟨11084405105331137313346355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389603403554091542230903 11084405105331137313346355)
                ·
                  refine ⟨16626607657996705970019533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11084405105331137313346355 16626607657996705970019533)
                  ·
                    refine ⟨6234977871748764738757325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16626607657996705970019533 6234977871748764738757325)
                    ·
                      refine ⟨2338116701905786777033997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234977871748764738757325 2338116701905786777033997)
                      ·
                        rfl

theorem cell23_4553466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_4553466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553466 prefixEnd_4553466 := by exact prefixLift 4553466
  have htrace : WordTrace (prefixWord ++ tailWord_4553466) baseStart_4553466 baseEnd_4553466 := by
    simpa [prefixWord, tailWord_4553466, baseEnd_4553466] using wordTrace_append hprefix tailTrace_4553466
  have hstable : (prefixWord ++ tailWord_4553466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553466).length < 2 ^ (prefixWord ++ tailWord_4553466).sum := by decide
  have hdescent : baseEnd_4553466 < baseStart_4553466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553470 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4553470 : Nat := 118140960795 + 4553470 * 2 ^ 59
def prefixEnd_4553470 : Nat := 4983230072969 + 3 ^ 40 * 4553470 * 2
def baseEnd_4553470 : Nat := 2338118755828404761383979

theorem tailTrace_4553470 : CollatzResearch.WordTrace tailWord_4553470 prefixEnd_4553470 2338118755828404761383979 := by
  unfold tailWord_4553470
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759836851695416950947233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110719129875708890405051909 20759836851695416950947233)
  ·
    refine ⟨15569877638771562713210425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20759836851695416950947233 15569877638771562713210425)
    ·
      refine ⟨11677408229078672034907819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15569877638771562713210425 11677408229078672034907819)
      ·
        refine ⟨17516112343618008052361729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11677408229078672034907819 17516112343618008052361729)
        ·
          refine ⟨13137084257713506039271297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17516112343618008052361729 13137084257713506039271297)
          ·
            refine ⟨9852813193285129529453473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13137084257713506039271297 9852813193285129529453473)
            ·
              refine ⟨7389609894963847147090105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9852813193285129529453473 7389609894963847147090105)
              ·
                refine ⟨5542207421222885360317579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7389609894963847147090105 5542207421222885360317579)
                ·
                  refine ⟨8313311131834328040476369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542207421222885360317579 8313311131834328040476369)
                  ·
                    refine ⟨6234983348875746030357277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8313311131834328040476369 6234983348875746030357277)
                    ·
                      refine ⟨2338118755828404761383979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6234983348875746030357277 2338118755828404761383979)
                      ·
                        rfl

theorem cell23_4553470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4553470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553470 prefixEnd_4553470 := by exact prefixLift 4553470
  have htrace : WordTrace (prefixWord ++ tailWord_4553470) baseStart_4553470 baseEnd_4553470 := by
    simpa [prefixWord, tailWord_4553470, baseEnd_4553470] using wordTrace_append hprefix tailTrace_4553470
  have hstable : (prefixWord ++ tailWord_4553470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553470).length < 2 ^ (prefixWord ++ tailWord_4553470).sum := by decide
  have hdescent : baseEnd_4553470 < baseStart_4553470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553493 : List Nat := [1, 3, 2, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_4553493 : Nat := 118140960795 + 4553493 * 2 ^ 59
def prefixEnd_4553493 : Nat := 4983230072969 + 3 ^ 40 * 4553493 * 2
def baseEnd_4553493 : Nat := 2338130565883458171396373

theorem tailTrace_4553493 : CollatzResearch.WordTrace tailWord_4553493 prefixEnd_4553493 2338130565883458171396373 := by
  unfold tailWord_4553493
  simp only [CollatzResearch.WordTrace]
  refine ⟨166079533692480010535665133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110719689128320007023776755 166079533692480010535665133)
  ·
    refine ⟨62279825134680003950874425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166079533692480010535665133 62279825134680003950874425)
    ·
      refine ⟨46709868851010002963155819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62279825134680003950874425 46709868851010002963155819)
      ·
        refine ⟨70064803276515004444733729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46709868851010002963155819 70064803276515004444733729)
        ·
          refine ⟨52548602457386253333550297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70064803276515004444733729 52548602457386253333550297)
          ·
            refine ⟨39411451843039690000162723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52548602457386253333550297 39411451843039690000162723)
            ·
              refine ⟨59117177764559535000244085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39411451843039690000162723 59117177764559535000244085)
              ·
                refine ⟨5542235415427456406272883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59117177764559535000244085 5542235415427456406272883)
                ·
                  refine ⟨8313353123141184609409325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542235415427456406272883 8313353123141184609409325)
                  ·
                    refine ⟨3117507421177944228528497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8313353123141184609409325 3117507421177944228528497)
                    ·
                      refine ⟨2338130565883458171396373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117507421177944228528497 2338130565883458171396373)
                      ·
                        rfl

theorem cell23_4553493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_4553493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553493 prefixEnd_4553493 := by exact prefixLift 4553493
  have htrace : WordTrace (prefixWord ++ tailWord_4553493) baseStart_4553493 baseEnd_4553493 := by
    simpa [prefixWord, tailWord_4553493, baseEnd_4553493] using wordTrace_append hprefix tailTrace_4553493
  have hstable : (prefixWord ++ tailWord_4553493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553493).length < 2 ^ (prefixWord ++ tailWord_4553493).sum := by decide
  have hdescent : baseEnd_4553493 < baseStart_4553493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553501 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4553501 : Nat := 118140960795 + 4553501 * 2 ^ 59
def prefixEnd_4553501 : Nat := 4983230072969 + 3 ^ 40 * 4553501 * 2
def baseEnd_4553501 : Nat := 2338134673728694140096337

theorem tailTrace_4553501 : CollatzResearch.WordTrace tailWord_4553501 prefixEnd_4553501 2338134673728694140096337 := by
  unfold tailWord_4553501
  simp only [CollatzResearch.WordTrace]
  refine ⟨166079825476451027901956357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110719883650967351934637571 166079825476451027901956357)
  ·
    refine ⟨31139967276834567731616817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166079825476451027901956357 31139967276834567731616817)
    ·
      refine ⟨23354975457625925798712613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31139967276834567731616817 23354975457625925798712613)
      ·
        refine ⟨4379057898304861087258615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23354975457625925798712613 4379057898304861087258615)
        ·
          refine ⟨6568586847457291630887923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4379057898304861087258615 6568586847457291630887923)
          ·
            refine ⟨9852880271185937446331885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6568586847457291630887923 9852880271185937446331885)
            ·
              refine ⟨3694830101694726542374457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9852880271185937446331885 3694830101694726542374457)
              ·
                refine ⟨2771122576271044906780843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694830101694726542374457 2771122576271044906780843)
                ·
                  refine ⟨4156683864406567360171265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771122576271044906780843 4156683864406567360171265)
                  ·
                    refine ⟨3117512898304925520128449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4156683864406567360171265 3117512898304925520128449)
                    ·
                      refine ⟨2338134673728694140096337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3117512898304925520128449 2338134673728694140096337)
                      ·
                        rfl

theorem cell23_4553501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4553501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553501 prefixEnd_4553501 := by exact prefixLift 4553501
  have htrace : WordTrace (prefixWord ++ tailWord_4553501) baseStart_4553501 baseEnd_4553501 := by
    simpa [prefixWord, tailWord_4553501, baseEnd_4553501] using wordTrace_append hprefix tailTrace_4553501
  have hstable : (prefixWord ++ tailWord_4553501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553501).length < 2 ^ (prefixWord ++ tailWord_4553501).sum := by decide
  have hdescent : baseEnd_4553501 < baseStart_4553501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553509 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_4553509 : Nat := 118140960795 + 4553509 * 2 ^ 59
def prefixEnd_4553509 : Nat := 4983230072969 + 3 ^ 40 * 4553509 * 2
def baseEnd_4553509 : Nat := 2338138781573930108796299

theorem tailTrace_4553509 : CollatzResearch.WordTrace tailWord_4553509 prefixEnd_4553509 2338138781573930108796299 := by
  unfold tailWord_4553509
  simp only [CollatzResearch.WordTrace]
  refine ⟨166080117260422045268247581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110720078173614696845498387 166080117260422045268247581)
  ·
    refine ⟨62280043972658266975592843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166080117260422045268247581 62280043972658266975592843)
    ·
      refine ⟨93420065958987400463389265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62280043972658266975592843 93420065958987400463389265)
      ·
        refine ⟨70065049469240550347541949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93420065958987400463389265 70065049469240550347541949)
        ·
          refine ⟨26274393550965206380328231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70065049469240550347541949 26274393550965206380328231)
          ·
            refine ⟨39411590326447809570492347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26274393550965206380328231 39411590326447809570492347)
            ·
              refine ⟨59117385489671714355738521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39411590326447809570492347 59117385489671714355738521)
              ·
                refine ⟨44338039117253785766803891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59117385489671714355738521 44338039117253785766803891)
                ·
                  refine ⟨66507058675880678650205837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44338039117253785766803891 66507058675880678650205837)
                  ·
                    refine ⟨24940147003455254493827189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66507058675880678650205837 24940147003455254493827189)
                    ·
                      refine ⟨2338138781573930108796299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24940147003455254493827189 2338138781573930108796299)
                      ·
                        rfl

theorem cell23_4553509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_4553509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553509 prefixEnd_4553509 := by exact prefixLift 4553509
  have htrace : WordTrace (prefixWord ++ tailWord_4553509) baseStart_4553509 baseEnd_4553509 := by
    simpa [prefixWord, tailWord_4553509, baseEnd_4553509] using wordTrace_append hprefix tailTrace_4553509
  have hstable : (prefixWord ++ tailWord_4553509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553509).length < 2 ^ (prefixWord ++ tailWord_4553509).sum := by decide
  have hdescent : baseEnd_4553509 < baseStart_4553509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553569 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4553569 : Nat := 118140960795 + 4553569 * 2 ^ 59
def prefixEnd_4553569 : Nat := 4983230072969 + 3 ^ 40 * 4553569 * 2
def baseEnd_4553569 : Nat := 2338169590413199874046023

theorem tailTrace_4553569 : CollatzResearch.WordTrace tailWord_4553569 prefixEnd_4553569 2338169590413199874046023 := by
  unfold tailWord_4553569
  simp only [CollatzResearch.WordTrace]
  refine ⟨166082305640204675515431761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110721537093469783676954507 166082305640204675515431761)
  ·
    refine ⟨124561729230153506636573821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166082305640204675515431761 124561729230153506636573821)
    ·
      refine ⟨46710648461307564988715183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124561729230153506636573821 46710648461307564988715183)
      ·
        refine ⟨70065972691961347483072775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46710648461307564988715183 70065972691961347483072775)
        ·
          refine ⟨105098959037942021224609163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70065972691961347483072775 105098959037942021224609163)
          ·
            refine ⟨157648438556913031836913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105098959037942021224609163 157648438556913031836913745)
            ·
              refine ⟨118236328917684773877685309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157648438556913031836913745 118236328917684773877685309)
              ·
                refine ⟨44338623344131790204131991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118236328917684773877685309 44338623344131790204131991)
                ·
                  refine ⟨66507935016197685306197987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44338623344131790204131991 66507935016197685306197987)
                  ·
                    refine ⟨99761902524296527959296981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66507935016197685306197987 99761902524296527959296981)
                    ·
                      refine ⟨2338169590413199874046023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99761902524296527959296981 2338169590413199874046023)
                      ·
                        rfl

theorem cell23_4553569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4553569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553569 prefixEnd_4553569 := by exact prefixLift 4553569
  have htrace : WordTrace (prefixWord ++ tailWord_4553569) baseStart_4553569 baseEnd_4553569 := by
    simpa [prefixWord, tailWord_4553569, baseEnd_4553569] using wordTrace_append hprefix tailTrace_4553569
  have hstable : (prefixWord ++ tailWord_4553569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553569).length < 2 ^ (prefixWord ++ tailWord_4553569).sum := by decide
  have hdescent : baseEnd_4553569 < baseStart_4553569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553593 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_4553593 : Nat := 118140960795 + 4553593 * 2 ^ 59
def prefixEnd_4553593 : Nat := 4983230072969 + 3 ^ 40 * 4553593 * 2
def baseEnd_4553593 : Nat := 779393971316302593381971

theorem tailTrace_4553593 : CollatzResearch.WordTrace tailWord_4553593 prefixEnd_4553593 779393971316302593381971 := by
  unfold tailWord_4553593
  simp only [CollatzResearch.WordTrace]
  refine ⟨166083180992117727614305433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110722120661411818409536955 166083180992117727614305433)
  ·
    refine ⟨124562385744088295710729075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166083180992117727614305433 124562385744088295710729075)
    ·
      refine ⟨186843578616132443566093613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124562385744088295710729075 186843578616132443566093613)
      ·
        refine ⟨70066341981049666337285105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186843578616132443566093613 70066341981049666337285105)
        ·
          refine ⟨52549756485787249752963829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70066341981049666337285105 52549756485787249752963829)
          ·
            refine ⟨4926539670542554664340359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52549756485787249752963829 4926539670542554664340359)
            ·
              refine ⟨7389809505813831996510539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926539670542554664340359 7389809505813831996510539)
              ·
                refine ⟨11084714258720747994765809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389809505813831996510539 11084714258720747994765809)
                ·
                  refine ⟨8313535694040560996074357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11084714258720747994765809 8313535694040560996074357)
                  ·
                    refine ⟨779393971316302593381971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8313535694040560996074357 779393971316302593381971)
                    ·
                      rfl

theorem cell23_4553593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_4553593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553593 prefixEnd_4553593 := by exact prefixLift 4553593
  have htrace : WordTrace (prefixWord ++ tailWord_4553593) baseStart_4553593 baseEnd_4553593 := by
    simpa [prefixWord, tailWord_4553593, baseEnd_4553593] using wordTrace_append hprefix tailTrace_4553593
  have hstable : (prefixWord ++ tailWord_4553593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553593).length < 2 ^ (prefixWord ++ tailWord_4553593).sum := by decide
  have hdescent : baseEnd_4553593 < baseStart_4553593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553623 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 3, 4]
def baseStart_4553623 : Nat := 118140960795 + 4553623 * 2 ^ 59
def prefixEnd_4553623 : Nat := 4983230072969 + 3 ^ 40 * 4553623 * 2
def baseEnd_4553623 : Nat := 779399106122847554256925

theorem tailTrace_4553623 : CollatzResearch.WordTrace tailWord_4553623 prefixEnd_4553623 779399106122847554256925 := by
  unfold tailWord_4553623
  simp only [CollatzResearch.WordTrace]
  refine ⟨166084275182009042737897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110722850121339361825265015 166084275182009042737897523)
  ·
    refine ⟨249126412773013564106846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166084275182009042737897523 249126412773013564106846285)
    ·
      refine ⟨93422404789880086540067357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 249126412773013564106846285 93422404789880086540067357)
      ·
        refine ⟨35033401796205032452525259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93422404789880086540067357 35033401796205032452525259)
        ·
          refine ⟨52550102694307548678787889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35033401796205032452525259 52550102694307548678787889)
          ·
            refine ⟨39412577020730661509090917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52550102694307548678787889 39412577020730661509090917)
            ·
              refine ⟨7389858191386999032954547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39412577020730661509090917 7389858191386999032954547)
              ·
                refine ⟨11084787287080498549431821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7389858191386999032954547 11084787287080498549431821)
                ·
                  refine ⟨4156795232655186956036933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11084787287080498549431821 4156795232655186956036933)
                  ·
                    refine ⟨779399106122847554256925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156795232655186956036933 779399106122847554256925)
                    ·
                      rfl

theorem cell23_4553623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_4553623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553623 prefixEnd_4553623 := by exact prefixLift 4553623
  have htrace : WordTrace (prefixWord ++ tailWord_4553623) baseStart_4553623 baseEnd_4553623 := by
    simpa [prefixWord, tailWord_4553623, baseEnd_4553623] using wordTrace_append hprefix tailTrace_4553623
  have hstable : (prefixWord ++ tailWord_4553623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553623).length < 2 ^ (prefixWord ++ tailWord_4553623).sum := by decide
  have hdescent : baseEnd_4553623 < baseStart_4553623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553633 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4553633 : Nat := 118140960795 + 4553633 * 2 ^ 59
def prefixEnd_4553633 : Nat := 4983230072969 + 3 ^ 40 * 4553633 * 2
def baseEnd_4553633 : Nat := 2338202453175087623645729

theorem tailTrace_4553633 : CollatzResearch.WordTrace tailWord_4553633 prefixEnd_4553633 2338202453175087623645729 := by
  unfold tailWord_4553633
  simp only [CollatzResearch.WordTrace]
  refine ⟨166084639911972814445761553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110723093274648542963841035 166084639911972814445761553)
  ·
    refine ⟨124563479933979610834321165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166084639911972814445761553 124563479933979610834321165)
    ·
      refine ⟨46711304975242354062870437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124563479933979610834321165 46711304975242354062870437)
      ·
        refine ⟨8758369682857941386788207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46711304975242354062870437 8758369682857941386788207)
        ·
          refine ⟨13137554524286912080182311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8758369682857941386788207 13137554524286912080182311)
          ·
            refine ⟨19706331786430368120273467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13137554524286912080182311 19706331786430368120273467)
            ·
              refine ⟨29559497679645552180410201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19706331786430368120273467 29559497679645552180410201)
              ·
                refine ⟨22169623259734164135307651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29559497679645552180410201 22169623259734164135307651)
                ·
                  refine ⟨33254434889601246202961477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22169623259734164135307651 33254434889601246202961477)
                  ·
                    refine ⟨6235206541800233663055277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33254434889601246202961477 6235206541800233663055277)
                    ·
                      refine ⟨2338202453175087623645729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235206541800233663055277 2338202453175087623645729)
                      ·
                        rfl

theorem cell23_4553633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4553633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553633 prefixEnd_4553633 := by exact prefixLift 4553633
  have htrace : WordTrace (prefixWord ++ tailWord_4553633) baseStart_4553633 baseEnd_4553633 := by
    simpa [prefixWord, tailWord_4553633, baseEnd_4553633] using wordTrace_append hprefix tailTrace_4553633
  have hstable : (prefixWord ++ tailWord_4553633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553633).length < 2 ^ (prefixWord ++ tailWord_4553633).sum := by decide
  have hdescent : baseEnd_4553633 < baseStart_4553633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553657 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 1, 4]
def baseStart_4553657 : Nat := 118140960795 + 4553657 * 2 ^ 59
def prefixEnd_4553657 : Nat := 4983230072969 + 3 ^ 40 * 4553657 * 2
def baseEnd_4553657 : Nat := 779404925570265176581873

theorem tailTrace_4553657 : CollatzResearch.WordTrace tailWord_4553657 prefixEnd_4553657 779404925570265176581873 := by
  unfold tailWord_4553657
  simp only [CollatzResearch.WordTrace]
  refine ⟨166085515263885866544635225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110723676842590577696423483 166085515263885866544635225)
  ·
    refine ⟨124564136447914399908476419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166085515263885866544635225 124564136447914399908476419)
    ·
      refine ⟨186846204671871599862714629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124564136447914399908476419 186846204671871599862714629)
      ·
        refine ⟨35033663375975924974258993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186846204671871599862714629 35033663375975924974258993)
        ·
          refine ⟨26275247531981943730694245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35033663375975924974258993 26275247531981943730694245)
          ·
            refine ⟨4926608912246614449505171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26275247531981943730694245 4926608912246614449505171)
            ·
              refine ⟨7389913368369921674257757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926608912246614449505171 7389913368369921674257757)
              ·
                refine ⟨2771217513138720627846659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7389913368369921674257757 2771217513138720627846659)
                ·
                  refine ⟨4156826269708080941769989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771217513138720627846659 4156826269708080941769989)
                  ·
                    refine ⟨779404925570265176581873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156826269708080941769989 779404925570265176581873)
                    ·
                      rfl

theorem cell23_4553657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_4553657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553657 prefixEnd_4553657 := by exact prefixLift 4553657
  have htrace : WordTrace (prefixWord ++ tailWord_4553657) baseStart_4553657 baseEnd_4553657 := by
    simpa [prefixWord, tailWord_4553657, baseEnd_4553657] using wordTrace_append hprefix tailTrace_4553657
  have hstable : (prefixWord ++ tailWord_4553657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553657).length < 2 ^ (prefixWord ++ tailWord_4553657).sum := by decide
  have hdescent : baseEnd_4553657 < baseStart_4553657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553713 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_4553713 : Nat := 118140960795 + 4553713 * 2 ^ 59
def prefixEnd_4553713 : Nat := 4983230072969 + 3 ^ 40 * 4553713 * 2
def baseEnd_4553713 : Nat := 779414510542482436881787

theorem tailTrace_4553713 : CollatzResearch.WordTrace tailWord_4553713 prefixEnd_4553713 779414510542482436881787 := by
  unfold tailWord_4553713
  simp only [CollatzResearch.WordTrace]
  refine ⟨166087557751682988108673793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110725038501121992072449195 166087557751682988108673793)
  ·
    refine ⟨124565668313762241081505345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166087557751682988108673793 124565668313762241081505345)
    ·
      refine ⟨93424251235321680811129009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124565668313762241081505345 93424251235321680811129009)
      ·
        refine ⟨70068188426491260608346757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93424251235321680811129009 70068188426491260608346757)
        ·
          refine ⟨13137785329967111364065017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70068188426491260608346757 13137785329967111364065017)
          ·
            refine ⟨9853338997475333523048763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13137785329967111364065017 9853338997475333523048763)
            ·
              refine ⟨14780008496213000284573145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9853338997475333523048763 14780008496213000284573145)
              ·
                refine ⟨11085006372159750213429859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14780008496213000284573145 11085006372159750213429859)
                ·
                  refine ⟨16627509558239625320144789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11085006372159750213429859 16627509558239625320144789)
                  ·
                    refine ⟨779414510542482436881787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16627509558239625320144789 779414510542482436881787)
                    ·
                      rfl

theorem cell23_4553713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_4553713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553713 prefixEnd_4553713 := by exact prefixLift 4553713
  have htrace : WordTrace (prefixWord ++ tailWord_4553713) baseStart_4553713 baseEnd_4553713 := by
    simpa [prefixWord, tailWord_4553713, baseEnd_4553713] using wordTrace_append hprefix tailTrace_4553713
  have hstable : (prefixWord ++ tailWord_4553713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553713).length < 2 ^ (prefixWord ++ tailWord_4553713).sum := by decide
  have hdescent : baseEnd_4553713 < baseStart_4553713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553753 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_4553753 : Nat := 118140960795 + 4553753 * 2 ^ 59
def prefixEnd_4553753 : Nat := 4983230072969 + 3 ^ 40 * 4553753 * 2
def baseEnd_4553753 : Nat := 2338264070853627154145177

theorem tailTrace_4553753 : CollatzResearch.WordTrace tailWord_4553753 prefixEnd_4553753 2338264070853627154145177 := by
  unfold tailWord_4553753
  simp only [CollatzResearch.WordTrace]
  refine ⟨166089016671538074940129913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110726011114358716626753275 166089016671538074940129913)
  ·
    refine ⟨124566762503653556205097435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166089016671538074940129913 124566762503653556205097435)
    ·
      refine ⟨186850143755480334307646153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124566762503653556205097435 186850143755480334307646153)
      ·
        refine ⟨140137607816610250730734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186850143755480334307646153 140137607816610250730734615)
        ·
          refine ⟨210206411724915376096101923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140137607816610250730734615 210206411724915376096101923)
          ·
            refine ⟨315309617587373064144152885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210206411724915376096101923 315309617587373064144152885)
            ·
              refine ⟨29560276648816224763514333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 315309617587373064144152885 29560276648816224763514333)
              ·
                refine ⟨11085103743306084286317875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29560276648816224763514333 11085103743306084286317875)
                ·
                  refine ⟨16627655614959126429476813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11085103743306084286317875 16627655614959126429476813)
                  ·
                    refine ⟨6235370855609672411053805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16627655614959126429476813 6235370855609672411053805)
                    ·
                      refine ⟨2338264070853627154145177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6235370855609672411053805 2338264070853627154145177)
                      ·
                        rfl

theorem cell23_4553753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_4553753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553753 prefixEnd_4553753 := by exact prefixLift 4553753
  have htrace : WordTrace (prefixWord ++ tailWord_4553753) baseStart_4553753 baseEnd_4553753 := by
    simpa [prefixWord, tailWord_4553753, baseEnd_4553753] using wordTrace_append hprefix tailTrace_4553753
  have hstable : (prefixWord ++ tailWord_4553753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553753).length < 2 ^ (prefixWord ++ tailWord_4553753).sum := by decide
  have hdescent : baseEnd_4553753 < baseStart_4553753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553813 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4553813 : Nat := 118140960795 + 4553813 * 2 ^ 59
def prefixEnd_4553813 : Nat := 4983230072969 + 3 ^ 40 * 4553813 * 2
def baseEnd_4553813 : Nat := 2338294879692896919394901

theorem tailTrace_4553813 : CollatzResearch.WordTrace tailWord_4553813 prefixEnd_4553813 2338294879692896919394901 := by
  unfold tailWord_4553813
  simp only [CollatzResearch.WordTrace]
  refine ⟨166091205051320705187314093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110727470034213803458209395 166091205051320705187314093)
  ·
    refine ⟨62284201894245264445242785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166091205051320705187314093 62284201894245264445242785)
    ·
      refine ⟨46713151420683948333932089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62284201894245264445242785 46713151420683948333932089)
      ·
        refine ⟨35034863565512961250449067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46713151420683948333932089 35034863565512961250449067)
        ·
          refine ⟨52552295348269441875673601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35034863565512961250449067 52552295348269441875673601)
          ·
            refine ⟨39414221511202081406755201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52552295348269441875673601 39414221511202081406755201)
            ·
              refine ⟨29560666133401561055066401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39414221511202081406755201 29560666133401561055066401)
              ·
                refine ⟨22170499600051170791299801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29560666133401561055066401 22170499600051170791299801)
                ·
                  refine ⟨16627874700038378093474851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22170499600051170791299801 16627874700038378093474851)
                  ·
                    refine ⟨24941812050057567140212277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16627874700038378093474851 24941812050057567140212277)
                    ·
                      refine ⟨2338294879692896919394901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24941812050057567140212277 2338294879692896919394901)
                      ·
                        rfl

theorem cell23_4553813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4553813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553813 prefixEnd_4553813 := by exact prefixLift 4553813
  have htrace : WordTrace (prefixWord ++ tailWord_4553813) baseStart_4553813 baseEnd_4553813 := by
    simpa [prefixWord, tailWord_4553813, baseEnd_4553813] using wordTrace_append hprefix tailTrace_4553813
  have hstable : (prefixWord ++ tailWord_4553813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553813).length < 2 ^ (prefixWord ++ tailWord_4553813).sum := by decide
  have hdescent : baseEnd_4553813 < baseStart_4553813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553863 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 6, 5]
def baseStart_4553863 : Nat := 118140960795 + 4553863 * 2 ^ 59
def prefixEnd_4553863 : Nat := 4983230072969 + 3 ^ 40 * 4553863 * 2
def baseEnd_4553863 : Nat := 779440184575207241256557

theorem tailTrace_4553863 : CollatzResearch.WordTrace tailWord_4553863 prefixEnd_4553863 779440184575207241256557 := by
  unfold tailWord_4553863
  simp only [CollatzResearch.WordTrace]
  refine ⟨166093028701139563726634243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110728685800759709151089495 166093028701139563726634243)
  ·
    refine ⟨249139543051709345589951365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166093028701139563726634243 249139543051709345589951365)
    ·
      refine ⟨46713664322195502298115881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 249139543051709345589951365 46713664322195502298115881)
      ·
        refine ⟨35035248241646626723586911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46713664322195502298115881 35035248241646626723586911)
        ·
          refine ⟨52552872362469940085380367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35035248241646626723586911 52552872362469940085380367)
          ·
            refine ⟨78829308543704910128070551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52552872362469940085380367 78829308543704910128070551)
            ·
              refine ⟨118243962815557365192105827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78829308543704910128070551 118243962815557365192105827)
              ·
                refine ⟨177365944223336047788158741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118243962815557365192105827 177365944223336047788158741)
                ·
                  refine ⟨8314028635468877240069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177365944223336047788158741 8314028635468877240069941)
                  ·
                    refine ⟨779440184575207241256557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314028635468877240069941 779440184575207241256557)
                    ·
                      rfl

theorem cell23_4553863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_4553863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553863 prefixEnd_4553863 := by exact prefixLift 4553863
  have htrace : WordTrace (prefixWord ++ tailWord_4553863) baseStart_4553863 baseEnd_4553863 := by
    simpa [prefixWord, tailWord_4553863, baseEnd_4553863] using wordTrace_append hprefix tailTrace_4553863
  have hstable : (prefixWord ++ tailWord_4553863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553863).length < 2 ^ (prefixWord ++ tailWord_4553863).sum := by decide
  have hdescent : baseEnd_4553863 < baseStart_4553863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553880 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_4553880 : Nat := 118140960795 + 4553880 * 2 ^ 59
def prefixEnd_4553880 : Nat := 4983230072969 + 3 ^ 40 * 4553880 * 2
def baseEnd_4553880 : Nat := 779443094298916052419031

theorem tailTrace_4553880 : CollatzResearch.WordTrace tailWord_4553880 prefixEnd_4553880 779443094298916052419031 := by
  unfold tailWord_4553880
  simp only [CollatzResearch.WordTrace]
  refine ⟨83046824371038987815001547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110729099161385317086668729 83046824371038987815001547)
  ·
    refine ⟨124570236556558481722502321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83046824371038987815001547 124570236556558481722502321)
    ·
      refine ⟨93427677417418861291876741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124570236556558481722502321 93427677417418861291876741)
      ·
        refine ⟨17517689515766036492226889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93427677417418861291876741 17517689515766036492226889)
        ·
          refine ⟨13138267136824527369170167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17517689515766036492226889 13138267136824527369170167)
          ·
            refine ⟨19707400705236791053755251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13138267136824527369170167 19707400705236791053755251)
            ·
              refine ⟨29561101057855186580632877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19707400705236791053755251 29561101057855186580632877)
              ·
                refine ⟨11085412896695694967737329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29561101057855186580632877 11085412896695694967737329)
                ·
                  refine ⟨8314059672521771225802997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11085412896695694967737329 8314059672521771225802997)
                  ·
                    refine ⟨779443094298916052419031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314059672521771225802997 779443094298916052419031)
                    ·
                      rfl

theorem cell23_4553880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_4553880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553880 prefixEnd_4553880 := by exact prefixLift 4553880
  have htrace : WordTrace (prefixWord ++ tailWord_4553880) baseStart_4553880 baseEnd_4553880 := by
    simpa [prefixWord, tailWord_4553880, baseEnd_4553880] using wordTrace_append hprefix tailTrace_4553880
  have hstable : (prefixWord ++ tailWord_4553880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553880).length < 2 ^ (prefixWord ++ tailWord_4553880).sum := by decide
  have hdescent : baseEnd_4553880 < baseStart_4553880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553901 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 5]
def baseStart_4553901 : Nat := 118140960795 + 4553901 * 2 ^ 59
def prefixEnd_4553901 : Nat := 4983230072969 + 3 ^ 40 * 4553901 * 2
def baseEnd_4553901 : Nat := 259815562887832508343833

theorem tailTrace_4553901 : CollatzResearch.WordTrace tailWord_4553901 prefixEnd_4553901 259815562887832508343833 := by
  unfold tailWord_4553901
  simp only [CollatzResearch.WordTrace]
  refine ⟨166094414675001896216517557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110729609783334597477678371 166094414675001896216517557)
  ·
    refine ⟨15571351375781427770298521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166094414675001896216517557 15571351375781427770298521)
    ·
      refine ⟨11678513531836070827723891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15571351375781427770298521 11678513531836070827723891)
      ·
        refine ⟨17517770297754106241585837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11678513531836070827723891 17517770297754106241585837)
        ·
          refine ⟨6569163861657789840594689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17517770297754106241585837 6569163861657789840594689)
          ·
            refine ⟨4926872896243342380446017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6569163861657789840594689 4926872896243342380446017)
            ·
              refine ⟨3695154672182506785334513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926872896243342380446017 3695154672182506785334513)
              ·
                refine ⟨2771366004136880089000885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695154672182506785334513 2771366004136880089000885)
                ·
                  refine ⟨259815562887832508343833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2771366004136880089000885 259815562887832508343833)
                  ·
                    rfl

theorem cell23_4553901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_4553901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553901 prefixEnd_4553901 := by exact prefixLift 4553901
  have htrace : WordTrace (prefixWord ++ tailWord_4553901) baseStart_4553901 baseEnd_4553901 := by
    simpa [prefixWord, tailWord_4553901, baseEnd_4553901] using wordTrace_append hprefix tailTrace_4553901
  have hstable : (prefixWord ++ tailWord_4553901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553901).length < 2 ^ (prefixWord ++ tailWord_4553901).sum := by decide
  have hdescent : baseEnd_4553901 < baseStart_4553901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553934 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4553934 : Nat := 118140960795 + 4553934 * 2 ^ 59
def prefixEnd_4553934 : Nat := 4983230072969 + 3 ^ 40 * 4553934 * 2
def baseEnd_4553934 : Nat := 2338357010852090945981845

theorem tailTrace_4553934 : CollatzResearch.WordTrace tailWord_4553934 prefixEnd_4553934 2338357010852090945981845 := by
  unfold tailWord_4553934
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761952285485292856558607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110730412189254895234979237 20761952285485292856558607)
  ·
    refine ⟨31142928428227939284837911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20761952285485292856558607 31142928428227939284837911)
    ·
      refine ⟨46714392642341908927256867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31142928428227939284837911 46714392642341908927256867)
      ·
        refine ⟨70071588963512863390885301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46714392642341908927256867 70071588963512863390885301)
        ·
          refine ⟨6569211465329330942895497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70071588963512863390885301 6569211465329330942895497)
          ·
            refine ⟨4926908598996998207171623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6569211465329330942895497 4926908598996998207171623)
            ·
              refine ⟨7390362898495497310757435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4926908598996998207171623 7390362898495497310757435)
              ·
                refine ⟨11085544347743245966136153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7390362898495497310757435 11085544347743245966136153)
                ·
                  refine ⟨8314158260807434474602115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11085544347743245966136153 8314158260807434474602115)
                  ·
                    refine ⟨12471237391211151711903173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8314158260807434474602115 12471237391211151711903173)
                    ·
                      refine ⟨2338357010852090945981845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12471237391211151711903173 2338357010852090945981845)
                      ·
                        rfl

theorem cell23_4553934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4553934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553934 prefixEnd_4553934 := by exact prefixLift 4553934
  have htrace : WordTrace (prefixWord ++ tailWord_4553934) baseStart_4553934 baseEnd_4553934 := by
    simpa [prefixWord, tailWord_4553934, baseEnd_4553934] using wordTrace_append hprefix tailTrace_4553934
  have hstable : (prefixWord ++ tailWord_4553934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553934).length < 2 ^ (prefixWord ++ tailWord_4553934).sum := by decide
  have hdescent : baseEnd_4553934 < baseStart_4553934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4553987 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 1, 5]
def baseStart_4553987 : Nat := 118140960795 + 4553987 * 2 ^ 59
def prefixEnd_4553987 : Nat := 4983230072969 + 3 ^ 40 * 4553987 * 2
def baseEnd_4553987 : Nat := 779461408442259746206367

theorem tailTrace_4553987 : CollatzResearch.WordTrace tailWord_4553987 prefixEnd_4553987 779461408442259746206367 := by
  unfold tailWord_4553987
  simp only [CollatzResearch.WordTrace]
  refine ⟨166097551352690332904148215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110731700901793555269432143 166097551352690332904148215)
  ·
    refine ⟨249146327029035499356222323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166097551352690332904148215 249146327029035499356222323)
    ·
      refine ⟨373719490543553249034333485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249146327029035499356222323 373719490543553249034333485)
      ·
        refine ⟨140144808953832468387875057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373719490543553249034333485 140144808953832468387875057)
        ·
          refine ⟨105108606715374351290906293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140144808953832468387875057 105108606715374351290906293)
          ·
            refine ⟨9853931879566345433522465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105108606715374351290906293 9853931879566345433522465)
            ·
              refine ⟨7390448909674759075141849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9853931879566345433522465 7390448909674759075141849)
              ·
                refine ⟨5542836682256069306356387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7390448909674759075141849 5542836682256069306356387)
                ·
                  refine ⟨8314255023384103959534581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542836682256069306356387 8314255023384103959534581)
                  ·
                    refine ⟨779461408442259746206367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8314255023384103959534581 779461408442259746206367)
                    ·
                      rfl

theorem cell23_4553987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 5].length) (baseStart_4553987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4553987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4553987 prefixEnd_4553987 := by exact prefixLift 4553987
  have htrace : WordTrace (prefixWord ++ tailWord_4553987) baseStart_4553987 baseEnd_4553987 := by
    simpa [prefixWord, tailWord_4553987, baseEnd_4553987] using wordTrace_append hprefix tailTrace_4553987
  have hstable : (prefixWord ++ tailWord_4553987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4553987).length < 2 ^ (prefixWord ++ tailWord_4553987).sum := by decide
  have hdescent : baseEnd_4553987 < baseStart_4553987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4553987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
