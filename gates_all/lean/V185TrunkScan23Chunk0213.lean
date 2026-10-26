import V185TrunkScan23Chunk0212

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1260225 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1260225 : Nat := 118140960795 + 1260225 * 2 ^ 59
def prefixEnd_1260225 : Nat := 4983230072969 + 3 ^ 40 * 1260225 * 2
def baseEnd_1260225 : Nat := 647101157812437097591837

theorem tailTrace_1260225 : CollatzResearch.WordTrace tailWord_1260225 prefixEnd_1260225 647101157812437097591837 := by
  unfold tailWord_1260225
  simp only [CollatzResearch.WordTrace]
  refine ⟨45964181859427529139830129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30642787906285019426553419 45964181859427529139830129)
  ·
    refine ⟨34473136394570646854872597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45964181859427529139830129 34473136394570646854872597)
    ·
      refine ⟨1615928268495499071322153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34473136394570646854872597 1615928268495499071322153)
      ·
        refine ⟨1211946201371624303491615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615928268495499071322153 1211946201371624303491615)
        ·
          refine ⟨1817919302057436455237423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211946201371624303491615 1817919302057436455237423)
          ·
            refine ⟨2726878953086154682856135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1817919302057436455237423 2726878953086154682856135)
            ·
              refine ⟨4090318429629232024284203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726878953086154682856135 4090318429629232024284203)
              ·
                refine ⟨6135477644443848036426305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090318429629232024284203 6135477644443848036426305)
                ·
                  refine ⟨4601608233332886027319729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135477644443848036426305 4601608233332886027319729)
                  ·
                    refine ⟨3451206174999664520489797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4601608233332886027319729 3451206174999664520489797)
                    ·
                      refine ⟨647101157812437097591837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3451206174999664520489797 647101157812437097591837)
                      ·
                        rfl

theorem cell23_1260225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1260225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260225 prefixEnd_1260225 := by exact prefixLift 1260225
  have htrace : WordTrace (prefixWord ++ tailWord_1260225) baseStart_1260225 baseEnd_1260225 := by
    simpa [prefixWord, tailWord_1260225, baseEnd_1260225] using wordTrace_append hprefix tailTrace_1260225
  have hstable : (prefixWord ++ tailWord_1260225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260225).length < 2 ^ (prefixWord ++ tailWord_1260225).sum := by decide
  have hdescent : baseEnd_1260225 < baseStart_1260225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260228 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1260228 : Nat := 118140960795 + 1260228 * 2 ^ 59
def prefixEnd_1260228 : Nat := 4983230072969 + 3 ^ 40 * 1260228 * 2
def baseEnd_1260228 : Nat := 647102698254400585854323

theorem tailTrace_1260228 : CollatzResearch.WordTrace tailWord_1260228 prefixEnd_1260228 647102698254400585854323 := by
  unfold tailWord_1260228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22982145639208330326094669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30642860852277773768126225 22982145639208330326094669)
  ·
    refine ⟨8618304614703123872285501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22982145639208330326094669 8618304614703123872285501)
    ·
      refine ⟨3231864230513671452107063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8618304614703123872285501 3231864230513671452107063)
      ·
        refine ⟨4847796345770507178160595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3231864230513671452107063 4847796345770507178160595)
        ·
          refine ⟨7271694518655760767240893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4847796345770507178160595 7271694518655760767240893)
          ·
            refine ⟨2726885444495910287715335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7271694518655760767240893 2726885444495910287715335)
            ·
              refine ⟨4090328166743865431573003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2726885444495910287715335 4090328166743865431573003)
              ·
                refine ⟨6135492250115798147359505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4090328166743865431573003 6135492250115798147359505)
                ·
                  refine ⟨4601619187586848610519629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6135492250115798147359505 4601619187586848610519629)
                  ·
                    refine ⟨1725607195345068228944861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4601619187586848610519629 1725607195345068228944861)
                    ·
                      refine ⟨647102698254400585854323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1725607195345068228944861 647102698254400585854323)
                      ·
                        rfl

theorem cell23_1260228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1260228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260228 prefixEnd_1260228 := by exact prefixLift 1260228
  have htrace : WordTrace (prefixWord ++ tailWord_1260228) baseStart_1260228 baseEnd_1260228 := by
    simpa [prefixWord, tailWord_1260228, baseEnd_1260228] using wordTrace_append hprefix tailTrace_1260228
  have hstable : (prefixWord ++ tailWord_1260228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260228).length < 2 ^ (prefixWord ++ tailWord_1260228).sum := by decide
  have hdescent : baseEnd_1260228 < baseStart_1260228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260248 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_1260248 : Nat := 118140960795 + 1260248 * 2 ^ 59
def prefixEnd_1260248 : Nat := 4983230072969 + 3 ^ 40 * 1260248 * 2
def baseEnd_1260248 : Nat := 215704322622496835868077

theorem tailTrace_1260248 : CollatzResearch.WordTrace tailWord_1260248 prefixEnd_1260248 215704322622496835868077 := by
  unfold tailWord_1260248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22982510369172102033958699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30643347158896136045278265 22982510369172102033958699)
  ·
    refine ⟨34473765553758153050938049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22982510369172102033958699 34473765553758153050938049)
    ·
      refine ⟨25855324165318614788203537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34473765553758153050938049 25855324165318614788203537)
      ·
        refine ⟨19391493123988961091152653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25855324165318614788203537 19391493123988961091152653)
        ·
          refine ⟨7271809921495860409182245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19391493123988961091152653 7271809921495860409182245)
          ·
            refine ⟨1363464360280473826721671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7271809921495860409182245 1363464360280473826721671)
            ·
              refine ⟨2045196540420710740082507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363464360280473826721671 2045196540420710740082507)
              ·
                refine ⟨3067794810631066110123761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045196540420710740082507 3067794810631066110123761)
                ·
                  refine ⟨2300846107973299582592821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3067794810631066110123761 2300846107973299582592821)
                  ·
                    refine ⟨215704322622496835868077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2300846107973299582592821 215704322622496835868077)
                    ·
                      rfl

theorem cell23_1260248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_1260248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260248 prefixEnd_1260248 := by exact prefixLift 1260248
  have htrace : WordTrace (prefixWord ++ tailWord_1260248) baseStart_1260248 baseEnd_1260248 := by
    simpa [prefixWord, tailWord_1260248, baseEnd_1260248] using wordTrace_append hprefix tailTrace_1260248
  have hstable : (prefixWord ++ tailWord_1260248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260248).length < 2 ^ (prefixWord ++ tailWord_1260248).sum := by decide
  have hdescent : baseEnd_1260248 < baseStart_1260248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260372 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1260372 : Nat := 118140960795 + 1260372 * 2 ^ 59
def prefixEnd_1260372 : Nat := 4983230072969 + 3 ^ 40 * 1260372 * 2
def baseEnd_1260372 : Nat := 215725546489549340817887

theorem tailTrace_1260372 : CollatzResearch.WordTrace tailWord_1260372 prefixEnd_1260372 215725546489549340817887 := by
  unfold tailWord_1260372
  simp only [CollatzResearch.WordTrace]
  refine ⟨22984771694947486622715685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30646362259929982163620913 22984771694947486622715685)
  ·
    refine ⟨4309644692802653741759191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22984771694947486622715685 4309644692802653741759191)
    ·
      refine ⟨6464467039203980612638787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4309644692802653741759191 6464467039203980612638787)
      ·
        refine ⟨9696700558805970918958181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6464467039203980612638787 9696700558805970918958181)
        ·
          refine ⟨1818131354776119547304659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9696700558805970918958181 1818131354776119547304659)
          ·
            refine ⟨2727197032164179320956989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818131354776119547304659 2727197032164179320956989)
            ·
              refine ⟨1022698887061567245358871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2727197032164179320956989 1022698887061567245358871)
              ·
                refine ⟨1534048330592350868038307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1022698887061567245358871 1534048330592350868038307)
                ·
                  refine ⟨2301072495888526302057461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534048330592350868038307 2301072495888526302057461)
                  ·
                    refine ⟨215725546489549340817887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2301072495888526302057461 215725546489549340817887)
                    ·
                      rfl

theorem cell23_1260372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1260372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260372 prefixEnd_1260372 := by exact prefixLift 1260372
  have htrace : WordTrace (prefixWord ++ tailWord_1260372) baseStart_1260372 baseEnd_1260372 := by
    simpa [prefixWord, tailWord_1260372, baseEnd_1260372] using wordTrace_append hprefix tailTrace_1260372
  have hstable : (prefixWord ++ tailWord_1260372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260372).length < 2 ^ (prefixWord ++ tailWord_1260372).sum := by decide
  have hdescent : baseEnd_1260372 < baseStart_1260372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260378 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1260378 : Nat := 118140960795 + 1260378 * 2 ^ 59
def prefixEnd_1260378 : Nat := 4983230072969 + 3 ^ 40 * 1260378 * 2
def baseEnd_1260378 : Nat := 647179720352574998978633

theorem tailTrace_1260378 : CollatzResearch.WordTrace tailWord_1260378 prefixEnd_1260378 647179720352574998978633 := by
  unfold tailWord_1260378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492440556968309067537447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30646508151915490846766525 11492440556968309067537447)
  ·
    refine ⟨17238660835452463601306171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492440556968309067537447 17238660835452463601306171)
    ·
      refine ⟨25857991253178695401959257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17238660835452463601306171 25857991253178695401959257)
      ·
        refine ⟨19393493439884021551469443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25857991253178695401959257 19393493439884021551469443)
        ·
          refine ⟨29090240159826032327204165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19393493439884021551469443 29090240159826032327204165)
          ·
            refine ⟨5454420029967381061350781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29090240159826032327204165 5454420029967381061350781)
            ·
              refine ⟨2045407511237767898006543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5454420029967381061350781 2045407511237767898006543)
              ·
                refine ⟨3068111266856651847009815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045407511237767898006543 3068111266856651847009815)
                ·
                  refine ⟨4602166900284977770514723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068111266856651847009815 4602166900284977770514723)
                  ·
                    refine ⟨6903250350427466655772085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4602166900284977770514723 6903250350427466655772085)
                    ·
                      refine ⟨647179720352574998978633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6903250350427466655772085 647179720352574998978633)
                      ·
                        rfl

theorem cell23_1260378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1260378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260378 prefixEnd_1260378 := by exact prefixLift 1260378
  have htrace : WordTrace (prefixWord ++ tailWord_1260378) baseStart_1260378 baseEnd_1260378 := by
    simpa [prefixWord, tailWord_1260378, baseEnd_1260378] using wordTrace_append hprefix tailTrace_1260378
  have hstable : (prefixWord ++ tailWord_1260378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260378).length < 2 ^ (prefixWord ++ tailWord_1260378).sum := by decide
  have hdescent : baseEnd_1260378 < baseStart_1260378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260405 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1260405 : Nat := 118140960795 + 1260405 * 2 ^ 59
def prefixEnd_1260405 : Nat := 4983230072969 + 3 ^ 40 * 1260405 * 2
def baseEnd_1260405 : Nat := 647193584330246393341009

theorem tailTrace_1260405 : CollatzResearch.WordTrace tailWord_1260405 prefixEnd_1260405 647193584330246393341009 := by
  unfold tailWord_1260405
  simp only [CollatzResearch.WordTrace]
  refine ⟨45970746998775419881382669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30647164665850279920921779 45970746998775419881382669)
  ·
    refine ⟨17239030124540782455518501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45970746998775419881382669 17239030124540782455518501)
    ·
      refine ⟨3232318148351396710409719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17239030124540782455518501 3232318148351396710409719)
      ·
        refine ⟨4848477222527095065614579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3232318148351396710409719 4848477222527095065614579)
        ·
          refine ⟨7272715833790642598421869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4848477222527095065614579 7272715833790642598421869)
          ·
            refine ⟨2727268437671490974408201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7272715833790642598421869 2727268437671490974408201)
            ·
              refine ⟨2045451328253618230806151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2727268437671490974408201 2045451328253618230806151)
              ·
                refine ⟨3068176992380427346209227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045451328253618230806151 3068176992380427346209227)
                ·
                  refine ⟨4602265488570641019313841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3068176992380427346209227 4602265488570641019313841)
                  ·
                    refine ⟨3451699116427980764485381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4602265488570641019313841 3451699116427980764485381)
                    ·
                      refine ⟨647193584330246393341009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3451699116427980764485381 647193584330246393341009)
                      ·
                        rfl

theorem cell23_1260405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1260405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260405 prefixEnd_1260405 := by exact prefixLift 1260405
  have htrace : WordTrace (prefixWord ++ tailWord_1260405) baseStart_1260405 baseEnd_1260405 := by
    simpa [prefixWord, tailWord_1260405, baseEnd_1260405] using wordTrace_append hprefix tailTrace_1260405
  have hstable : (prefixWord ++ tailWord_1260405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260405).length < 2 ^ (prefixWord ++ tailWord_1260405).sum := by decide
  have hdescent : baseEnd_1260405 < baseStart_1260405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260426 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1260426 : Nat := 118140960795 + 1260426 * 2 ^ 59
def prefixEnd_1260426 : Nat := 4983230072969 + 3 ^ 40 * 1260426 * 2
def baseEnd_1260426 : Nat := 647204367423990811178413

theorem tailTrace_1260426 : CollatzResearch.WordTrace tailWord_1260426 prefixEnd_1260426 647204367423990811178413 := by
  unfold tailWord_1260426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492878232924835116974283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30647675287799560311931421 11492878232924835116974283)
  ·
    refine ⟨17239317349387252675461425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492878232924835116974283 17239317349387252675461425)
    ·
      refine ⟨12929488012040439506596069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17239317349387252675461425 12929488012040439506596069)
      ·
        refine ⟨2424279002257582407486763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12929488012040439506596069 2424279002257582407486763)
        ·
          refine ⟨3636418503386373611230145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2424279002257582407486763 3636418503386373611230145)
          ·
            refine ⟨2727313877539780208422609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3636418503386373611230145 2727313877539780208422609)
            ·
              refine ⟨2045485408154835156316957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2727313877539780208422609 2045485408154835156316957)
              ·
                refine ⟨767057028058063183618859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2045485408154835156316957 767057028058063183618859)
                ·
                  refine ⟨1150585542087094775428289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767057028058063183618859 1150585542087094775428289)
                  ·
                    refine ⟨862939156565321081571217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1150585542087094775428289 862939156565321081571217)
                    ·
                      refine ⟨647204367423990811178413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 862939156565321081571217 647204367423990811178413)
                      ·
                        rfl

theorem cell23_1260426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1260426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260426 prefixEnd_1260426 := by exact prefixLift 1260426
  have htrace : WordTrace (prefixWord ++ tailWord_1260426) baseStart_1260426 baseEnd_1260426 := by
    simpa [prefixWord, tailWord_1260426, baseEnd_1260426] using wordTrace_append hprefix tailTrace_1260426
  have hstable : (prefixWord ++ tailWord_1260426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260426).length < 2 ^ (prefixWord ++ tailWord_1260426).sum := by decide
  have hdescent : baseEnd_1260426 < baseStart_1260426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260442 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1260442 : Nat := 118140960795 + 1260442 * 2 ^ 59
def prefixEnd_1260442 : Nat := 4983230072969 + 3 ^ 40 * 1260442 * 2
def baseEnd_1260442 : Nat := 647212583114462748578339

theorem tailTrace_1260442 : CollatzResearch.WordTrace tailWord_1260442 prefixEnd_1260442 647212583114462748578339 := by
  unfold tailWord_1260442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493024124910343800119895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30648064333094250133653053 11493024124910343800119895)
  ·
    refine ⟨17239536187365515700179843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493024124910343800119895 17239536187365515700179843)
    ·
      refine ⟨25859304281048273550269765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17239536187365515700179843 25859304281048273550269765)
      ·
        refine ⟨4848619552696551290675581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25859304281048273550269765 4848619552696551290675581)
        ·
          refine ⟨1818232332261206734003343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4848619552696551290675581 1818232332261206734003343)
          ·
            refine ⟨2727348498391810101005015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818232332261206734003343 2727348498391810101005015)
            ·
              refine ⟨4091022747587715151507523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2727348498391810101005015 4091022747587715151507523)
              ·
                refine ⟨6136534121381572727261285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4091022747587715151507523 6136534121381572727261285)
                ·
                  refine ⟨1150600147759044886361491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6136534121381572727261285 1150600147759044886361491)
                  ·
                    refine ⟨1725900221638567329542237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150600147759044886361491 1725900221638567329542237)
                    ·
                      refine ⟨647212583114462748578339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1725900221638567329542237 647212583114462748578339)
                      ·
                        rfl

theorem cell23_1260442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1260442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260442 prefixEnd_1260442 := by exact prefixLift 1260442
  have htrace : WordTrace (prefixWord ++ tailWord_1260442) baseStart_1260442 baseEnd_1260442 := by
    simpa [prefixWord, tailWord_1260442, baseEnd_1260442] using wordTrace_append hprefix tailTrace_1260442
  have hstable : (prefixWord ++ tailWord_1260442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260442).length < 2 ^ (prefixWord ++ tailWord_1260442).sum := by decide
  have hdescent : baseEnd_1260442 < baseStart_1260442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260505 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 7]
def baseStart_1260505 : Nat := 118140960795 + 1260505 * 2 ^ 59
def prefixEnd_1260505 : Nat := 4983230072969 + 3 ^ 40 * 1260505 * 2
def baseEnd_1260505 : Nat := 71916103599521778010061

theorem tailTrace_1260505 : CollatzResearch.WordTrace tailWord_1260505 prefixEnd_1260505 71916103599521778010061 := by
  unfold tailWord_1260505
  simp only [CollatzResearch.WordTrace]
  refine ⟨45974394298413136960022969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30649596198942091306681979 45974394298413136960022969)
  ·
    refine ⟨34480795723809852720017227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45974394298413136960022969 34480795723809852720017227)
    ·
      refine ⟨51721193585714779080025841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34480795723809852720017227 51721193585714779080025841)
      ·
        refine ⟨38790895189286084310019381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51721193585714779080025841 38790895189286084310019381)
        ·
          refine ⟨3636646423995570404064317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38790895189286084310019381 3636646423995570404064317)
          ·
            refine ⟨1363742408998338901524119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3636646423995570404064317 1363742408998338901524119)
            ·
              refine ⟨2045613613497508352286179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363742408998338901524119 2045613613497508352286179)
              ·
                refine ⟨3068420420246262528429269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045613613497508352286179 3068420420246262528429269)
                ·
                  refine ⟨71916103599521778010061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3068420420246262528429269 71916103599521778010061)
                  ·
                    rfl

theorem cell23_1260505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_1260505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260505 prefixEnd_1260505 := by exact prefixLift 1260505
  have htrace : WordTrace (prefixWord ++ tailWord_1260505) baseStart_1260505 baseEnd_1260505 := by
    simpa [prefixWord, tailWord_1260505, baseEnd_1260505] using wordTrace_append hprefix tailTrace_1260505
  have hstable : (prefixWord ++ tailWord_1260505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260505).length < 2 ^ (prefixWord ++ tailWord_1260505).sum := by decide
  have hdescent : baseEnd_1260505 < baseStart_1260505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260538 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1260538 : Nat := 118140960795 + 1260538 * 2 ^ 59
def prefixEnd_1260538 : Nat := 4983230072969 + 3 ^ 40 * 1260538 * 2
def baseEnd_1260538 : Nat := 647261877257294372977897

theorem tailTrace_1260538 : CollatzResearch.WordTrace tailWord_1260538 prefixEnd_1260538 647261877257294372977897 := by
  unfold tailWord_1260538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11493899476823395898993567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30650398604862389063982845 11493899476823395898993567)
  ·
    refine ⟨17240849215235093848490351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11493899476823395898993567 17240849215235093848490351)
    ·
      refine ⟨25861273822852640772735527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17240849215235093848490351 25861273822852640772735527)
      ·
        refine ⟨38791910734278961159103291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25861273822852640772735527 38791910734278961159103291)
        ·
          refine ⟨58187866101418441738654937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38791910734278961159103291 58187866101418441738654937)
          ·
            refine ⟨43640899576063831303991203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58187866101418441738654937 43640899576063831303991203)
            ·
              refine ⟨65461349364095746955986805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43640899576063831303991203 65461349364095746955986805)
              ·
                refine ⟨6137001502883976277123763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65461349364095746955986805 6137001502883976277123763)
                ·
                  refine ⟨9205502254325964415685645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6137001502883976277123763 9205502254325964415685645)
                  ·
                    refine ⟨3452063345372236655882117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9205502254325964415685645 3452063345372236655882117)
                    ·
                      refine ⟨647261877257294372977897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3452063345372236655882117 647261877257294372977897)
                      ·
                        rfl

theorem cell23_1260538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1260538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260538 prefixEnd_1260538 := by exact prefixLift 1260538
  have htrace : WordTrace (prefixWord ++ tailWord_1260538) baseStart_1260538 baseEnd_1260538 := by
    simpa [prefixWord, tailWord_1260538, baseEnd_1260538] using wordTrace_append hprefix tailTrace_1260538
  have hstable : (prefixWord ++ tailWord_1260538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260538).length < 2 ^ (prefixWord ++ tailWord_1260538).sum := by decide
  have hdescent : baseEnd_1260538 < baseStart_1260538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260555 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4]
def baseStart_1260555 : Nat := 118140960795 + 1260555 * 2 ^ 59
def prefixEnd_1260555 : Nat := 4983230072969 + 3 ^ 40 * 1260555 * 2
def baseEnd_1260555 : Nat := 647270606428420806465319

theorem tailTrace_1260555 : CollatzResearch.WordTrace tailWord_1260555 prefixEnd_1260555 647270606428420806465319 := by
  unfold tailWord_1260555
  simp only [CollatzResearch.WordTrace]
  refine ⟨45976217948231995499343119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30650811965487996999562079 45976217948231995499343119)
  ·
    refine ⟨68964326922347993249014679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45976217948231995499343119 68964326922347993249014679)
    ·
      refine ⟨103446490383521989873522019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68964326922347993249014679 103446490383521989873522019)
      ·
        refine ⟨155169735575282984810283029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103446490383521989873522019 155169735575282984810283029)
        ·
          refine ⟨7273581355091389912982017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155169735575282984810283029 7273581355091389912982017)
          ·
            refine ⟨5455186016318542434736513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7273581355091389912982017 5455186016318542434736513)
            ·
              refine ⟨4091389512238906826052385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5455186016318542434736513 4091389512238906826052385)
              ·
                refine ⟨3068542134179180119539289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4091389512238906826052385 3068542134179180119539289)
                ·
                  refine ⟨2301406600634385089654467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3068542134179180119539289 2301406600634385089654467)
                  ·
                    refine ⟨3452109900951577634481701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2301406600634385089654467 3452109900951577634481701)
                    ·
                      refine ⟨647270606428420806465319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3452109900951577634481701 647270606428420806465319)
                      ·
                        rfl

theorem cell23_1260555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_1260555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260555 prefixEnd_1260555 := by exact prefixLift 1260555
  have htrace : WordTrace (prefixWord ++ tailWord_1260555) baseStart_1260555 baseEnd_1260555 := by
    simpa [prefixWord, tailWord_1260555, baseEnd_1260555] using wordTrace_append hprefix tailTrace_1260555
  have hstable : (prefixWord ++ tailWord_1260555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260555).length < 2 ^ (prefixWord ++ tailWord_1260555).sum := by decide
  have hdescent : baseEnd_1260555 < baseStart_1260555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260655 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 6, 4]
def baseStart_1260655 : Nat := 118140960795 + 1260655 * 2 ^ 59
def prefixEnd_1260655 : Nat := 4983230072969 + 3 ^ 40 * 1260655 * 2
def baseEnd_1260655 : Nat := 215773984831290138404953

theorem tailTrace_1260655 : CollatzResearch.WordTrace tailWord_1260655 prefixEnd_1260655 215773984831290138404953 := by
  unfold tailWord_1260655
  simp only [CollatzResearch.WordTrace]
  refine ⟨45979865247869712577983419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30653243498579808385322279 45979865247869712577983419)
  ·
    refine ⟨68969797871804568866975129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45979865247869712577983419 68969797871804568866975129)
    ·
      refine ⟨51727348403853426650231347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68969797871804568866975129 51727348403853426650231347)
      ·
        refine ⟨77591022605780139975347021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51727348403853426650231347 77591022605780139975347021)
        ·
          refine ⟨29096633477167552490755133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77591022605780139975347021 29096633477167552490755133)
          ·
            refine ⟨10911237553937832184033175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29096633477167552490755133 10911237553937832184033175)
            ·
              refine ⟨16366856330906748276049763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10911237553937832184033175 16366856330906748276049763)
              ·
                refine ⟨24550284496360122414074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16366856330906748276049763 24550284496360122414074645)
                ·
                  refine ⟨1150794585766880738159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24550284496360122414074645 1150794585766880738159749)
                  ·
                    refine ⟨215773984831290138404953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1150794585766880738159749 215773984831290138404953)
                    ·
                      rfl

theorem cell23_1260655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_1260655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260655 prefixEnd_1260655 := by exact prefixLift 1260655
  have htrace : WordTrace (prefixWord ++ tailWord_1260655) baseStart_1260655 baseEnd_1260655 := by
    simpa [prefixWord, tailWord_1260655, baseEnd_1260655] using wordTrace_append hprefix tailTrace_1260655
  have hstable : (prefixWord ++ tailWord_1260655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260655).length < 2 ^ (prefixWord ++ tailWord_1260655).sum := by decide
  have hdescent : baseEnd_1260655 < baseStart_1260655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260673 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_1260673 : Nat := 118140960795 + 1260673 * 2 ^ 59
def prefixEnd_1260673 : Nat := 4983230072969 + 3 ^ 40 * 1260673 * 2
def baseEnd_1260673 : Nat := 647331197145651344789777

theorem tailTrace_1260673 : CollatzResearch.WordTrace tailWord_1260673 prefixEnd_1260673 647331197145651344789777 := by
  unfold tailWord_1260673
  simp only [CollatzResearch.WordTrace]
  refine ⟨45980521761804501652138673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30653681174536334434759115 45980521761804501652138673)
  ·
    refine ⟨34485391321353376239104005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45980521761804501652138673 34485391321353376239104005)
    ·
      refine ⟨6466010872753758044832001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34485391321353376239104005 6466010872753758044832001)
      ·
        refine ⟨4849508154565318533624001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6466010872753758044832001 4849508154565318533624001)
        ·
          refine ⟨3637131115923988900218001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4849508154565318533624001 3637131115923988900218001)
          ·
            refine ⟨2727848336942991675163501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3637131115923988900218001 2727848336942991675163501)
            ·
              refine ⟨1022943126353621878186313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2727848336942991675163501 1022943126353621878186313)
              ·
                refine ⟨767207344765216408639735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1022943126353621878186313 767207344765216408639735)
                ·
                  refine ⟨1150811017147824612959603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767207344765216408639735 1150811017147824612959603)
                  ·
                    refine ⟨1726216525721736919439405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150811017147824612959603 1726216525721736919439405)
                    ·
                      refine ⟨647331197145651344789777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726216525721736919439405 647331197145651344789777)
                      ·
                        rfl

theorem cell23_1260673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_1260673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260673 prefixEnd_1260673 := by exact prefixLift 1260673
  have htrace : WordTrace (prefixWord ++ tailWord_1260673) baseStart_1260673 baseEnd_1260673 := by
    simpa [prefixWord, tailWord_1260673, baseEnd_1260673] using wordTrace_append hprefix tailTrace_1260673
  have hstable : (prefixWord ++ tailWord_1260673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260673).length < 2 ^ (prefixWord ++ tailWord_1260673).sum := by decide
  have hdescent : baseEnd_1260673 < baseStart_1260673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260682 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1260682 : Nat := 118140960795 + 1260682 * 2 ^ 59
def prefixEnd_1260682 : Nat := 4983230072969 + 3 ^ 40 * 1260682 * 2
def baseEnd_1260682 : Nat := 647335818471541809577235

theorem tailTrace_1260682 : CollatzResearch.WordTrace tailWord_1260682 prefixEnd_1260682 647335818471541809577235 := by
  unfold tailWord_1260682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495212504692974047304075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30653900012514597459477533 11495212504692974047304075)
  ·
    refine ⟨17242818757039461070956113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495212504692974047304075 17242818757039461070956113)
    ·
      refine ⟨12932114067779595803217085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17242818757039461070956113 12932114067779595803217085)
      ·
        refine ⟨4849542775417348426206407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12932114067779595803217085 4849542775417348426206407)
        ·
          refine ⟨7274314163126022639309611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4849542775417348426206407 7274314163126022639309611)
          ·
            refine ⟨10911471244689033958964417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7274314163126022639309611 10911471244689033958964417)
            ·
              refine ⟨8183603433516775469223313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10911471244689033958964417 8183603433516775469223313)
              ·
                refine ⟨6137702575137581601917485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8183603433516775469223313 6137702575137581601917485)
                ·
                  refine ⟨2301638465676593100719057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6137702575137581601917485 2301638465676593100719057)
                  ·
                    refine ⟨1726228849257444825539293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2301638465676593100719057 1726228849257444825539293)
                    ·
                      refine ⟨647335818471541809577235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726228849257444825539293 647335818471541809577235)
                      ·
                        rfl

theorem cell23_1260682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1260682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260682 prefixEnd_1260682 := by exact prefixLift 1260682
  have htrace : WordTrace (prefixWord ++ tailWord_1260682) baseStart_1260682 baseEnd_1260682 := by
    simpa [prefixWord, tailWord_1260682, baseEnd_1260682] using wordTrace_append hprefix tailTrace_1260682
  have hstable : (prefixWord ++ tailWord_1260682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260682).length < 2 ^ (prefixWord ++ tailWord_1260682).sum := by decide
  have hdescent : baseEnd_1260682 < baseStart_1260682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260702 : List Nat := [4, 3, 1, 1, 2, 1, 2, 9]
def baseStart_1260702 : Nat := 118140960795 + 1260702 * 2 ^ 59
def prefixEnd_1260702 : Nat := 4983230072969 + 3 ^ 40 * 1260702 * 2
def baseEnd_1260702 : Nat := 23975781040171545604709

theorem tailTrace_1260702 : CollatzResearch.WordTrace tailWord_1260702 prefixEnd_1260702 23975781040171545604709 := by
  unfold tailWord_1260702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747697434837429950618045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30654386319132959736629573 5747697434837429950618045)
  ·
    refine ⟨2155386538064036231481767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5747697434837429950618045 2155386538064036231481767)
    ·
      refine ⟨3233079807096054347222651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2155386538064036231481767 3233079807096054347222651)
      ·
        refine ⟨4849619710644081520833977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3233079807096054347222651 4849619710644081520833977)
        ·
          refine ⟨3637214782983061140625483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4849619710644081520833977 3637214782983061140625483)
          ·
            refine ⟨5455822174474591710938225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637214782983061140625483 5455822174474591710938225)
            ·
              refine ⟨4091866630855943783203669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5455822174474591710938225 4091866630855943783203669)
              ·
                refine ⟨23975781040171545604709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4091866630855943783203669 23975781040171545604709)
                ·
                  rfl

theorem cell23_1260702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 9].length) (baseStart_1260702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260702 prefixEnd_1260702 := by exact prefixLift 1260702
  have htrace : WordTrace (prefixWord ++ tailWord_1260702) baseStart_1260702 baseEnd_1260702 := by
    simpa [prefixWord, tailWord_1260702, baseEnd_1260702] using wordTrace_append hprefix tailTrace_1260702
  have hstable : (prefixWord ++ tailWord_1260702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260702).length < 2 ^ (prefixWord ++ tailWord_1260702).sum := by decide
  have hdescent : baseEnd_1260702 < baseStart_1260702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260729 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1260729 : Nat := 118140960795 + 1260729 * 2 ^ 59
def prefixEnd_1260729 : Nat := 4983230072969 + 3 ^ 40 * 1260729 * 2
def baseEnd_1260729 : Nat := 647359952062303125689519

theorem tailTrace_1260729 : CollatzResearch.WordTrace tailWord_1260729 prefixEnd_1260729 647359952062303125689519 := by
  unfold tailWord_1260729
  simp only [CollatzResearch.WordTrace]
  refine ⟨45982564249601623216177241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30655042833067748810784827 45982564249601623216177241)
  ·
    refine ⟨34486923187201217412132931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45982564249601623216177241 34486923187201217412132931)
    ·
      refine ⟨51730384780801826118199397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34486923187201217412132931 51730384780801826118199397)
      ·
        refine ⟨9699447146400342397162387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51730384780801826118199397 9699447146400342397162387)
        ·
          refine ⟨14549170719600513595743581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699447146400342397162387 14549170719600513595743581)
          ·
            refine ⟨5455939019850192598403843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14549170719600513595743581 5455939019850192598403843)
            ·
              refine ⟨8183908529775288897605765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5455939019850192598403843 8183908529775288897605765)
              ·
                refine ⟨1534482849332866668301081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8183908529775288897605765 1534482849332866668301081)
                ·
                  refine ⟨1150862136999650001225811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534482849332866668301081 1150862136999650001225811)
                  ·
                    refine ⟨1726293205499475001838717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1150862136999650001225811 1726293205499475001838717)
                    ·
                      refine ⟨647359952062303125689519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726293205499475001838717 647359952062303125689519)
                      ·
                        rfl

theorem cell23_1260729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1260729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260729 prefixEnd_1260729 := by exact prefixLift 1260729
  have htrace : WordTrace (prefixWord ++ tailWord_1260729) baseStart_1260729 baseEnd_1260729 := by
    simpa [prefixWord, tailWord_1260729, baseEnd_1260729] using wordTrace_append hprefix tailTrace_1260729
  have hstable : (prefixWord ++ tailWord_1260729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260729).length < 2 ^ (prefixWord ++ tailWord_1260729).sum := by decide
  have hdescent : baseEnd_1260729 < baseStart_1260729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260735 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1260735 : Nat := 118140960795 + 1260735 * 2 ^ 59
def prefixEnd_1260735 : Nat := 4983230072969 + 3 ^ 40 * 1260735 * 2
def baseEnd_1260735 : Nat := 647363032946230102214491

theorem tailTrace_1260735 : CollatzResearch.WordTrace tailWord_1260735 prefixEnd_1260735 647363032946230102214491 := by
  unfold tailWord_1260735
  simp only [CollatzResearch.WordTrace]
  refine ⟨45982783087579886240895659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30655188725053257493930439 45982783087579886240895659)
  ·
    refine ⟨68974174631369829361343489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45982783087579886240895659 68974174631369829361343489)
    ·
      refine ⟨51730630973527372021007617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68974174631369829361343489 51730630973527372021007617)
      ·
        refine ⟨38797973230145529015755713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51730630973527372021007617 38797973230145529015755713)
        ·
          refine ⟨29098479922609146761816785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38797973230145529015755713 29098479922609146761816785)
          ·
            refine ⟨21823859941956860071362589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29098479922609146761816785 21823859941956860071362589)
            ·
              refine ⟨8183947478233822526760971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21823859941956860071362589 8183947478233822526760971)
              ·
                refine ⟨12275921217350733790141457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8183947478233822526760971 12275921217350733790141457)
                ·
                  refine ⟨9206940913013050342606093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12275921217350733790141457 9206940913013050342606093)
                  ·
                    refine ⟨3452602842379893878477285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9206940913013050342606093 3452602842379893878477285)
                    ·
                      refine ⟨647363032946230102214491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3452602842379893878477285 647363032946230102214491)
                      ·
                        rfl

theorem cell23_1260735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1260735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260735 prefixEnd_1260735 := by exact prefixLift 1260735
  have htrace : WordTrace (prefixWord ++ tailWord_1260735) baseStart_1260735 baseEnd_1260735 := by
    simpa [prefixWord, tailWord_1260735, baseEnd_1260735] using wordTrace_append hprefix tailTrace_1260735
  have hstable : (prefixWord ++ tailWord_1260735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260735).length < 2 ^ (prefixWord ++ tailWord_1260735).sum := by decide
  have hdescent : baseEnd_1260735 < baseStart_1260735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260769 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_1260769 : Nat := 118140960795 + 1260769 * 2 ^ 59
def prefixEnd_1260769 : Nat := 4983230072969 + 3 ^ 40 * 1260769 * 2
def baseEnd_1260769 : Nat := 647380491288482969189335

theorem tailTrace_1260769 : CollatzResearch.WordTrace tailWord_1260769 prefixEnd_1260769 647380491288482969189335 := by
  unfold tailWord_1260769
  simp only [CollatzResearch.WordTrace]
  refine ⟨45984023169456710047633361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30656015446304473365088907 45984023169456710047633361)
  ·
    refine ⟨34488017377092532535725021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45984023169456710047633361 34488017377092532535725021)
    ·
      refine ⟨12933006516409699700896883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34488017377092532535725021 12933006516409699700896883)
      ·
        refine ⟨19399509774614549551345325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12933006516409699700896883 19399509774614549551345325)
        ·
          refine ⟨7274816165480456081754497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19399509774614549551345325 7274816165480456081754497)
          ·
            refine ⟨5456112124110342061315873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7274816165480456081754497 5456112124110342061315873)
            ·
              refine ⟨4092084093082756545986905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5456112124110342061315873 4092084093082756545986905)
              ·
                refine ⟨3069063069812067409490179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4092084093082756545986905 3069063069812067409490179)
                ·
                  refine ⟨4603594604718101114235269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3069063069812067409490179 4603594604718101114235269)
                  ·
                    refine ⟨863173988384643958919113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4603594604718101114235269 863173988384643958919113)
                    ·
                      refine ⟨647380491288482969189335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863173988384643958919113 647380491288482969189335)
                      ·
                        rfl

theorem cell23_1260769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_1260769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260769 prefixEnd_1260769 := by exact prefixLift 1260769
  have htrace : WordTrace (prefixWord ++ tailWord_1260769) baseStart_1260769 baseEnd_1260769 := by
    simpa [prefixWord, tailWord_1260769, baseEnd_1260769] using wordTrace_append hprefix tailTrace_1260769
  have hstable : (prefixWord ++ tailWord_1260769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260769).length < 2 ^ (prefixWord ++ tailWord_1260769).sum := by decide
  have hdescent : baseEnd_1260769 < baseStart_1260769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260782 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1260782 : Nat := 118140960795 + 1260782 * 2 ^ 59
def prefixEnd_1260782 : Nat := 4983230072969 + 3 ^ 40 * 1260782 * 2
def baseEnd_1260782 : Nat := 647387166536991418326775

theorem tailTrace_1260782 : CollatzResearch.WordTrace tailWord_1260782 prefixEnd_1260782 647387166536991418326775 := by
  unfold tailWord_1260782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748062164801201658482075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30656331545606408845237733 5748062164801201658482075)
  ·
    refine ⟨8622093247201802487723113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748062164801201658482075 8622093247201802487723113)
    ·
      refine ⟨6466569935401351865792335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8622093247201802487723113 6466569935401351865792335)
      ·
        refine ⟨9699854903102027798688503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6466569935401351865792335 9699854903102027798688503)
        ·
          refine ⟨14549782354653041698032755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9699854903102027798688503 14549782354653041698032755)
          ·
            refine ⟨21824673531979562547049133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14549782354653041698032755 21824673531979562547049133)
            ·
              refine ⟨8184252574492335955143425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21824673531979562547049133 8184252574492335955143425)
              ·
                refine ⟨6138189430869251966357569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8184252574492335955143425 6138189430869251966357569)
                ·
                  refine ⟨4603642073151938974768177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6138189430869251966357569 4603642073151938974768177)
                  ·
                    refine ⟨3452731554863954231076133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4603642073151938974768177 3452731554863954231076133)
                    ·
                      refine ⟨647387166536991418326775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3452731554863954231076133 647387166536991418326775)
                      ·
                        rfl

theorem cell23_1260782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1260782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260782 prefixEnd_1260782 := by exact prefixLift 1260782
  have htrace : WordTrace (prefixWord ++ tailWord_1260782) baseStart_1260782 baseEnd_1260782 := by
    simpa [prefixWord, tailWord_1260782, baseEnd_1260782] using wordTrace_append hprefix tailTrace_1260782
  have hstable : (prefixWord ++ tailWord_1260782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260782).length < 2 ^ (prefixWord ++ tailWord_1260782).sum := by decide
  have hdescent : baseEnd_1260782 < baseStart_1260782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260803 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 2, 2, 2]
def baseStart_1260803 : Nat := 118140960795 + 1260803 * 2 ^ 59
def prefixEnd_1260803 : Nat := 4983230072969 + 3 ^ 40 * 1260803 * 2
def baseEnd_1260803 : Nat := 647397949630735836164179

theorem tailTrace_1260803 : CollatzResearch.WordTrace tailWord_1260803 prefixEnd_1260803 647397949630735836164179 := by
  unfold tailWord_1260803
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985263251333533854371063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30656842167555689236247375 45985263251333533854371063)
  ·
    refine ⟨68977894877000300781556595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45985263251333533854371063 68977894877000300781556595)
    ·
      refine ⟨103466842315500451172334893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68977894877000300781556595 103466842315500451172334893)
      ·
        refine ⟨38800065868312669189625585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103466842315500451172334893 38800065868312669189625585)
        ·
          refine ⟨29100049401234501892219189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38800065868312669189625585 29100049401234501892219189)
          ·
            refine ⟨2728129631365734552395549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29100049401234501892219189 2728129631365734552395549)
            ·
              refine ⟨1023048611762150457148331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2728129631365734552395549 1023048611762150457148331)
              ·
                refine ⟨1534572917643225685722497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023048611762150457148331 1534572917643225685722497)
                ·
                  refine ⟨1150929688232419264291873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534572917643225685722497 1150929688232419264291873)
                  ·
                    refine ⟨863197266174314448218905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1150929688232419264291873 863197266174314448218905)
                    ·
                      refine ⟨647397949630735836164179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863197266174314448218905 647397949630735836164179)
                      ·
                        rfl

theorem cell23_1260803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_1260803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260803 prefixEnd_1260803 := by exact prefixLift 1260803
  have htrace : WordTrace (prefixWord ++ tailWord_1260803) baseStart_1260803 baseEnd_1260803 := by
    simpa [prefixWord, tailWord_1260803, baseEnd_1260803] using wordTrace_append hprefix tailTrace_1260803
  have hstable : (prefixWord ++ tailWord_1260803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260803).length < 2 ^ (prefixWord ++ tailWord_1260803).sum := by decide
  have hdescent : baseEnd_1260803 < baseStart_1260803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260805 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1260805 : Nat := 118140960795 + 1260805 * 2 ^ 59
def prefixEnd_1260805 : Nat := 4983230072969 + 3 ^ 40 * 1260805 * 2
def baseEnd_1260805 : Nat := 215799658864014942779723

theorem tailTrace_1260805 : CollatzResearch.WordTrace tailWord_1260805 prefixEnd_1260805 215799658864014942779723 := by
  unfold tailWord_1260805
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985336197326288195943869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30656890798217525463962579 45985336197326288195943869)
  ·
    refine ⟨17244501073997358073478951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45985336197326288195943869 17244501073997358073478951)
    ·
      refine ⟨25866751610996037110218427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17244501073997358073478951 25866751610996037110218427)
      ·
        refine ⟨38800127416494055665327641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25866751610996037110218427 38800127416494055665327641)
        ·
          refine ⟨29100095562370541748995731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38800127416494055665327641 29100095562370541748995731)
          ·
            refine ⟨43650143343555812623493597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29100095562370541748995731 43650143343555812623493597)
            ·
              refine ⟨16368803753833429733810099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43650143343555812623493597 16368803753833429733810099)
              ·
                refine ⟨24553205630750144600715149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16368803753833429733810099 24553205630750144600715149)
                ·
                  refine ⟨9207452111531304225268181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24553205630750144600715149 9207452111531304225268181)
                  ·
                    refine ⟨215799658864014942779723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9207452111531304225268181 215799658864014942779723)
                    ·
                      rfl

theorem cell23_1260805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1260805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260805 prefixEnd_1260805 := by exact prefixLift 1260805
  have htrace : WordTrace (prefixWord ++ tailWord_1260805) baseStart_1260805 baseEnd_1260805 := by
    simpa [prefixWord, tailWord_1260805, baseEnd_1260805] using wordTrace_append hprefix tailTrace_1260805
  have hstable : (prefixWord ++ tailWord_1260805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260805).length < 2 ^ (prefixWord ++ tailWord_1260805).sum := by decide
  have hdescent : baseEnd_1260805 < baseStart_1260805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260815 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_1260815 : Nat := 118140960795 + 1260815 * 2 ^ 59
def prefixEnd_1260815 : Nat := 4983230072969 + 3 ^ 40 * 1260815 * 2
def baseEnd_1260815 : Nat := 647404111398589789214123

theorem tailTrace_1260815 : CollatzResearch.WordTrace tailWord_1260815 prefixEnd_1260815 647404111398589789214123 := by
  unfold tailWord_1260815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45985700927290059903807899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30657133951526706602538599 45985700927290059903807899)
  ·
    refine ⟨68978551390935089855711849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45985700927290059903807899 68978551390935089855711849)
    ·
      refine ⟨51733913543201317391783887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68978551390935089855711849 51733913543201317391783887)
      ·
        refine ⟨77600870314801976087675831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51733913543201317391783887 77600870314801976087675831)
        ·
          refine ⟨116401305472202964131513747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77600870314801976087675831 116401305472202964131513747)
          ·
            refine ⟨174601958208304446197270621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116401305472202964131513747 174601958208304446197270621)
            ·
              refine ⟨65475734328114167323976483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174601958208304446197270621 65475734328114167323976483)
              ·
                refine ⟨98213601492171250985964725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65475734328114167323976483 98213601492171250985964725)
                ·
                  refine ⟨9207525139891054779934193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98213601492171250985964725 9207525139891054779934193)
                  ·
                    refine ⟨6905643854918291084950645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9207525139891054779934193 6905643854918291084950645)
                    ·
                      refine ⟨647404111398589789214123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6905643854918291084950645 647404111398589789214123)
                      ·
                        rfl

theorem cell23_1260815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_1260815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260815 prefixEnd_1260815 := by exact prefixLift 1260815
  have htrace : WordTrace (prefixWord ++ tailWord_1260815) baseStart_1260815 baseEnd_1260815 := by
    simpa [prefixWord, tailWord_1260815, baseEnd_1260815] using wordTrace_append hprefix tailTrace_1260815
  have hstable : (prefixWord ++ tailWord_1260815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260815).length < 2 ^ (prefixWord ++ tailWord_1260815).sum := by decide
  have hdescent : baseEnd_1260815 < baseStart_1260815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260826 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_1260826 : Nat := 118140960795 + 1260826 * 2 ^ 59
def prefixEnd_1260826 : Nat := 4983230072969 + 3 ^ 40 * 1260826 * 2
def baseEnd_1260826 : Nat := 71934417742865471797397

theorem tailTrace_1260826 : CollatzResearch.WordTrace tailWord_1260826 prefixEnd_1260826 71934417742865471797397 := by
  unfold tailWord_1260826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11496525532562552195614583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30657401420166805854972221 11496525532562552195614583)
  ·
    refine ⟨17244788298843828293421875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11496525532562552195614583 17244788298843828293421875)
    ·
      refine ⟨25867182448265742440132813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17244788298843828293421875 25867182448265742440132813)
      ·
        refine ⟨9700193418099653415049805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25867182448265742440132813 9700193418099653415049805)
        ·
          refine ⟨3637572531787370030643677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9700193418099653415049805 3637572531787370030643677)
          ·
            refine ⟨1364089699420263761491379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3637572531787370030643677 1364089699420263761491379)
            ·
              refine ⟨2046134549130395642237069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364089699420263761491379 2046134549130395642237069)
              ·
                refine ⟨767300455923898365838901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046134549130395642237069 767300455923898365838901)
                ·
                  refine ⟨71934417742865471797397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 767300455923898365838901 71934417742865471797397)
                  ·
                    rfl

theorem cell23_1260826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_1260826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260826 prefixEnd_1260826 := by exact prefixLift 1260826
  have htrace : WordTrace (prefixWord ++ tailWord_1260826) baseStart_1260826 baseEnd_1260826 := by
    simpa [prefixWord, tailWord_1260826, baseEnd_1260826] using wordTrace_append hprefix tailTrace_1260826
  have hstable : (prefixWord ++ tailWord_1260826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260826).length < 2 ^ (prefixWord ++ tailWord_1260826).sum := by decide
  have hdescent : baseEnd_1260826 < baseStart_1260826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260854 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1260854 : Nat := 118140960795 + 1260854 * 2 ^ 59
def prefixEnd_1260854 : Nat := 4983230072969 + 3 ^ 40 * 1260854 * 2
def baseEnd_1260854 : Nat := 647424137144115136626445

theorem tailTrace_1260854 : CollatzResearch.WordTrace tailWord_1260854 prefixEnd_1260854 647424137144115136626445 := by
  unfold tailWord_1260854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874195210884298097779851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30658082249432513042985077 2874195210884298097779851)
  ·
    refine ⟨4311292816326447146669777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874195210884298097779851 4311292816326447146669777)
    ·
      refine ⟨3233469612244835360002333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4311292816326447146669777 3233469612244835360002333)
      ·
        refine ⟨1212551104591813260000875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3233469612244835360002333 1212551104591813260000875)
        ·
          refine ⟨1818826656887719890001313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212551104591813260000875 1818826656887719890001313)
          ·
            refine ⟨1364119992665789917500985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1818826656887719890001313 1364119992665789917500985)
            ·
              refine ⟨1023089994499342438125739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1364119992665789917500985 1023089994499342438125739)
              ·
                refine ⟨1534634991749013657188609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1023089994499342438125739 1534634991749013657188609)
                ·
                  refine ⟨1150976243811760242891457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534634991749013657188609 1150976243811760242891457)
                  ·
                    refine ⟨863232182858820182168593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1150976243811760242891457 863232182858820182168593)
                    ·
                      refine ⟨647424137144115136626445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863232182858820182168593 647424137144115136626445)
                      ·
                        rfl

theorem cell23_1260854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1260854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260854 prefixEnd_1260854 := by exact prefixLift 1260854
  have htrace : WordTrace (prefixWord ++ tailWord_1260854) baseStart_1260854 baseEnd_1260854 := by
    simpa [prefixWord, tailWord_1260854, baseEnd_1260854] using wordTrace_append hprefix tailTrace_1260854
  have hstable : (prefixWord ++ tailWord_1260854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260854).length < 2 ^ (prefixWord ++ tailWord_1260854).sum := by decide
  have hdescent : baseEnd_1260854 < baseStart_1260854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260899 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 6]
def baseStart_1260899 : Nat := 118140960795 + 1260899 * 2 ^ 59
def prefixEnd_1260899 : Nat := 4983230072969 + 3 ^ 40 * 1260899 * 2
def baseEnd_1260899 : Nat := 71938582641507495618193

theorem tailTrace_1260899 : CollatzResearch.WordTrace tailWord_1260899 prefixEnd_1260899 71938582641507495618193 := by
  unfold tailWord_1260899
  simp only [CollatzResearch.WordTrace]
  refine ⟨45988764658985742249865751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30659176439323828166577167 45988764658985742249865751)
  ·
    refine ⟨68983146988478613374798627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45988764658985742249865751 68983146988478613374798627)
    ·
      refine ⟨103474720482717920062197941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68983146988478613374798627 103474720482717920062197941)
      ·
        refine ⟨9700755045254805005831057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103474720482717920062197941 9700755045254805005831057)
        ·
          refine ⟨7275566283941103754373293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9700755045254805005831057 7275566283941103754373293)
          ·
            refine ⟨2728337356477913907889985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7275566283941103754373293 2728337356477913907889985)
            ·
              refine ⟨2046253017358435430917489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728337356477913907889985 2046253017358435430917489)
              ·
                refine ⟨1534689763018826573188117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046253017358435430917489 1534689763018826573188117)
                ·
                  refine ⟨71938582641507495618193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1534689763018826573188117 71938582641507495618193)
                  ·
                    rfl

theorem cell23_1260899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 6].length) (baseStart_1260899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260899 prefixEnd_1260899 := by exact prefixLift 1260899
  have htrace : WordTrace (prefixWord ++ tailWord_1260899) baseStart_1260899 baseEnd_1260899 := by
    simpa [prefixWord, tailWord_1260899, baseEnd_1260899] using wordTrace_append hprefix tailTrace_1260899
  have hstable : (prefixWord ++ tailWord_1260899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260899).length < 2 ^ (prefixWord ++ tailWord_1260899).sum := by decide
  have hdescent : baseEnd_1260899 < baseStart_1260899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260903 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 1, 4]
def baseStart_1260903 : Nat := 118140960795 + 1260903 * 2 ^ 59
def prefixEnd_1260903 : Nat := 4983230072969 + 3 ^ 40 * 1260903 * 2
def baseEnd_1260903 : Nat := 215816432565395148304573

theorem tailTrace_1260903 : CollatzResearch.WordTrace tailWord_1260903 prefixEnd_1260903 215816432565395148304573 := by
  unfold tailWord_1260903
  simp only [CollatzResearch.WordTrace]
  refine ⟨45988910550971250933011363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30659273700647500622007575 45988910550971250933011363)
  ·
    refine ⟨68983365826456876399517045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45988910550971250933011363 68983365826456876399517045)
    ·
      refine ⟨6467190546230332162454723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68983365826456876399517045 6467190546230332162454723)
      ·
        refine ⟨9700785819345498243682085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6467190546230332162454723 9700785819345498243682085)
        ·
          refine ⟨1818897341127280920690391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9700785819345498243682085 1818897341127280920690391)
          ·
            refine ⟨2728346011690921381035587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818897341127280920690391 2728346011690921381035587)
            ·
              refine ⟨4092519017536382071553381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728346011690921381035587 4092519017536382071553381)
              ·
                refine ⟨767347315788071638416259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4092519017536382071553381 767347315788071638416259)
                ·
                  refine ⟨1151020973682107457624389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767347315788071638416259 1151020973682107457624389)
                  ·
                    refine ⟨215816432565395148304573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1151020973682107457624389 215816432565395148304573)
                    ·
                      rfl

theorem cell23_1260903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_1260903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260903 prefixEnd_1260903 := by exact prefixLift 1260903
  have htrace : WordTrace (prefixWord ++ tailWord_1260903) baseStart_1260903 baseEnd_1260903 := by
    simpa [prefixWord, tailWord_1260903, baseEnd_1260903] using wordTrace_append hprefix tailTrace_1260903
  have hstable : (prefixWord ++ tailWord_1260903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260903).length < 2 ^ (prefixWord ++ tailWord_1260903).sum := by decide
  have hdescent : baseEnd_1260903 < baseStart_1260903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260912 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_1260912 : Nat := 118140960795 + 1260912 * 2 ^ 59
def prefixEnd_1260912 : Nat := 4983230072969 + 3 ^ 40 * 1260912 * 2
def baseEnd_1260912 : Nat := 215817973007358636567059

theorem tailTrace_1260912 : CollatzResearch.WordTrace tailWord_1260912 prefixEnd_1260912 215817973007358636567059 := by
  unfold tailWord_1260912
  simp only [CollatzResearch.WordTrace]
  refine ⟨22994619403969322735044495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30659492538625763646725993 22994619403969322735044495)
  ·
    refine ⟨34491929105953984102566743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22994619403969322735044495 34491929105953984102566743)
    ·
      refine ⟨51737893658930976153850115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34491929105953984102566743 51737893658930976153850115)
      ·
        refine ⟨77606840488396464230775173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51737893658930976153850115 77606840488396464230775173)
        ·
          refine ⟨14551282591574337043270345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77606840488396464230775173 14551282591574337043270345)
          ·
            refine ⟨10913461943680752782452759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14551282591574337043270345 10913461943680752782452759)
            ·
              refine ⟨16370192915521129173679139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10913461943680752782452759 16370192915521129173679139)
              ·
                refine ⟨24555289373281693760518709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16370192915521129173679139 24555289373281693760518709)
                ·
                  refine ⟨2302058378745158790048629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24555289373281693760518709 2302058378745158790048629)
                  ·
                    refine ⟨215817973007358636567059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2302058378745158790048629 215817973007358636567059)
                    ·
                      rfl

theorem cell23_1260912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_1260912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260912 prefixEnd_1260912 := by exact prefixLift 1260912
  have htrace : WordTrace (prefixWord ++ tailWord_1260912) baseStart_1260912 baseEnd_1260912 := by
    simpa [prefixWord, tailWord_1260912, baseEnd_1260912] using wordTrace_append hprefix tailTrace_1260912
  have hstable : (prefixWord ++ tailWord_1260912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260912).length < 2 ^ (prefixWord ++ tailWord_1260912).sum := by decide
  have hdescent : baseEnd_1260912 < baseStart_1260912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260919 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_1260919 : Nat := 118140960795 + 1260919 * 2 ^ 59
def prefixEnd_1260919 : Nat := 4983230072969 + 3 ^ 40 * 1260919 * 2
def baseEnd_1260919 : Nat := 647457513386657382313645

theorem tailTrace_1260919 : CollatzResearch.WordTrace tailWord_1260919 prefixEnd_1260919 647457513386657382313645 := by
  unfold tailWord_1260919
  simp only [CollatzResearch.WordTrace]
  refine ⟨45989494118913285665593811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30659662745942190443729207 45989494118913285665593811)
  ·
    refine ⟨68984241178369928498390717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45989494118913285665593811 68984241178369928498390717)
    ·
      refine ⟨25869090441888723186896519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68984241178369928498390717 25869090441888723186896519)
      ·
        refine ⟨38803635662833084780344779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25869090441888723186896519 38803635662833084780344779)
        ·
          refine ⟨58205453494249627170517169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38803635662833084780344779 58205453494249627170517169)
          ·
            refine ⟨43654090120687220377887877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58205453494249627170517169 43654090120687220377887877)
            ·
              refine ⟨8185141897628853820853977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43654090120687220377887877 8185141897628853820853977)
              ·
                refine ⟨6138856423221640365640483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8185141897628853820853977 6138856423221640365640483)
                ·
                  refine ⟨9208284634832460548460725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138856423221640365640483 9208284634832460548460725)
                  ·
                    refine ⟨863276684515543176418193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9208284634832460548460725 863276684515543176418193)
                    ·
                      refine ⟨647457513386657382313645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863276684515543176418193 647457513386657382313645)
                      ·
                        rfl

theorem cell23_1260919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_1260919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260919 prefixEnd_1260919 := by exact prefixLift 1260919
  have htrace : WordTrace (prefixWord ++ tailWord_1260919) baseStart_1260919 baseEnd_1260919 := by
    simpa [prefixWord, tailWord_1260919, baseEnd_1260919] using wordTrace_append hprefix tailTrace_1260919
  have hstable : (prefixWord ++ tailWord_1260919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260919).length < 2 ^ (prefixWord ++ tailWord_1260919).sum := by decide
  have hdescent : baseEnd_1260919 < baseStart_1260919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260930 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1260930 : Nat := 118140960795 + 1260930 * 2 ^ 59
def prefixEnd_1260930 : Nat := 4983230072969 + 3 ^ 40 * 1260930 * 2
def baseEnd_1260930 : Nat := 647463161673856839276095

theorem tailTrace_1260930 : CollatzResearch.WordTrace tailWord_1260930 prefixEnd_1260930 647463161673856839276095 := by
  unfold tailWord_1260930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497473830468358636061061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30659930214582289696162829 11497473830468358636061061)
  ·
    refine ⟨2155776343212817244261449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11497473830468358636061061 2155776343212817244261449)
    ·
      refine ⟨1616832257409612933196087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155776343212817244261449 1616832257409612933196087)
      ·
        refine ⟨2425248386114419399794131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616832257409612933196087 2425248386114419399794131)
        ·
          refine ⟨3637872579171629099691197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2425248386114419399794131 3637872579171629099691197)
          ·
            refine ⟨1364202217189360912384199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3637872579171629099691197 1364202217189360912384199)
            ·
              refine ⟨2046303325784041368576299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364202217189360912384199 2046303325784041368576299)
              ·
                refine ⟨3069454988676062052864449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2046303325784041368576299 3069454988676062052864449)
                ·
                  refine ⟨2302091241507046539648337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3069454988676062052864449 2302091241507046539648337)
                  ·
                    refine ⟨1726568431130284904736253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302091241507046539648337 1726568431130284904736253)
                    ·
                      refine ⟨647463161673856839276095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726568431130284904736253 647463161673856839276095)
                      ·
                        rfl

theorem cell23_1260930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1260930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260930 prefixEnd_1260930 := by exact prefixLift 1260930
  have htrace : WordTrace (prefixWord ++ tailWord_1260930) baseStart_1260930 baseEnd_1260930 := by
    simpa [prefixWord, tailWord_1260930, baseEnd_1260930] using wordTrace_append hprefix tailTrace_1260930
  have hstable : (prefixWord ++ tailWord_1260930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260930).length < 2 ^ (prefixWord ++ tailWord_1260930).sum := by decide
  have hdescent : baseEnd_1260930 < baseStart_1260930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260936 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_1260936 : Nat := 118140960795 + 1260936 * 2 ^ 59
def prefixEnd_1260936 : Nat := 4983230072969 + 3 ^ 40 * 1260936 * 2
def baseEnd_1260936 : Nat := 647466242557783815801067

theorem tailTrace_1260936 : CollatzResearch.WordTrace tailWord_1260936 prefixEnd_1260936 647466242557783815801067 := by
  unfold tailWord_1260936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22995057079925848784481331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30660076106567798379308441 22995057079925848784481331)
  ·
    refine ⟨34492585619888773176721997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22995057079925848784481331 34492585619888773176721997)
    ·
      refine ⟨12934719607458289941270749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34492585619888773176721997 12934719607458289941270749)
      ·
        refine ⟨4850519852796858727976531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12934719607458289941270749 4850519852796858727976531)
        ·
          refine ⟨7275779779195288091964797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4850519852796858727976531 7275779779195288091964797)
          ·
            refine ⟨2728417417198233034486799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7275779779195288091964797 2728417417198233034486799)
            ·
              refine ⟨4092626125797349551730199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2728417417198233034486799 4092626125797349551730199)
              ·
                refine ⟨6138939188696024327595299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092626125797349551730199 6138939188696024327595299)
                ·
                  refine ⟨9208408783044036491392949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6138939188696024327595299 9208408783044036491392949)
                  ·
                    refine ⟨863288323410378421068089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9208408783044036491392949 863288323410378421068089)
                    ·
                      refine ⟨647466242557783815801067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863288323410378421068089 647466242557783815801067)
                      ·
                        rfl

theorem cell23_1260936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_1260936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260936 prefixEnd_1260936 := by exact prefixLift 1260936
  have htrace : WordTrace (prefixWord ++ tailWord_1260936) baseStart_1260936 baseEnd_1260936 := by
    simpa [prefixWord, tailWord_1260936, baseEnd_1260936] using wordTrace_append hprefix tailTrace_1260936
  have hstable : (prefixWord ++ tailWord_1260936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260936).length < 2 ^ (prefixWord ++ tailWord_1260936).sum := by decide
  have hdescent : baseEnd_1260936 < baseStart_1260936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1260999 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1260999 : Nat := 118140960795 + 1260999 * 2 ^ 59
def prefixEnd_1260999 : Nat := 4983230072969 + 3 ^ 40 * 1260999 * 2
def baseEnd_1260999 : Nat := 647498591839017069313277

theorem tailTrace_1260999 : CollatzResearch.WordTrace tailWord_1260999 prefixEnd_1260999 647498591839017069313277 := by
  unfold tailWord_1260999
  simp only [CollatzResearch.WordTrace]
  refine ⟨45992411958623459328506051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30661607972415639552337367 45992411958623459328506051)
  ·
    refine ⟨68988617937935188992759077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45992411958623459328506051 68988617937935188992759077)
    ·
      refine ⟨12935365863362847936142327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68988617937935188992759077 12935365863362847936142327)
      ·
        refine ⟨19403048795044271904213491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12935365863362847936142327 19403048795044271904213491)
        ·
          refine ⟨29104573192566407856320237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19403048795044271904213491 29104573192566407856320237)
          ·
            refine ⟨10914214947212402946120089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29104573192566407856320237 10914214947212402946120089)
            ·
              refine ⟨8185661210409302209590067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10914214947212402946120089 8185661210409302209590067)
              ·
                refine ⟨12278491815613953314385101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8185661210409302209590067 12278491815613953314385101)
                ·
                  refine ⟨4604434430855232492894413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12278491815613953314385101 4604434430855232492894413)
                  ·
                    refine ⟨1726662911570712184835405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4604434430855232492894413 1726662911570712184835405)
                    ·
                      refine ⟨647498591839017069313277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726662911570712184835405 647498591839017069313277)
                      ·
                        rfl

theorem cell23_1260999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1260999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1260999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1260999 prefixEnd_1260999 := by exact prefixLift 1260999
  have htrace : WordTrace (prefixWord ++ tailWord_1260999) baseStart_1260999 baseEnd_1260999 := by
    simpa [prefixWord, tailWord_1260999, baseEnd_1260999] using wordTrace_append hprefix tailTrace_1260999
  have hstable : (prefixWord ++ tailWord_1260999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1260999).length < 2 ^ (prefixWord ++ tailWord_1260999).sum := by decide
  have hdescent : baseEnd_1260999 < baseStart_1260999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1260999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261016 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1261016 : Nat := 118140960795 + 1261016 * 2 ^ 59
def prefixEnd_1261016 : Nat := 4983230072969 + 3 ^ 40 * 1261016 * 2
def baseEnd_1261016 : Nat := 647507321010143502800699

theorem tailTrace_1261016 : CollatzResearch.WordTrace tailWord_1261016 prefixEnd_1261016 647507321010143502800699 := by
  unfold tailWord_1261016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22996515999780935615937451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30662021333041247487916601 22996515999780935615937451)
  ·
    refine ⟨34494773999671403423906177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22996515999780935615937451 34494773999671403423906177)
    ·
      refine ⟨25871080499753552567929633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34494773999671403423906177 25871080499753552567929633)
      ·
        refine ⟨19403310374815164425947225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25871080499753552567929633 19403310374815164425947225)
        ·
          refine ⟨14552482781111373319460419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19403310374815164425947225 14552482781111373319460419)
          ·
            refine ⟨21828724171667059979190629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14552482781111373319460419 21828724171667059979190629)
            ·
              refine ⟨4092885782187573746098243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21828724171667059979190629 4092885782187573746098243)
              ·
                refine ⟨6139328673281360619147365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4092885782187573746098243 6139328673281360619147365)
                ·
                  refine ⟨1151124126240255116090131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6139328673281360619147365 1151124126240255116090131)
                  ·
                    refine ⟨1726686189360382674135197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1151124126240255116090131 1726686189360382674135197)
                    ·
                      refine ⟨647507321010143502800699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726686189360382674135197 647507321010143502800699)
                      ·
                        rfl

theorem cell23_1261016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1261016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261016 prefixEnd_1261016 := by exact prefixLift 1261016
  have htrace : WordTrace (prefixWord ++ tailWord_1261016) baseStart_1261016 baseEnd_1261016 := by
    simpa [prefixWord, tailWord_1261016, baseEnd_1261016] using wordTrace_append hprefix tailTrace_1261016
  have hstable : (prefixWord ++ tailWord_1261016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261016).length < 2 ^ (prefixWord ++ tailWord_1261016).sum := by decide
  have hdescent : baseEnd_1261016 < baseStart_1261016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261017 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 1, 2, 2]
def baseStart_1261017 : Nat := 118140960795 + 1261017 * 2 ^ 59
def prefixEnd_1261017 : Nat := 4983230072969 + 3 ^ 40 * 1261017 * 2
def baseEnd_1261017 : Nat := 647507834490797998888195

theorem tailTrace_1261017 : CollatzResearch.WordTrace tailWord_1261017 prefixEnd_1261017 647507834490797998888195 := by
  unfold tailWord_1261017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45993068472558248402661305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30662045648372165601774203 45993068472558248402661305)
  ·
    refine ⟨34494801354418686301995979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45993068472558248402661305 34494801354418686301995979)
    ·
      refine ⟨51742202031628029452993969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34494801354418686301995979 51742202031628029452993969)
      ·
        refine ⟨38806651523721022089745477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51742202031628029452993969 38806651523721022089745477)
        ·
          refine ⟨7276247160697691641827277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38806651523721022089745477 7276247160697691641827277)
          ·
            refine ⟨2728592685261634365685229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7276247160697691641827277 2728592685261634365685229)
            ·
              refine ⟨1023222256973112887131961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2728592685261634365685229 1023222256973112887131961)
              ·
                refine ⟨767416692729834665348971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1023222256973112887131961 767416692729834665348971)
                ·
                  refine ⟨1151125039094751998023457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767416692729834665348971 1151125039094751998023457)
                  ·
                    refine ⟨863343779321063998517593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1151125039094751998023457 863343779321063998517593)
                    ·
                      refine ⟨647507834490797998888195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863343779321063998517593 647507834490797998888195)
                      ·
                        rfl

theorem cell23_1261017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_1261017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261017 prefixEnd_1261017 := by exact prefixLift 1261017
  have htrace : WordTrace (prefixWord ++ tailWord_1261017) baseStart_1261017 baseEnd_1261017 := by
    simpa [prefixWord, tailWord_1261017, baseEnd_1261017] using wordTrace_append hprefix tailTrace_1261017
  have hstable : (prefixWord ++ tailWord_1261017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261017).length < 2 ^ (prefixWord ++ tailWord_1261017).sum := by decide
  have hdescent : baseEnd_1261017 < baseStart_1261017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261037 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1261037 : Nat := 118140960795 + 1261037 * 2 ^ 59
def prefixEnd_1261037 : Nat := 4983230072969 + 3 ^ 40 * 1261037 * 2
def baseEnd_1261037 : Nat := 647518104103887920638103

theorem tailTrace_1261037 : CollatzResearch.WordTrace tailWord_1261037 prefixEnd_1261037 647518104103887920638103 := by
  unfold tailWord_1261037
  simp only [CollatzResearch.WordTrace]
  refine ⟨45993797932485791818389365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30662531954990527878926243 45993797932485791818389365)
  ·
    refine ⟨4311918556170542982974003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45993797932485791818389365 4311918556170542982974003)
    ·
      refine ⟨6467877834255814474461005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311918556170542982974003 6467877834255814474461005)
      ·
        refine ⟨2425454187845930427922877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6467877834255814474461005 2425454187845930427922877)
        ·
          refine ⟨909545320442223910471079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2425454187845930427922877 909545320442223910471079)
          ·
            refine ⟨1364317980663335865706619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909545320442223910471079 1364317980663335865706619)
            ·
              refine ⟨2046476970995003798559929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364317980663335865706619 2046476970995003798559929)
              ·
                refine ⟨1534857728246252848919947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046476970995003798559929 1534857728246252848919947)
                ·
                  refine ⟨2302286592369379273379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1534857728246252848919947 2302286592369379273379921)
                  ·
                    refine ⟨1726714944277034455034941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302286592369379273379921 1726714944277034455034941)
                    ·
                      refine ⟨647518104103887920638103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726714944277034455034941 647518104103887920638103)
                      ·
                        rfl

theorem cell23_1261037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1261037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261037 prefixEnd_1261037 := by exact prefixLift 1261037
  have htrace : WordTrace (prefixWord ++ tailWord_1261037) baseStart_1261037 baseEnd_1261037 := by
    simpa [prefixWord, tailWord_1261037, baseEnd_1261037] using wordTrace_append hprefix tailTrace_1261037
  have hstable : (prefixWord ++ tailWord_1261037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261037).length < 2 ^ (prefixWord ++ tailWord_1261037).sum := by decide
  have hdescent : baseEnd_1261037 < baseStart_1261037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261090 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1261090 : Nat := 118140960795 + 1261090 * 2 ^ 59
def prefixEnd_1261090 : Nat := 4983230072969 + 3 ^ 40 * 1261090 * 2
def baseEnd_1261090 : Nat := 647545318578576213275359

theorem tailTrace_1261090 : CollatzResearch.WordTrace tailWord_1261090 prefixEnd_1261090 647545318578576213275359 := by
  unfold tailWord_1261090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11498932750323445467517181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30663820667529187913379149 11498932750323445467517181)
  ·
    refine ⟨4312099781371292050318943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11498932750323445467517181 4312099781371292050318943)
    ·
      refine ⟨6468149672056938075478415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4312099781371292050318943 6468149672056938075478415)
      ·
        refine ⟨9702224508085407113217623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468149672056938075478415 9702224508085407113217623)
        ·
          refine ⟨14553336762128110669826435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9702224508085407113217623 14553336762128110669826435)
          ·
            refine ⟨21830005143192166004739653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14553336762128110669826435 21830005143192166004739653)
            ·
              refine ⟨4093125964348531125888685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21830005143192166004739653 4093125964348531125888685)
              ·
                refine ⟨1534922236630699172208257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4093125964348531125888685 1534922236630699172208257)
                ·
                  refine ⟨1151191677473024379156193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1534922236630699172208257 1151191677473024379156193)
                  ·
                    refine ⟨863393758104768284367145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1151191677473024379156193 863393758104768284367145)
                    ·
                      refine ⟨647545318578576213275359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863393758104768284367145 647545318578576213275359)
                      ·
                        rfl

theorem cell23_1261090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1261090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261090 prefixEnd_1261090 := by exact prefixLift 1261090
  have htrace : WordTrace (prefixWord ++ tailWord_1261090) baseStart_1261090 baseEnd_1261090 := by
    simpa [prefixWord, tailWord_1261090, baseEnd_1261090] using wordTrace_append hprefix tailTrace_1261090
  have hstable : (prefixWord ++ tailWord_1261090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261090).length < 2 ^ (prefixWord ++ tailWord_1261090).sum := by decide
  have hdescent : baseEnd_1261090 < baseStart_1261090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261113 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 5]
def baseStart_1261113 : Nat := 118140960795 + 1261113 * 2 ^ 59
def prefixEnd_1261113 : Nat := 4983230072969 + 3 ^ 40 * 1261113 * 2
def baseEnd_1261113 : Nat := 71950792070403291476417

theorem tailTrace_1261113 : CollatzResearch.WordTrace tailWord_1261113 prefixEnd_1261113 71950792070403291476417 := by
  unfold tailWord_1261113
  simp only [CollatzResearch.WordTrace]
  refine ⟨45996569880210456798155993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30664379920140304532103995 45996569880210456798155993)
  ·
    refine ⟨34497427410157842598616995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45996569880210456798155993 34497427410157842598616995)
    ·
      refine ⟨51746141115236763897925493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34497427410157842598616995 51746141115236763897925493)
      ·
        refine ⟨4851200729553446615430515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51746141115236763897925493 4851200729553446615430515)
        ·
          refine ⟨7276801094330169923145773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4851200729553446615430515 7276801094330169923145773)
          ·
            refine ⟨2728800410373813721179665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7276801094330169923145773 2728800410373813721179665)
            ·
              refine ⟨2046600307780360290884749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2728800410373813721179665 2046600307780360290884749)
              ·
                refine ⟨767475115417635109081781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2046600307780360290884749 767475115417635109081781)
                ·
                  refine ⟨71950792070403291476417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 767475115417635109081781 71950792070403291476417)
                  ·
                    rfl

theorem cell23_1261113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 5].length) (baseStart_1261113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261113 prefixEnd_1261113 := by exact prefixLift 1261113
  have htrace : WordTrace (prefixWord ++ tailWord_1261113) baseStart_1261113 baseEnd_1261113 := by
    simpa [prefixWord, tailWord_1261113, baseEnd_1261113] using wordTrace_append hprefix tailTrace_1261113
  have hstable : (prefixWord ++ tailWord_1261113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261113).length < 2 ^ (prefixWord ++ tailWord_1261113).sum := by decide
  have hdescent : baseEnd_1261113 < baseStart_1261113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261209 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1261209 : Nat := 118140960795 + 1261209 * 2 ^ 59
def prefixEnd_1261209 : Nat := 4983230072969 + 3 ^ 40 * 1261209 * 2
def baseEnd_1261209 : Nat := 647606422776461247687311

theorem tailTrace_1261209 : CollatzResearch.WordTrace tailWord_1261209 prefixEnd_1261209 647606422776461247687311 := by
  unfold tailWord_1261209
  simp only [CollatzResearch.WordTrace]
  refine ⟨46000071287862665193650681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30666714191908443462433787 46000071287862665193650681)
  ·
    refine ⟨34500053465896998895238011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46000071287862665193650681 34500053465896998895238011)
    ·
      refine ⟨51750080198845498342857017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34500053465896998895238011 51750080198845498342857017)
      ·
        refine ⟨38812560149134123757142763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51750080198845498342857017 38812560149134123757142763)
        ·
          refine ⟨58218840223701185635714145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38812560149134123757142763 58218840223701185635714145)
          ·
            refine ⟨43664130167775889226785609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58218840223701185635714145 43664130167775889226785609)
            ·
              refine ⟨32748097625831916920089207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43664130167775889226785609 32748097625831916920089207)
              ·
                refine ⟨49122146438747875380133811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32748097625831916920089207 49122146438747875380133811)
                ·
                  refine ⟨73683219658121813070200717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49122146438747875380133811 73683219658121813070200717)
                  ·
                    refine ⟨27631207371795679901325269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73683219658121813070200717 27631207371795679901325269)
                    ·
                      refine ⟨647606422776461247687311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27631207371795679901325269 647606422776461247687311)
                      ·
                        rfl

theorem cell23_1261209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1261209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261209 prefixEnd_1261209 := by exact prefixLift 1261209
  have htrace : WordTrace (prefixWord ++ tailWord_1261209) baseStart_1261209 baseEnd_1261209 := by
    simpa [prefixWord, tailWord_1261209, baseEnd_1261209] using wordTrace_append hprefix tailTrace_1261209
  have hstable : (prefixWord ++ tailWord_1261209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261209).length < 2 ^ (prefixWord ++ tailWord_1261209).sum := by decide
  have hdescent : baseEnd_1261209 < baseStart_1261209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261213 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1261213 : Nat := 118140960795 + 1261213 * 2 ^ 59
def prefixEnd_1261213 : Nat := 4983230072969 + 3 ^ 40 * 1261213 * 2
def baseEnd_1261213 : Nat := 647608476699079232037293

theorem tailTrace_1261213 : CollatzResearch.WordTrace tailWord_1261213 prefixEnd_1261213 647608476699079232037293 := by
  unfold tailWord_1261213
  simp only [CollatzResearch.WordTrace]
  refine ⟨46000217179848173876796293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30666811453232115917864195 46000217179848173876796293)
  ·
    refine ⟨8625040721221532601899305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46000217179848173876796293 8625040721221532601899305)
    ·
      refine ⟨6468780540916149451424479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8625040721221532601899305 6468780540916149451424479)
      ·
        refine ⟨9703170811374224177136719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6468780540916149451424479 9703170811374224177136719)
        ·
          refine ⟨14554756217061336265705079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9703170811374224177136719 14554756217061336265705079)
          ·
            refine ⟨21832134325592004398557619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14554756217061336265705079 21832134325592004398557619)
            ·
              refine ⟨32748201488388006597836429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21832134325592004398557619 32748201488388006597836429)
              ·
                refine ⟨12280575558145502474188661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32748201488388006597836429 12280575558145502474188661)
                ·
                  refine ⟨1151303958576140856955187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12280575558145502474188661 1151303958576140856955187)
                  ·
                    refine ⟨1726955937864211285432781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1151303958576140856955187 1726955937864211285432781)
                    ·
                      refine ⟨647608476699079232037293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1726955937864211285432781 647608476699079232037293)
                      ·
                        rfl

theorem cell23_1261213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1261213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261213 prefixEnd_1261213 := by exact prefixLift 1261213
  have htrace : WordTrace (prefixWord ++ tailWord_1261213) baseStart_1261213 baseEnd_1261213 := by
    simpa [prefixWord, tailWord_1261213, baseEnd_1261213] using wordTrace_append hprefix tailTrace_1261213
  have hstable : (prefixWord ++ tailWord_1261213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261213).length < 2 ^ (prefixWord ++ tailWord_1261213).sum := by decide
  have hdescent : baseEnd_1261213 < baseStart_1261213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261256 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1261256 : Nat := 118140960795 + 1261256 * 2 ^ 59
def prefixEnd_1261256 : Nat := 4983230072969 + 3 ^ 40 * 1261256 * 2
def baseEnd_1261256 : Nat := 647630556367222563799595

theorem tailTrace_1261256 : CollatzResearch.WordTrace tailWord_1261256 prefixEnd_1261256 647630556367222563799595 := by
  unfold tailWord_1261256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23000892759346196110305811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30667857012461594813741081 23000892759346196110305811)
  ·
    refine ⟨34501339139019294165458717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23000892759346196110305811 34501339139019294165458717)
    ·
      refine ⟨12938002177132235312047019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34501339139019294165458717 12938002177132235312047019)
      ·
        refine ⟨19407003265698352968070529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12938002177132235312047019 19407003265698352968070529)
        ·
          refine ⟨14555252449273764726052897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19407003265698352968070529 14555252449273764726052897)
          ·
            refine ⟨10916439336955323544539673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14555252449273764726052897 10916439336955323544539673)
            ·
              refine ⟨8187329502716492658404755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10916439336955323544539673 8187329502716492658404755)
              ·
                refine ⟨12280994254074738987607133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8187329502716492658404755 12280994254074738987607133)
                ·
                  refine ⟨4605372845278027120352675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12280994254074738987607133 4605372845278027120352675)
                  ·
                    refine ⟨6908059267917040680529013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4605372845278027120352675 6908059267917040680529013)
                    ·
                      refine ⟨647630556367222563799595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6908059267917040680529013 647630556367222563799595)
                      ·
                        rfl

theorem cell23_1261256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1261256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261256 prefixEnd_1261256 := by exact prefixLift 1261256
  have htrace : WordTrace (prefixWord ++ tailWord_1261256) baseStart_1261256 baseEnd_1261256 := by
    simpa [prefixWord, tailWord_1261256, baseEnd_1261256] using wordTrace_append hprefix tailTrace_1261256
  have hstable : (prefixWord ++ tailWord_1261256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261256).length < 2 ^ (prefixWord ++ tailWord_1261256).sum := by decide
  have hdescent : baseEnd_1261256 < baseStart_1261256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261273 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_1261273 : Nat := 118140960795 + 1261273 * 2 ^ 59
def prefixEnd_1261273 : Nat := 4983230072969 + 3 ^ 40 * 1261273 * 2
def baseEnd_1261273 : Nat := 647639285538348997287017

theorem tailTrace_1261273 : CollatzResearch.WordTrace tailWord_1261273 prefixEnd_1261273 647639285538348997287017 := by
  unfold tailWord_1261273
  simp only [CollatzResearch.WordTrace]
  refine ⟨46002405559630804123980473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30668270373087202749320315 46002405559630804123980473)
  ·
    refine ⟨34501804169723103092985355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46002405559630804123980473 34501804169723103092985355)
    ·
      refine ⟨51752706254584654639478033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34501804169723103092985355 51752706254584654639478033)
      ·
        refine ⟨38814529690938490979608525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51752706254584654639478033 38814529690938490979608525)
        ·
          refine ⟨14555448634101934117353197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38814529690938490979608525 14555448634101934117353197)
          ·
            refine ⟨5458293237788225294007449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14555448634101934117353197 5458293237788225294007449)
            ·
              refine ⟨4093719928341168970505587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5458293237788225294007449 4093719928341168970505587)
              ·
                refine ⟨6140579892511753455758381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4093719928341168970505587 6140579892511753455758381)
                ·
                  refine ⟨2302717459691907545909393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6140579892511753455758381 2302717459691907545909393)
                  ·
                    refine ⟨1727038094768930659432045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2302717459691907545909393 1727038094768930659432045)
                    ·
                      refine ⟨647639285538348997287017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727038094768930659432045 647639285538348997287017)
                      ·
                        rfl

theorem cell23_1261273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_1261273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261273 prefixEnd_1261273 := by exact prefixLift 1261273
  have htrace : WordTrace (prefixWord ++ tailWord_1261273) baseStart_1261273 baseEnd_1261273 := by
    simpa [prefixWord, tailWord_1261273, baseEnd_1261273] using wordTrace_append hprefix tailTrace_1261273
  have hstable : (prefixWord ++ tailWord_1261273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261273).length < 2 ^ (prefixWord ++ tailWord_1261273).sum := by decide
  have hdescent : baseEnd_1261273 < baseStart_1261273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261287 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1261287 : Nat := 118140960795 + 1261287 * 2 ^ 59
def prefixEnd_1261287 : Nat := 4983230072969 + 3 ^ 40 * 1261287 * 2
def baseEnd_1261287 : Nat := 647646474267511942511953

theorem tailTrace_1261287 : CollatzResearch.WordTrace tailWord_1261287 prefixEnd_1261287 647646474267511942511953 := by
  unfold tailWord_1261287
  simp only [CollatzResearch.WordTrace]
  refine ⟨46002916181580084514990115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30668610787720056343326743 46002916181580084514990115)
  ·
    refine ⟨69004374272370126772485173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46002916181580084514990115 69004374272370126772485173)
    ·
      refine ⟨6469160088034699384920485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69004374272370126772485173 6469160088034699384920485)
      ·
        refine ⟨1212967516506506134672591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6469160088034699384920485 1212967516506506134672591)
        ·
          refine ⟨1819451274759759202008887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212967516506506134672591 1819451274759759202008887)
          ·
            refine ⟨2729176912139638803013331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819451274759759202008887 2729176912139638803013331)
            ·
              refine ⟨4093765368209458204519997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729176912139638803013331 4093765368209458204519997)
              ·
                refine ⟨1535162013078546826694999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4093765368209458204519997 1535162013078546826694999)
                ·
                  refine ⟨2302743019617820240042499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535162013078546826694999 2302743019617820240042499)
                  ·
                    refine ⟨3454114529426730360063749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2302743019617820240042499 3454114529426730360063749)
                    ·
                      refine ⟨647646474267511942511953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3454114529426730360063749 647646474267511942511953)
                      ·
                        rfl

theorem cell23_1261287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1261287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261287 prefixEnd_1261287 := by exact prefixLift 1261287
  have htrace : WordTrace (prefixWord ++ tailWord_1261287) baseStart_1261287 baseEnd_1261287 := by
    simpa [prefixWord, tailWord_1261287, baseEnd_1261287] using wordTrace_append hprefix tailTrace_1261287
  have hstable : (prefixWord ++ tailWord_1261287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261287).length < 2 ^ (prefixWord ++ tailWord_1261287).sum := by decide
  have hdescent : baseEnd_1261287 < baseStart_1261287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261318 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1261318 : Nat := 118140960795 + 1261318 * 2 ^ 59
def prefixEnd_1261318 : Nat := 4983230072969 + 3 ^ 40 * 1261318 * 2
def baseEnd_1261318 : Nat := 215887464055933773741437

theorem tailTrace_1261318 : CollatzResearch.WordTrace tailWord_1261318 prefixEnd_1261318 215887464055933773741437 := by
  unfold tailWord_1261318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437626463889618025292769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30669364562978517872912405 1437626463889618025292769)
  ·
    refine ⟨1078219847917213518969577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1437626463889618025292769 1078219847917213518969577)
    ·
      refine ⟨808664885937910139227183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078219847917213518969577 808664885937910139227183)
      ·
        refine ⟨1212997328906865208840775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808664885937910139227183 1212997328906865208840775)
        ·
          refine ⟨1819495993360297813261163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212997328906865208840775 1819495993360297813261163)
          ·
            refine ⟨2729243990040446719891745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819495993360297813261163 2729243990040446719891745)
            ·
              refine ⟨2046932992530335039918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729243990040446719891745 2046932992530335039918809)
              ·
                refine ⟨1535199744397751279939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2046932992530335039918809 1535199744397751279939107)
                ·
                  refine ⟨2302799616596626919908661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535199744397751279939107 2302799616596626919908661)
                  ·
                    refine ⟨215887464055933773741437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2302799616596626919908661 215887464055933773741437)
                    ·
                      rfl

theorem cell23_1261318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1261318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261318 prefixEnd_1261318 := by exact prefixLift 1261318
  have htrace : WordTrace (prefixWord ++ tailWord_1261318) baseStart_1261318 baseEnd_1261318 := by
    simpa [prefixWord, tailWord_1261318, baseEnd_1261318] using wordTrace_append hprefix tailTrace_1261318
  have hstable : (prefixWord ++ tailWord_1261318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261318).length < 2 ^ (prefixWord ++ tailWord_1261318).sum := by decide
  have hdescent : baseEnd_1261318 < baseStart_1261318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261336 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1261336 : Nat := 118140960795 + 1261336 * 2 ^ 59
def prefixEnd_1261336 : Nat := 4983230072969 + 3 ^ 40 * 1261336 * 2
def baseEnd_1261336 : Nat := 215890544939860750266409

theorem tailTrace_1261336 : CollatzResearch.WordTrace tailWord_1261336 prefixEnd_1261336 215890544939860750266409 := by
  unfold tailWord_1261336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23002351679201282941761931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30669802238935043922349241 23002351679201282941761931)
  ·
    refine ⟨34503527518801924412642897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23002351679201282941761931 34503527518801924412642897)
    ·
      refine ⟨25877645639101443309482173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34503527518801924412642897 25877645639101443309482173)
      ·
        refine ⟨9704117114663041241055815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25877645639101443309482173 9704117114663041241055815)
        ·
          refine ⟨14556175671994561861583723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9704117114663041241055815 14556175671994561861583723)
          ·
            refine ⟨21834263507991842792375585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14556175671994561861583723 21834263507991842792375585)
            ·
              refine ⟨16375697630993882094281689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21834263507991842792375585 16375697630993882094281689)
              ·
                refine ⟨12281773223245411570711267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16375697630993882094281689 12281773223245411570711267)
                ·
                  refine ⟨18422659834868117356066901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12281773223245411570711267 18422659834868117356066901)
                  ·
                    refine ⟨215890544939860750266409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18422659834868117356066901 215890544939860750266409)
                    ·
                      rfl

theorem cell23_1261336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1261336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261336 prefixEnd_1261336 := by exact prefixLift 1261336
  have htrace : WordTrace (prefixWord ++ tailWord_1261336) baseStart_1261336 baseEnd_1261336 := by
    simpa [prefixWord, tailWord_1261336, baseEnd_1261336] using wordTrace_append hprefix tailTrace_1261336
  have hstable : (prefixWord ++ tailWord_1261336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261336).length < 2 ^ (prefixWord ++ tailWord_1261336).sum := by decide
  have hdescent : baseEnd_1261336 < baseStart_1261336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261420 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_1261420 : Nat := 118140960795 + 1261420 * 2 ^ 59
def prefixEnd_1261420 : Nat := 4983230072969 + 3 ^ 40 * 1261420 * 2
def baseEnd_1261420 : Nat := 647714767194559922148841

theorem tailTrace_1261420 : CollatzResearch.WordTrace tailWord_1261420 prefixEnd_1261420 647714767194559922148841 := by
  unfold tailWord_1261420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23003883545049124114790857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30671844726732165486387809 23003883545049124114790857)
  ·
    refine ⟨17252912658786843086093143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23003883545049124114790857 17252912658786843086093143)
    ·
      refine ⟨25879368988180264629139715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17252912658786843086093143 25879368988180264629139715)
      ·
        refine ⟨38819053482270396943709573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25879368988180264629139715 38819053482270396943709573)
        ·
          refine ⟨7278572527925699426945545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38819053482270396943709573 7278572527925699426945545)
          ·
            refine ⟨5458929395944274570209159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7278572527925699426945545 5458929395944274570209159)
            ·
              refine ⟨8188394093916411855313739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5458929395944274570209159 8188394093916411855313739)
              ·
                refine ⟨12282591140874617782970609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188394093916411855313739 12282591140874617782970609)
                ·
                  refine ⟨9211943355655963337227957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12282591140874617782970609 9211943355655963337227957)
                  ·
                    refine ⟨863619689592746562865121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9211943355655963337227957 863619689592746562865121)
                    ·
                      refine ⟨647714767194559922148841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863619689592746562865121 647714767194559922148841)
                      ·
                        rfl

theorem cell23_1261420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_1261420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261420 prefixEnd_1261420 := by exact prefixLift 1261420
  have htrace : WordTrace (prefixWord ++ tailWord_1261420) baseStart_1261420 baseEnd_1261420 := by
    simpa [prefixWord, tailWord_1261420, baseEnd_1261420] using wordTrace_append hprefix tailTrace_1261420
  have hstable : (prefixWord ++ tailWord_1261420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261420).length < 2 ^ (prefixWord ++ tailWord_1261420).sum := by decide
  have hdescent : baseEnd_1261420 < baseStart_1261420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261433 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1261433 : Nat := 118140960795 + 1261433 * 2 ^ 59
def prefixEnd_1261433 : Nat := 4983230072969 + 3 ^ 40 * 1261433 * 2
def baseEnd_1261433 : Nat := 647721442443068371286281

theorem tailTrace_1261433 : CollatzResearch.WordTrace tailWord_1261433 prefixEnd_1261433 647721442443068371286281 := by
  unfold tailWord_1261433
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008241239051151449804953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30672160826034100966536635 46008241239051151449804953)
  ·
    refine ⟨34506180929288363587353715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46008241239051151449804953 34506180929288363587353715)
    ·
      refine ⟨51759271393932545381030573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34506180929288363587353715 51759271393932545381030573)
      ·
        refine ⟨19409726772724704517886465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51759271393932545381030573 19409726772724704517886465)
        ·
          refine ⟨14557295079543528388414849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19409726772724704517886465 14557295079543528388414849)
          ·
            refine ⟨10917971309657646291311137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14557295079543528388414849 10917971309657646291311137)
            ·
              refine ⟨8188478482243234718483353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10917971309657646291311137 8188478482243234718483353)
              ·
                refine ⟨6141358861682426038862515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8188478482243234718483353 6141358861682426038862515)
                ·
                  refine ⟨9212038292523639058293773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6141358861682426038862515 9212038292523639058293773)
                  ·
                    refine ⟨3454514359696364646860165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9212038292523639058293773 3454514359696364646860165)
                    ·
                      refine ⟨647721442443068371286281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3454514359696364646860165 647721442443068371286281)
                      ·
                        rfl

theorem cell23_1261433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1261433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261433 prefixEnd_1261433 := by exact prefixLift 1261433
  have htrace : WordTrace (prefixWord ++ tailWord_1261433) baseStart_1261433 baseEnd_1261433 := by
    simpa [prefixWord, tailWord_1261433, baseEnd_1261433] using wordTrace_append hprefix tailTrace_1261433
  have hstable : (prefixWord ++ tailWord_1261433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261433).length < 2 ^ (prefixWord ++ tailWord_1261433).sum := by decide
  have hdescent : baseEnd_1261433 < baseStart_1261433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261447 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 2, 5]
def baseStart_1261447 : Nat := 118140960795 + 1261447 * 2 ^ 59
def prefixEnd_1261447 : Nat := 4983230072969 + 3 ^ 40 * 1261447 * 2
def baseEnd_1261447 : Nat := 215909543724077105503739

theorem tailTrace_1261447 : CollatzResearch.WordTrace tailWord_1261447 prefixEnd_1261447 215909543724077105503739 := by
  unfold tailWord_1261447
  simp only [CollatzResearch.WordTrace]
  refine ⟨46008751861000431840814595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30672501240666954560543063 46008751861000431840814595)
  ·
    refine ⟨69013127791500647761221893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46008751861000431840814595 69013127791500647761221893)
    ·
      refine ⟨12939961460906371455229105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69013127791500647761221893 12939961460906371455229105)
      ·
        refine ⟨9704971095679778591421829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12939961460906371455229105 9704971095679778591421829)
        ·
          refine ⟨1819682080439958485891593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9704971095679778591421829 1819682080439958485891593)
          ·
            refine ⟨1364761560329968864418695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819682080439958485891593 1364761560329968864418695)
            ·
              refine ⟨2047142340494953296628043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364761560329968864418695 2047142340494953296628043)
              ·
                refine ⟨3070713510742429944942065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047142340494953296628043 3070713510742429944942065)
                ·
                  refine ⟨2303035133056822458706549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070713510742429944942065 2303035133056822458706549)
                  ·
                    refine ⟨215909543724077105503739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2303035133056822458706549 215909543724077105503739)
                    ·
                      rfl

theorem cell23_1261447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_1261447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261447 prefixEnd_1261447 := by exact prefixLift 1261447
  have htrace : WordTrace (prefixWord ++ tailWord_1261447) baseStart_1261447 baseEnd_1261447 := by
    simpa [prefixWord, tailWord_1261447, baseEnd_1261447] using wordTrace_append hprefix tailTrace_1261447
  have hstable : (prefixWord ++ tailWord_1261447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261447).length < 2 ^ (prefixWord ++ tailWord_1261447).sum := by decide
  have hdescent : baseEnd_1261447 < baseStart_1261447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261462 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1261462 : Nat := 118140960795 + 1261462 * 2 ^ 59
def prefixEnd_1261462 : Nat := 4983230072969 + 3 ^ 40 * 1261462 * 2
def baseEnd_1261462 : Nat := 647736333382048757823649

theorem tailTrace_1261462 : CollatzResearch.WordTrace tailWord_1261462 prefixEnd_1261462 647736333382048757823649 := by
  unfold tailWord_1261462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875581184746630587663165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30672865970630726268407093 2875581184746630587663165)
  ·
    refine ⟨1078342944279986470373687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2875581184746630587663165 1078342944279986470373687)
    ·
      refine ⟨1617514416419979705560531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078342944279986470373687 1617514416419979705560531)
      ·
        refine ⟨2426271624629969558340797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1617514416419979705560531 2426271624629969558340797)
        ·
          refine ⟨909851859236238584377799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2426271624629969558340797 909851859236238584377799)
          ·
            refine ⟨1364777788854357876566699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909851859236238584377799 1364777788854357876566699)
            ·
              refine ⟨2047166683281536814850049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364777788854357876566699 2047166683281536814850049)
              ·
                refine ⟨1535375012461152611137537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2047166683281536814850049 1535375012461152611137537)
                ·
                  refine ⟨1151531259345864458353153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535375012461152611137537 1151531259345864458353153)
                  ·
                    refine ⟨863648444509398343764865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1151531259345864458353153 863648444509398343764865)
                    ·
                      refine ⟨647736333382048757823649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863648444509398343764865 647736333382048757823649)
                      ·
                        rfl

theorem cell23_1261462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1261462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261462 prefixEnd_1261462 := by exact prefixLift 1261462
  have htrace : WordTrace (prefixWord ++ tailWord_1261462) baseStart_1261462 baseEnd_1261462 := by
    simpa [prefixWord, tailWord_1261462, baseEnd_1261462] using wordTrace_append hprefix tailTrace_1261462
  have hstable : (prefixWord ++ tailWord_1261462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261462).length < 2 ^ (prefixWord ++ tailWord_1261462).sum := by decide
  have hdescent : baseEnd_1261462 < baseStart_1261462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261463 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1261463 : Nat := 118140960795 + 1261463 * 2 ^ 59
def prefixEnd_1261463 : Nat := 4983230072969 + 3 ^ 40 * 1261463 * 2
def baseEnd_1261463 : Nat := 647736846862703253911143

theorem tailTrace_1261463 : CollatzResearch.WordTrace tailWord_1261463 prefixEnd_1261463 647736846862703253911143 := by
  unfold tailWord_1261463
  simp only [CollatzResearch.WordTrace]
  refine ⟨46009335428942466573397043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30672890285961644382264695 46009335428942466573397043)
  ·
    refine ⟨69014003143413699860095565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46009335428942466573397043 69014003143413699860095565)
    ·
      refine ⟨25880251178780137447535837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69014003143413699860095565 25880251178780137447535837)
      ·
        refine ⟨9705094192042551542825939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25880251178780137447535837 9705094192042551542825939)
        ·
          refine ⟨14557641288063827314238909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9705094192042551542825939 14557641288063827314238909)
          ·
            refine ⟨5459115483023935242839591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14557641288063827314238909 5459115483023935242839591)
            ·
              refine ⟨8188673224535902864259387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5459115483023935242839591 8188673224535902864259387)
              ·
                refine ⟨12283009836803854296389081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8188673224535902864259387 12283009836803854296389081)
                ·
                  refine ⟨9212257377602890722291811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12283009836803854296389081 9212257377602890722291811)
                  ·
                    refine ⟨13818386066404336083437717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9212257377602890722291811 13818386066404336083437717)
                    ·
                      refine ⟨647736846862703253911143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13818386066404336083437717 647736846862703253911143)
                      ·
                        rfl

theorem cell23_1261463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1261463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261463 prefixEnd_1261463 := by exact prefixLift 1261463
  have htrace : WordTrace (prefixWord ++ tailWord_1261463) baseStart_1261463 baseEnd_1261463 := by
    simpa [prefixWord, tailWord_1261463, baseEnd_1261463] using wordTrace_append hprefix tailTrace_1261463
  have hstable : (prefixWord ++ tailWord_1261463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261463).length < 2 ^ (prefixWord ++ tailWord_1261463).sum := by decide
  have hdescent : baseEnd_1261463 < baseStart_1261463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261483 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3]
def baseStart_1261483 : Nat := 118140960795 + 1261483 * 2 ^ 59
def prefixEnd_1261483 : Nat := 4983230072969 + 3 ^ 40 * 1261483 * 2
def baseEnd_1261483 : Nat := 647747116475793175661051

theorem tailTrace_1261483 : CollatzResearch.WordTrace tailWord_1261483 prefixEnd_1261483 647747116475793175661051 := by
  unfold tailWord_1261483
  simp only [CollatzResearch.WordTrace]
  refine ⟨46010064888870009989125103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30673376592580006659416735 46010064888870009989125103)
  ·
    refine ⟨69015097333305014983687655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46010064888870009989125103 69015097333305014983687655)
    ·
      refine ⟨103522645999957522475531483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69015097333305014983687655 103522645999957522475531483)
      ·
        refine ⟨155283968999936283713297225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103522645999957522475531483 155283968999936283713297225)
        ·
          refine ⟨116462976749952212784972919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155283968999936283713297225 116462976749952212784972919)
          ·
            refine ⟨174694465124928319177459379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116462976749952212784972919 174694465124928319177459379)
            ·
              refine ⟨262041697687392478766189069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174694465124928319177459379 262041697687392478766189069)
              ·
                refine ⟨98265636632772179537320901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262041697687392478766189069 98265636632772179537320901)
                ·
                  refine ⟨18424806868644783663247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98265636632772179537320901 18424806868644783663247669)
                  ·
                    refine ⟨1727325643935448468429469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18424806868644783663247669 1727325643935448468429469)
                    ·
                      refine ⟨647747116475793175661051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727325643935448468429469 647747116475793175661051)
                      ·
                        rfl

theorem cell23_1261483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 3].length) (baseStart_1261483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261483 prefixEnd_1261483 := by exact prefixLift 1261483
  have htrace : WordTrace (prefixWord ++ tailWord_1261483) baseStart_1261483 baseEnd_1261483 := by
    simpa [prefixWord, tailWord_1261483, baseEnd_1261483] using wordTrace_append hprefix tailTrace_1261483
  have hstable : (prefixWord ++ tailWord_1261483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261483).length < 2 ^ (prefixWord ++ tailWord_1261483).sum := by decide
  have hdescent : baseEnd_1261483 < baseStart_1261483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261520 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_1261520 : Nat := 118140960795 + 1261520 * 2 ^ 59
def prefixEnd_1261520 : Nat := 4983230072969 + 3 ^ 40 * 1261520 * 2
def baseEnd_1261520 : Nat := 215922038420003176966127

theorem tailTrace_1261520 : CollatzResearch.WordTrace tailWord_1261520 prefixEnd_1261520 215922038420003176966127 := by
  unfold tailWord_1261520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23005707194867982654111007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30674276259823976872148009 23005707194867982654111007)
  ·
    refine ⟨34508560792301973981166511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23005707194867982654111007 34508560792301973981166511)
    ·
      refine ⟨51762841188452960971749767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34508560792301973981166511 51762841188452960971749767)
      ·
        refine ⟨77644261782679441457624651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51762841188452960971749767 77644261782679441457624651)
        ·
          refine ⟨116466392674019162186436977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77644261782679441457624651 116466392674019162186436977)
          ·
            refine ⟨87349794505514371639827733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116466392674019162186436977 87349794505514371639827733)
            ·
              refine ⟨4094521617445986170616925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87349794505514371639827733 4094521617445986170616925)
              ·
                refine ⟨1535445606542244813981347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4094521617445986170616925 1535445606542244813981347)
                ·
                  refine ⟨2303168409813367220972021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1535445606542244813981347 2303168409813367220972021)
                  ·
                    refine ⟨215922038420003176966127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2303168409813367220972021 215922038420003176966127)
                    ·
                      rfl

theorem cell23_1261520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_1261520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261520 prefixEnd_1261520 := by exact prefixLift 1261520
  have htrace : WordTrace (prefixWord ++ tailWord_1261520) baseStart_1261520 baseEnd_1261520 := by
    simpa [prefixWord, tailWord_1261520, baseEnd_1261520] using wordTrace_append hprefix tailTrace_1261520
  have hstable : (prefixWord ++ tailWord_1261520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261520).length < 2 ^ (prefixWord ++ tailWord_1261520).sum := by decide
  have hdescent : baseEnd_1261520 < baseStart_1261520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261527 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_1261527 : Nat := 118140960795 + 1261527 * 2 ^ 59
def prefixEnd_1261527 : Nat := 4983230072969 + 3 ^ 40 * 1261527 * 2
def baseEnd_1261527 : Nat := 647769709624591003510849

theorem tailTrace_1261527 : CollatzResearch.WordTrace tailWord_1261527 prefixEnd_1261527 647769709624591003510849 := by
  unfold tailWord_1261527
  simp only [CollatzResearch.WordTrace]
  refine ⟨46011669700710605503726835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30674446467140403669151223 46011669700710605503726835)
  ·
    refine ⟨69017504551065908255590253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46011669700710605503726835 69017504551065908255590253)
    ·
      refine ⟨25881564206649715595846345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69017504551065908255590253 25881564206649715595846345)
      ·
        refine ⟨19411173154987286696884759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25881564206649715595846345 19411173154987286696884759)
        ·
          refine ⟨29116759732480930045327139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19411173154987286696884759 29116759732480930045327139)
          ·
            refine ⟨43675139598721395067990709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29116759732480930045327139 43675139598721395067990709)
            ·
              refine ⟨4094544337380130787624129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43675139598721395067990709 4094544337380130787624129)
              ·
                refine ⟨3070908253035098090718097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4094544337380130787624129 3070908253035098090718097)
                ·
                  refine ⟨2303181189776323568038573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3070908253035098090718097 2303181189776323568038573)
                  ·
                    refine ⟨863692946166121338014465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2303181189776323568038573 863692946166121338014465)
                    ·
                      refine ⟨647769709624591003510849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863692946166121338014465 647769709624591003510849)
                      ·
                        rfl

theorem cell23_1261527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_1261527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261527 prefixEnd_1261527 := by exact prefixLift 1261527
  have htrace : WordTrace (prefixWord ++ tailWord_1261527) baseStart_1261527 baseEnd_1261527 := by
    simpa [prefixWord, tailWord_1261527, baseEnd_1261527] using wordTrace_append hprefix tailTrace_1261527
  have hstable : (prefixWord ++ tailWord_1261527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261527).length < 2 ^ (prefixWord ++ tailWord_1261527).sum := by decide
  have hdescent : baseEnd_1261527 < baseStart_1261527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261540 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1261540 : Nat := 118140960795 + 1261540 * 2 ^ 59
def prefixEnd_1261540 : Nat := 4983230072969 + 3 ^ 40 * 1261540 * 2
def baseEnd_1261540 : Nat := 647776384873099452648289

theorem tailTrace_1261540 : CollatzResearch.WordTrace tailWord_1261540 prefixEnd_1261540 647776384873099452648289 := by
  unfold tailWord_1261540
  simp only [CollatzResearch.WordTrace]
  refine ⟨23006071924831754361975037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30674762566442339149300049 23006071924831754361975037)
  ·
    refine ⟨8627276971811907885740639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23006071924831754361975037 8627276971811907885740639)
    ·
      refine ⟨12940915457717861828610959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8627276971811907885740639 12940915457717861828610959)
      ·
        refine ⟨19411373186576792742916439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12940915457717861828610959 19411373186576792742916439)
        ·
          refine ⟨29117059779865189114374659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19411373186576792742916439 29117059779865189114374659)
          ·
            refine ⟨43675589669797783671561989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29117059779865189114374659 43675589669797783671561989)
            ·
              refine ⟨8189173063087084438417873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43675589669797783671561989 8189173063087084438417873)
              ·
                refine ⟨6141879797315313328813405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8189173063087084438417873 6141879797315313328813405)
                ·
                  refine ⟨2303204923993242498305027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6141879797315313328813405 2303204923993242498305027)
                  ·
                    refine ⟨3454807385989863747457541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2303204923993242498305027 3454807385989863747457541)
                    ·
                      refine ⟨647776384873099452648289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3454807385989863747457541 647776384873099452648289)
                      ·
                        rfl

theorem cell23_1261540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1261540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261540 prefixEnd_1261540 := by exact prefixLift 1261540
  have htrace : WordTrace (prefixWord ++ tailWord_1261540) baseStart_1261540 baseEnd_1261540 := by
    simpa [prefixWord, tailWord_1261540, baseEnd_1261540] using wordTrace_append hprefix tailTrace_1261540
  have hstable : (prefixWord ++ tailWord_1261540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261540).length < 2 ^ (prefixWord ++ tailWord_1261540).sum := by decide
  have hdescent : baseEnd_1261540 < baseStart_1261540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261563 : List Nat := [1, 1, 1, 1, 1, 3, 6, 9]
def baseStart_1261563 : Nat := 118140960795 + 1261563 * 2 ^ 59
def prefixEnd_1261563 : Nat := 4983230072969 + 3 ^ 40 * 1261563 * 2
def baseEnd_1261563 : Nat := 23992155367709365283729

theorem tailTrace_1261563 : CollatzResearch.WordTrace tailWord_1261563 prefixEnd_1261563 23992155367709365283729 := by
  unfold tailWord_1261563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46012982728580183652037343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30675321819053455768024895 46012982728580183652037343)
  ·
    refine ⟨69019474092870275478056015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46012982728580183652037343 69019474092870275478056015)
    ·
      refine ⟨103529211139305413217084023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69019474092870275478056015 103529211139305413217084023)
      ·
        refine ⟨155293816708958119825626035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103529211139305413217084023 155293816708958119825626035)
        ·
          refine ⟨232940725063437179738439053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155293816708958119825626035 232940725063437179738439053)
          ·
            refine ⟨87352771898788942401914645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232940725063437179738439053 87352771898788942401914645)
            ·
              refine ⟨4094661182755731675089749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87352771898788942401914645 4094661182755731675089749)
              ·
                refine ⟨23992155367709365283729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4094661182755731675089749 23992155367709365283729)
                ·
                  rfl

theorem cell23_1261563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 9].length) (baseStart_1261563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261563 prefixEnd_1261563 := by exact prefixLift 1261563
  have htrace : WordTrace (prefixWord ++ tailWord_1261563) baseStart_1261563 baseEnd_1261563 := by
    simpa [prefixWord, tailWord_1261563, baseEnd_1261563] using wordTrace_append hprefix tailTrace_1261563
  have hstable : (prefixWord ++ tailWord_1261563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261563).length < 2 ^ (prefixWord ++ tailWord_1261563).sum := by decide
  have hdescent : baseEnd_1261563 < baseStart_1261563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261597 : List Nat := [1, 4, 2, 2, 2, 3, 1, 8]
def baseStart_1261597 : Nat := 118140960795 + 1261597 * 2 ^ 59
def prefixEnd_1261597 : Nat := 4983230072969 + 3 ^ 40 * 1261597 * 2
def baseEnd_1261597 : Nat := 23992801972977989986501

theorem tailTrace_1261597 : CollatzResearch.WordTrace tailWord_1261597 prefixEnd_1261597 23992801972977989986501 := by
  unfold tailWord_1261597
  simp only [CollatzResearch.WordTrace]
  refine ⟨46014222810457007458775045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30676148540304671639183363 46014222810457007458775045)
  ·
    refine ⟨8627666776960688898520321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46014222810457007458775045 8627666776960688898520321)
    ·
      refine ⟨6470750082720516673890241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8627666776960688898520321 6470750082720516673890241)
      ·
        refine ⟨4853062562040387505417681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6470750082720516673890241 4853062562040387505417681)
        ·
          refine ⟨3639796921530290629063261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4853062562040387505417681 3639796921530290629063261)
          ·
            refine ⟨1364923845573858985898723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3639796921530290629063261 1364923845573858985898723)
            ·
              refine ⟨2047385768360788478848085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364923845573858985898723 2047385768360788478848085)
              ·
                refine ⟨23992801972977989986501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2047385768360788478848085 23992801972977989986501)
                ·
                  rfl

theorem cell23_1261597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 8].length) (baseStart_1261597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261597 prefixEnd_1261597 := by exact prefixLift 1261597
  have htrace : WordTrace (prefixWord ++ tailWord_1261597) baseStart_1261597 baseEnd_1261597 := by
    simpa [prefixWord, tailWord_1261597, baseEnd_1261597] using wordTrace_append hprefix tailTrace_1261597
  have hstable : (prefixWord ++ tailWord_1261597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261597).length < 2 ^ (prefixWord ++ tailWord_1261597).sum := by decide
  have hdescent : baseEnd_1261597 < baseStart_1261597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261604 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1261604 : Nat := 118140960795 + 1261604 * 2 ^ 59
def prefixEnd_1261604 : Nat := 4983230072969 + 3 ^ 40 * 1261604 * 2
def baseEnd_1261604 : Nat := 647809247634987202247995

theorem tailTrace_1261604 : CollatzResearch.WordTrace tailWord_1261604 prefixEnd_1261604 647809247634987202247995 := by
  unfold tailWord_1261604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007239060715823827139933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30676318747621098436186577 23007239060715823827139933)
  ·
    refine ⟨8627714647768433935177475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23007239060715823827139933 8627714647768433935177475)
    ·
      refine ⟨12941571971652650902766213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8627714647768433935177475 12941571971652650902766213)
      ·
        refine ⟨2426544744684872044268665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12941571971652650902766213 2426544744684872044268665)
        ·
          refine ⟨1819908558513654033201499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426544744684872044268665 1819908558513654033201499)
          ·
            refine ⟨2729862837770481049802249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819908558513654033201499 2729862837770481049802249)
            ·
              refine ⟨2047397128327860787351687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2729862837770481049802249 2047397128327860787351687)
              ·
                refine ⟨3071095692491791181027531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047397128327860787351687 3071095692491791181027531)
                ·
                  refine ⟨4606643538737686771541297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071095692491791181027531 4606643538737686771541297)
                  ·
                    refine ⟨3454982654053265078655973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4606643538737686771541297 3454982654053265078655973)
                    ·
                      refine ⟨647809247634987202247995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3454982654053265078655973 647809247634987202247995)
                      ·
                        rfl

theorem cell23_1261604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1261604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261604 prefixEnd_1261604 := by exact prefixLift 1261604
  have htrace : WordTrace (prefixWord ++ tailWord_1261604) baseStart_1261604 baseEnd_1261604 := by
    simpa [prefixWord, tailWord_1261604, baseEnd_1261604] using wordTrace_append hprefix tailTrace_1261604
  have hstable : (prefixWord ++ tailWord_1261604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261604).length < 2 ^ (prefixWord ++ tailWord_1261604).sum := by decide
  have hdescent : baseEnd_1261604 < baseStart_1261604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261608 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1261608 : Nat := 118140960795 + 1261608 * 2 ^ 59
def prefixEnd_1261608 : Nat := 4983230072969 + 3 ^ 40 * 1261608 * 2
def baseEnd_1261608 : Nat := 647811301557605186597977

theorem tailTrace_1261608 : CollatzResearch.WordTrace tailWord_1261608 prefixEnd_1261608 647811301557605186597977 := by
  unfold tailWord_1261608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23007312006708578168712739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30676416008944770891616985 23007312006708578168712739)
  ·
    refine ⟨34510968010062867253069109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23007312006708578168712739 34510968010062867253069109)
    ·
      refine ⟨3235403250943393804975229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34510968010062867253069109 3235403250943393804975229)
      ·
        refine ⟨1213276219103772676865711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3235403250943393804975229 1213276219103772676865711)
        ·
          refine ⟨1819914328655659015298567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213276219103772676865711 1819914328655659015298567)
          ·
            refine ⟨2729871492983488522947851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1819914328655659015298567 2729871492983488522947851)
            ·
              refine ⟨4094807239475232784421777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2729871492983488522947851 4094807239475232784421777)
              ·
                refine ⟨3071105429606424588316333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4094807239475232784421777 3071105429606424588316333)
                ·
                  refine ⟨1151664536102409220618625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3071105429606424588316333 1151664536102409220618625)
                  ·
                    refine ⟨863748402076806915463969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1151664536102409220618625 863748402076806915463969)
                    ·
                      refine ⟨647811301557605186597977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863748402076806915463969 647811301557605186597977)
                      ·
                        rfl

theorem cell23_1261608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1261608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261608 prefixEnd_1261608 := by exact prefixLift 1261608
  have htrace : WordTrace (prefixWord ++ tailWord_1261608) baseStart_1261608 baseEnd_1261608 := by
    simpa [prefixWord, tailWord_1261608, baseEnd_1261608] using wordTrace_append hprefix tailTrace_1261608
  have hstable : (prefixWord ++ tailWord_1261608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261608).length < 2 ^ (prefixWord ++ tailWord_1261608).sum := by decide
  have hdescent : baseEnd_1261608 < baseStart_1261608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261664 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2]
def baseStart_1261664 : Nat := 118140960795 + 1261664 * 2 ^ 59
def prefixEnd_1261664 : Nat := 4983230072969 + 3 ^ 40 * 1261664 * 2
def baseEnd_1261664 : Nat := 647840056474256967497719

theorem tailTrace_1261664 : CollatzResearch.WordTrace tailWord_1261664 prefixEnd_1261664 647840056474256967497719 := by
  unfold tailWord_1261664
  simp only [CollatzResearch.WordTrace]
  refine ⟨23008333250607138950732023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30677777667476185267642697 23008333250607138950732023)
  ·
    refine ⟨34512499875910708426098035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23008333250607138950732023 34512499875910708426098035)
    ·
      refine ⟨51768749813866062639147053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34512499875910708426098035 51768749813866062639147053)
      ·
        refine ⟨19413281180199773489680145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51768749813866062639147053 19413281180199773489680145)
        ·
          refine ⟨14559960885149830117260109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19413281180199773489680145 14559960885149830117260109)
          ·
            refine ⟨5459985331931186293972541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14559960885149830117260109 5459985331931186293972541)
            ·
              refine ⟨2047494499474194860239703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5459985331931186293972541 2047494499474194860239703)
              ·
                refine ⟨3071241749211292290359555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047494499474194860239703 3071241749211292290359555)
                ·
                  refine ⟨4606862623816938435539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3071241749211292290359555 4606862623816938435539333)
                  ·
                    refine ⟨863786741965675956663625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4606862623816938435539333 863786741965675956663625)
                    ·
                      refine ⟨647840056474256967497719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 863786741965675956663625 647840056474256967497719)
                      ·
                        rfl

theorem cell23_1261664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_1261664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261664 prefixEnd_1261664 := by exact prefixLift 1261664
  have htrace : WordTrace (prefixWord ++ tailWord_1261664) baseStart_1261664 baseEnd_1261664 := by
    simpa [prefixWord, tailWord_1261664, baseEnd_1261664] using wordTrace_append hprefix tailTrace_1261664
  have hstable : (prefixWord ++ tailWord_1261664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261664).length < 2 ^ (prefixWord ++ tailWord_1261664).sum := by decide
  have hdescent : baseEnd_1261664 < baseStart_1261664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261704 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 7]
def baseStart_1261704 : Nat := 118140960795 + 1261704 * 2 ^ 59
def prefixEnd_1261704 : Nat := 4983230072969 + 3 ^ 40 * 1261704 * 2
def baseEnd_1261704 : Nat := 71984510633381867888615

theorem tailTrace_1261704 : CollatzResearch.WordTrace tailWord_1261704 prefixEnd_1261704 71984510633381867888615 := by
  unfold tailWord_1261704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23009062710534682366460083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30678750280712909821946777 23009062710534682366460083)
  ·
    refine ⟨34513594065802023549690125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23009062710534682366460083 34513594065802023549690125)
    ·
      refine ⟨12942597774675758831133797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34513594065802023549690125 12942597774675758831133797)
      ·
        refine ⟨2426737082751704780837587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12942597774675758831133797 2426737082751704780837587)
        ·
          refine ⟨3640105624127557171256381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2426737082751704780837587 3640105624127557171256381)
          ·
            refine ⟨1365039609047833939221143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3640105624127557171256381 1365039609047833939221143)
            ·
              refine ⟨2047559413571750908831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365039609047833939221143 2047559413571750908831715)
              ·
                refine ⟨3071339120357626363247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2047559413571750908831715 3071339120357626363247573)
                ·
                  refine ⟨71984510633381867888615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3071339120357626363247573 71984510633381867888615)
                  ·
                    rfl

theorem cell23_1261704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_1261704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261704 prefixEnd_1261704 := by exact prefixLift 1261704
  have htrace : WordTrace (prefixWord ++ tailWord_1261704) baseStart_1261704 baseEnd_1261704 := by
    simpa [prefixWord, tailWord_1261704, baseEnd_1261704] using wordTrace_append hprefix tailTrace_1261704
  have hstable : (prefixWord ++ tailWord_1261704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261704).length < 2 ^ (prefixWord ++ tailWord_1261704).sum := by decide
  have hdescent : baseEnd_1261704 < baseStart_1261704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261757 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1261757 : Nat := 118140960795 + 1261757 * 2 ^ 59
def prefixEnd_1261757 : Nat := 4983230072969 + 3 ^ 40 * 1261757 * 2
def baseEnd_1261757 : Nat := 647887810175125103634791

theorem tailTrace_1261757 : CollatzResearch.WordTrace tailWord_1261757 prefixEnd_1261757 647887810175125103634791 := by
  unfold tailWord_1261757
  simp only [CollatzResearch.WordTrace]
  refine ⟨46020058489877354784599525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30680038993251569856399683 46020058489877354784599525)
  ·
    refine ⟨8628760966852004022112411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46020058489877354784599525 8628760966852004022112411)
    ·
      refine ⟨12943141450278006033168617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8628760966852004022112411 12943141450278006033168617)
      ·
        refine ⟨9707356087708504524876463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12943141450278006033168617 9707356087708504524876463)
        ·
          refine ⟨14561034131562756787314695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9707356087708504524876463 14561034131562756787314695)
          ·
            refine ⟨21841551197344135180972043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14561034131562756787314695 21841551197344135180972043)
            ·
              refine ⟨32762326796016202771458065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21841551197344135180972043 32762326796016202771458065)
              ·
                refine ⟨24571745097012152078593549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32762326796016202771458065 24571745097012152078593549)
                ·
                  refine ⟨9214404411379557029472581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24571745097012152078593549 9214404411379557029472581)
                  ·
                    refine ⟨1727700827133666943026109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9214404411379557029472581 1727700827133666943026109)
                    ·
                      refine ⟨647887810175125103634791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727700827133666943026109 647887810175125103634791)
                      ·
                        rfl

theorem cell23_1261757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1261757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261757 prefixEnd_1261757 := by exact prefixLift 1261757
  have htrace : WordTrace (prefixWord ++ tailWord_1261757) baseStart_1261757 baseEnd_1261757 := by
    simpa [prefixWord, tailWord_1261757, baseEnd_1261757] using wordTrace_append hprefix tailTrace_1261757
  have hstable : (prefixWord ++ tailWord_1261757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261757).length < 2 ^ (prefixWord ++ tailWord_1261757).sum := by decide
  have hdescent : baseEnd_1261757 < baseStart_1261757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261777 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 6]
def baseStart_1261777 : Nat := 118140960795 + 1261777 * 2 ^ 59
def prefixEnd_1261777 : Nat := 4983230072969 + 3 ^ 40 * 1261777 * 2
def baseEnd_1261777 : Nat := 71988675532023891709411

theorem tailTrace_1261777 : CollatzResearch.WordTrace tailWord_1261777 prefixEnd_1261777 71988675532023891709411 := by
  unfold tailWord_1261777
  simp only [CollatzResearch.WordTrace]
  refine ⟨46020787949804898200327585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30680525299869932133551723 46020787949804898200327585)
  ·
    refine ⟨34515590962353673650245689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46020787949804898200327585 34515590962353673650245689)
    ·
      refine ⟨25886693221765255237684267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34515590962353673650245689 25886693221765255237684267)
      ·
        refine ⟨38830039832647882856526401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25886693221765255237684267 38830039832647882856526401)
        ·
          refine ⟨29122529874485912142394801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38830039832647882856526401 29122529874485912142394801)
          ·
            refine ⟨21841897405864434106796101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29122529874485912142394801 21841897405864434106796101)
            ·
              refine ⟨4095355763599581395024269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21841897405864434106796101 4095355763599581395024269)
              ·
                refine ⟨1535758411349843023134101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4095355763599581395024269 1535758411349843023134101)
                ·
                  refine ⟨71988675532023891709411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1535758411349843023134101 71988675532023891709411)
                  ·
                    rfl

theorem cell23_1261777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_1261777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261777 prefixEnd_1261777 := by exact prefixLift 1261777
  have htrace : WordTrace (prefixWord ++ tailWord_1261777) baseStart_1261777 baseEnd_1261777 := by
    simpa [prefixWord, tailWord_1261777, baseEnd_1261777] using wordTrace_append hprefix tailTrace_1261777
  have hstable : (prefixWord ++ tailWord_1261777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261777).length < 2 ^ (prefixWord ++ tailWord_1261777).sum := by decide
  have hdescent : baseEnd_1261777 < baseStart_1261777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261781 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1261781 : Nat := 118140960795 + 1261781 * 2 ^ 59
def prefixEnd_1261781 : Nat := 4983230072969 + 3 ^ 40 * 1261781 * 2
def baseEnd_1261781 : Nat := 215966711236944336578227

theorem tailTrace_1261781 : CollatzResearch.WordTrace tailWord_1261781 prefixEnd_1261781 215966711236944336578227 := by
  unfold tailWord_1261781
  simp only [CollatzResearch.WordTrace]
  refine ⟨46020933841790406883473197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30680622561193604588982131 46020933841790406883473197)
  ·
    refine ⟨17257850190671402581302449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46020933841790406883473197 17257850190671402581302449)
    ·
      refine ⟨12943387643003551935976837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17257850190671402581302449 12943387643003551935976837)
      ·
        refine ⟨2426885183063165987995657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12943387643003551935976837 2426885183063165987995657)
        ·
          refine ⟨1820163887297374490996743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2426885183063165987995657 1820163887297374490996743)
          ·
            refine ⟨2730245830946061736495115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820163887297374490996743 2730245830946061736495115)
            ·
              refine ⟨4095368746419092604742673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730245830946061736495115 4095368746419092604742673)
              ·
                refine ⟨3071526559814319453557005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4095368746419092604742673 3071526559814319453557005)
                ·
                  refine ⟨1151822459930369795083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3071526559814319453557005 1151822459930369795083877)
                  ·
                    refine ⟨215966711236944336578227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1151822459930369795083877 215966711236944336578227)
                    ·
                      rfl

theorem cell23_1261781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1261781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261781 prefixEnd_1261781 := by exact prefixLift 1261781
  have htrace : WordTrace (prefixWord ++ tailWord_1261781) baseStart_1261781 baseEnd_1261781 := by
    simpa [prefixWord, tailWord_1261781, baseEnd_1261781] using wordTrace_append hprefix tailTrace_1261781
  have hstable : (prefixWord ++ tailWord_1261781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261781).length < 2 ^ (prefixWord ++ tailWord_1261781).sum := by decide
  have hdescent : baseEnd_1261781 < baseStart_1261781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261804 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_1261804 : Nat := 118140960795 + 1261804 * 2 ^ 59
def prefixEnd_1261804 : Nat := 4983230072969 + 3 ^ 40 * 1261804 * 2
def baseEnd_1261804 : Nat := 647911943765886419747075

theorem tailTrace_1261804 : CollatzResearch.WordTrace tailWord_1261804 prefixEnd_1261804 647911943765886419747075 := by
  unfold tailWord_1261804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23010886360353540905780233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30681181813804721207706977 23010886360353540905780233)
  ·
    refine ⟨17258164770265155679335175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23010886360353540905780233 17258164770265155679335175)
    ·
      refine ⟨25887247155397733519002763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17258164770265155679335175 25887247155397733519002763)
      ·
        refine ⟨38830870733096600278504145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25887247155397733519002763 38830870733096600278504145)
        ·
          refine ⟨29123153049822450208878109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38830870733096600278504145 29123153049822450208878109)
          ·
            refine ⟨10921182393683418828329291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29123153049822450208878109 10921182393683418828329291)
            ·
              refine ⟨16381773590525128242493937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921182393683418828329291 16381773590525128242493937)
              ·
                refine ⟨12286330192893846181870453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16381773590525128242493937 12286330192893846181870453)
                ·
                  refine ⟨1151843455583798079550355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12286330192893846181870453 1151843455583798079550355)
                  ·
                    refine ⟨1727765183375697119325533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1151843455583798079550355 1727765183375697119325533)
                    ·
                      refine ⟨647911943765886419747075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727765183375697119325533 647911943765886419747075)
                      ·
                        rfl

theorem cell23_1261804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_1261804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261804 prefixEnd_1261804 := by exact prefixLift 1261804
  have htrace : WordTrace (prefixWord ++ tailWord_1261804) baseStart_1261804 baseEnd_1261804 := by
    simpa [prefixWord, tailWord_1261804, baseEnd_1261804] using wordTrace_append hprefix tailTrace_1261804
  have hstable : (prefixWord ++ tailWord_1261804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261804).length < 2 ^ (prefixWord ++ tailWord_1261804).sum := by decide
  have hdescent : baseEnd_1261804 < baseStart_1261804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261855 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 1, 1, 3]
def baseStart_1261855 : Nat := 118140960795 + 1261855 * 2 ^ 59
def prefixEnd_1261855 : Nat := 4983230072969 + 3 ^ 40 * 1261855 * 2
def baseEnd_1261855 : Nat := 647938131279265720209341

theorem tailTrace_1261855 : CollatzResearch.WordTrace tailWord_1261855 prefixEnd_1261855 647938131279265720209341 := by
  unfold tailWord_1261855
  simp only [CollatzResearch.WordTrace]
  refine ⟨46023632843522317521667019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30682421895681545014444679 46023632843522317521667019)
  ·
    refine ⟨69035449265283476282500529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46023632843522317521667019 69035449265283476282500529)
    ·
      refine ⟨51776586948962607211875397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69035449265283476282500529 51776586948962607211875397)
      ·
        refine ⟨9708110052930488852226637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51776586948962607211875397 9708110052930488852226637)
        ·
          refine ⟨3640541269848933319584989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9708110052930488852226637 3640541269848933319584989)
          ·
            refine ⟨1365202976193349994844371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3640541269848933319584989 1365202976193349994844371)
            ·
              refine ⟨2047804464290024992266557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365202976193349994844371 2047804464290024992266557)
              ·
                refine ⟨767926674108759372099959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2047804464290024992266557 767926674108759372099959)
                ·
                  refine ⟨1151890011163139058149939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 767926674108759372099959 1151890011163139058149939)
                  ·
                    refine ⟨1727835016744708587224909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1151890011163139058149939 1727835016744708587224909)
                    ·
                      refine ⟨647938131279265720209341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727835016744708587224909 647938131279265720209341)
                      ·
                        rfl

theorem cell23_1261855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_1261855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261855 prefixEnd_1261855 := by exact prefixLift 1261855
  have htrace : WordTrace (prefixWord ++ tailWord_1261855) baseStart_1261855 baseEnd_1261855 := by
    simpa [prefixWord, tailWord_1261855, baseEnd_1261855] using wordTrace_append hprefix tailTrace_1261855
  have hstable : (prefixWord ++ tailWord_1261855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261855).length < 2 ^ (prefixWord ++ tailWord_1261855).sum := by decide
  have hdescent : baseEnd_1261855 < baseStart_1261855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261887 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1261887 : Nat := 118140960795 + 1261887 * 2 ^ 59
def prefixEnd_1261887 : Nat := 4983230072969 + 3 ^ 40 * 1261887 * 2
def baseEnd_1261887 : Nat := 647954562660209595009193

theorem tailTrace_1261887 : CollatzResearch.WordTrace tailWord_1261887 prefixEnd_1261887 647954562660209595009193 := by
  unfold tailWord_1261887
  simp only [CollatzResearch.WordTrace]
  refine ⟨46024799979406386986831915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30683199986270924657887943 46024799979406386986831915)
  ·
    refine ⟨69037199969109580480247873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46024799979406386986831915 69037199969109580480247873)
    ·
      refine ⟨51777899976832185360185905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69037199969109580480247873 51777899976832185360185905)
      ·
        refine ⟨38833424982624139020139429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51777899976832185360185905 38833424982624139020139429)
        ·
          refine ⟨7281267184242026066276143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38833424982624139020139429 7281267184242026066276143)
          ·
            refine ⟨10921900776363039099414215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7281267184242026066276143 10921900776363039099414215)
            ·
              refine ⟨16382851164544558649121323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10921900776363039099414215 16382851164544558649121323)
              ·
                refine ⟨24574276746816837973681985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16382851164544558649121323 24574276746816837973681985)
                ·
                  refine ⟨18430707560112628480261489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24574276746816837973681985 18430707560112628480261489)
                  ·
                    refine ⟨13823030670084471360196117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18430707560112628480261489 13823030670084471360196117)
                    ·
                      refine ⟨647954562660209595009193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13823030670084471360196117 647954562660209595009193)
                      ·
                        rfl

theorem cell23_1261887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1261887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261887 prefixEnd_1261887 := by exact prefixLift 1261887
  have htrace : WordTrace (prefixWord ++ tailWord_1261887) baseStart_1261887 baseEnd_1261887 := by
    simpa [prefixWord, tailWord_1261887, baseEnd_1261887] using wordTrace_append hprefix tailTrace_1261887
  have hstable : (prefixWord ++ tailWord_1261887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261887).length < 2 ^ (prefixWord ++ tailWord_1261887).sum := by decide
  have hdescent : baseEnd_1261887 < baseStart_1261887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261907 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_1261907 : Nat := 118140960795 + 1261907 * 2 ^ 59
def prefixEnd_1261907 : Nat := 4983230072969 + 3 ^ 40 * 1261907 * 2
def baseEnd_1261907 : Nat := 647964832273299516759101

theorem tailTrace_1261907 : CollatzResearch.WordTrace tailWord_1261907 prefixEnd_1261907 647964832273299516759101 := by
  unfold tailWord_1261907
  simp only [CollatzResearch.WordTrace]
  refine ⟨46025529439333930402559975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30683686292889286935039983 46025529439333930402559975)
  ·
    refine ⟨69038294159000895603839963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46025529439333930402559975 69038294159000895603839963)
    ·
      refine ⟨103557441238501343405759945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69038294159000895603839963 103557441238501343405759945)
      ·
        refine ⟨77668080928876007554319959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103557441238501343405759945 77668080928876007554319959)
        ·
          refine ⟨116502121393314011331479939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77668080928876007554319959 116502121393314011331479939)
          ·
            refine ⟨174753182089971016997219909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116502121393314011331479939 174753182089971016997219909)
            ·
              refine ⟨32766221641869565686978733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174753182089971016997219909 32766221641869565686978733)
              ·
                refine ⟨12287333115701087132617025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32766221641869565686978733 12287333115701087132617025)
                ·
                  refine ⟨9215499836775815349462769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12287333115701087132617025 9215499836775815349462769)
                  ·
                    refine ⟨6911624877581861512097077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9215499836775815349462769 6911624877581861512097077)
                    ·
                      refine ⟨647964832273299516759101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6911624877581861512097077 647964832273299516759101)
                      ·
                        rfl

theorem cell23_1261907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_1261907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261907 prefixEnd_1261907 := by exact prefixLift 1261907
  have htrace : WordTrace (prefixWord ++ tailWord_1261907) baseStart_1261907 baseEnd_1261907 := by
    simpa [prefixWord, tailWord_1261907, baseEnd_1261907] using wordTrace_append hprefix tailTrace_1261907
  have hstable : (prefixWord ++ tailWord_1261907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261907).length < 2 ^ (prefixWord ++ tailWord_1261907).sum := by decide
  have hdescent : baseEnd_1261907 < baseStart_1261907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261918 : List Nat := [4, 4, 2, 1, 12]
def baseStart_1261918 : Nat := 118140960795 + 1261918 * 2 ^ 59
def prefixEnd_1261918 : Nat := 4983230072969 + 3 ^ 40 * 1261918 * 2
def baseEnd_1261918 : Nat := 888848395830588441319

theorem tailTrace_1261918 : CollatzResearch.WordTrace tailWord_1261918 prefixEnd_1261918 888848395830588441319 := by
  unfold tailWord_1261918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753241330286759910151301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30683953761529386187473605 5753241330286759910151301)
  ·
    refine ⟨1078732749428767483153369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5753241330286759910151301 1078732749428767483153369)
    ·
      refine ⟨809049562071575612365027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078732749428767483153369 809049562071575612365027)
      ·
        refine ⟨1213574343107363418547541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809049562071575612365027 1213574343107363418547541)
        ·
          refine ⟨888848395830588441319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1213574343107363418547541 888848395830588441319)
          ·
            rfl

theorem cell23_1261918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 12].length) (baseStart_1261918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261918 prefixEnd_1261918 := by exact prefixLift 1261918
  have htrace : WordTrace (prefixWord ++ tailWord_1261918) baseStart_1261918 baseEnd_1261918 := by
    simpa [prefixWord, tailWord_1261918, baseEnd_1261918] using wordTrace_append hprefix tailTrace_1261918
  have hstable : (prefixWord ++ tailWord_1261918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261918).length < 2 ^ (prefixWord ++ tailWord_1261918).sum := by decide
  have hdescent : baseEnd_1261918 < baseStart_1261918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261928 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1261928 : Nat := 118140960795 + 1261928 * 2 ^ 59
def prefixEnd_1261928 : Nat := 4983230072969 + 3 ^ 40 * 1261928 * 2
def baseEnd_1261928 : Nat := 647975615367043934596505

theorem tailTrace_1261928 : CollatzResearch.WordTrace tailWord_1261928 prefixEnd_1261928 647975615367043934596505 := by
  unfold tailWord_1261928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23013147686128925494537219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30684196914838567326049625 23013147686128925494537219)
  ·
    refine ⟨34519721529193388241805829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23013147686128925494537219 34519721529193388241805829)
    ·
      refine ⟨6472447786723760295338593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34519721529193388241805829 6472447786723760295338593)
      ·
        refine ⟨4854335840042820221503945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6472447786723760295338593 4854335840042820221503945)
        ·
          refine ⟨3640751880032115166127959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854335840042820221503945 3640751880032115166127959)
          ·
            refine ⟨5461127820048172749191939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640751880032115166127959 5461127820048172749191939)
            ·
              refine ⟨8191691730072259123787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461127820048172749191939 8191691730072259123787909)
              ·
                refine ⟨1535942199388548585710233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8191691730072259123787909 1535942199388548585710233)
                ·
                  refine ⟨1151956649541411439282675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1535942199388548585710233 1151956649541411439282675)
                  ·
                    refine ⟨1727934974312117158924013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1151956649541411439282675 1727934974312117158924013)
                    ·
                      refine ⟨647975615367043934596505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1727934974312117158924013 647975615367043934596505)
                      ·
                        rfl

theorem cell23_1261928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1261928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261928 prefixEnd_1261928 := by exact prefixLift 1261928
  have htrace : WordTrace (prefixWord ++ tailWord_1261928) baseStart_1261928 baseEnd_1261928 := by
    simpa [prefixWord, tailWord_1261928, baseEnd_1261928] using wordTrace_append hprefix tailTrace_1261928
  have hstable : (prefixWord ++ tailWord_1261928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261928).length < 2 ^ (prefixWord ++ tailWord_1261928).sum := by decide
  have hdescent : baseEnd_1261928 < baseStart_1261928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1261991 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 7]
def baseStart_1261991 : Nat := 118140960795 + 1261991 * 2 ^ 59
def prefixEnd_1261991 : Nat := 4983230072969 + 3 ^ 40 * 1261991 * 2
def baseEnd_1261991 : Nat := 72000884960919687567635

theorem tailTrace_1261991 : CollatzResearch.WordTrace tailWord_1261991 prefixEnd_1261991 72000884960919687567635 := by
  unfold tailWord_1261991
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028593171029612748617827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30685728780686408499078551 46028593171029612748617827)
  ·
    refine ⟨69042889756544419122926741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46028593171029612748617827 69042889756544419122926741)
    ·
      refine ⟨3236385457338019646387191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69042889756544419122926741 3236385457338019646387191)
      ·
        refine ⟨4854578186007029469580787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236385457338019646387191 4854578186007029469580787)
        ·
          refine ⟨7281867279010544204371181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854578186007029469580787 7281867279010544204371181)
          ·
            refine ⟨2730700229628954076639193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7281867279010544204371181 2730700229628954076639193)
            ·
              refine ⟨2048025172221715557479395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2730700229628954076639193 2048025172221715557479395)
              ·
                refine ⟨3072037758332573336219093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048025172221715557479395 3072037758332573336219093)
                ·
                  refine ⟨72000884960919687567635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3072037758332573336219093 72000884960919687567635)
                  ·
                    rfl

theorem cell23_1261991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 7].length) (baseStart_1261991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1261991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1261991 prefixEnd_1261991 := by exact prefixLift 1261991
  have htrace : WordTrace (prefixWord ++ tailWord_1261991) baseStart_1261991 baseEnd_1261991 := by
    simpa [prefixWord, tailWord_1261991, baseEnd_1261991] using wordTrace_append hprefix tailTrace_1261991
  have hstable : (prefixWord ++ tailWord_1261991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1261991).length < 2 ^ (prefixWord ++ tailWord_1261991).sum := by decide
  have hdescent : baseEnd_1261991 < baseStart_1261991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1261991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262001 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1262001 : Nat := 118140960795 + 1262001 * 2 ^ 59
def prefixEnd_1262001 : Nat := 4983230072969 + 3 ^ 40 * 1262001 * 2
def baseEnd_1262001 : Nat := 648013099454822148983669

theorem tailTrace_1262001 : CollatzResearch.WordTrace tailWord_1262001 prefixEnd_1262001 648013099454822148983669 := by
  unfold tailWord_1262001
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028957900993384456481857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30685971933995589637654571 46028957900993384456481857)
  ·
    refine ⟨34521718425745038342361393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46028957900993384456481857 34521718425745038342361393)
    ·
      refine ⟨25891288819308778756771045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34521718425745038342361393 25891288819308778756771045)
      ·
        refine ⟨4854616653620396016894571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25891288819308778756771045 4854616653620396016894571)
        ·
          refine ⟨7281924980430594025341857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854616653620396016894571 7281924980430594025341857)
          ·
            refine ⟨5461443735322945519006393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7281924980430594025341857 5461443735322945519006393)
            ·
              refine ⟨4096082801492209139254795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5461443735322945519006393 4096082801492209139254795)
              ·
                refine ⟨6144124202238313708882193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096082801492209139254795 6144124202238313708882193)
                ·
                  refine ⟨4608093151678735281661645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144124202238313708882193 4608093151678735281661645)
                  ·
                    refine ⟨1728034931879525730623117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4608093151678735281661645 1728034931879525730623117)
                    ·
                      refine ⟨648013099454822148983669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1728034931879525730623117 648013099454822148983669)
                      ·
                        rfl

theorem cell23_1262001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1262001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262001 prefixEnd_1262001 := by exact prefixLift 1262001
  have htrace : WordTrace (prefixWord ++ tailWord_1262001) baseStart_1262001 baseEnd_1262001 := by
    simpa [prefixWord, tailWord_1262001, baseEnd_1262001] using wordTrace_append hprefix tailTrace_1262001
  have hstable : (prefixWord ++ tailWord_1262001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262001).length < 2 ^ (prefixWord ++ tailWord_1262001).sum := by decide
  have hdescent : baseEnd_1262001 < baseStart_1262001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262038 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1262038 : Nat := 118140960795 + 1262038 * 2 ^ 59
def prefixEnd_1262038 : Nat := 4983230072969 + 3 ^ 40 * 1262038 * 2
def baseEnd_1262038 : Nat := 216010699413012834740333

theorem tailTrace_1262038 : CollatzResearch.WordTrace tailWord_1262038 prefixEnd_1262038 216010699413012834740333 := by
  unfold tailWord_1262038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2876894212616208735973673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30686871601239559850385845 2876894212616208735973673)
  ·
    refine ⟨2157670659462156551980255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2876894212616208735973673 2157670659462156551980255)
    ·
      refine ⟨3236505989193234827970383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157670659462156551980255 3236505989193234827970383)
      ·
        refine ⟨4854758983789852241955575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236505989193234827970383 4854758983789852241955575)
        ·
          refine ⟨7282138475684778362933363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854758983789852241955575 7282138475684778362933363)
          ·
            refine ⟨10923207713527167544400045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282138475684778362933363 10923207713527167544400045)
            ·
              refine ⟨4096202892572687829150017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10923207713527167544400045 4096202892572687829150017)
              ·
                refine ⟨3072152169429515871862513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096202892572687829150017 3072152169429515871862513)
                ·
                  refine ⟨2304114127072136903896885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072152169429515871862513 2304114127072136903896885)
                  ·
                    refine ⟨216010699413012834740333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2304114127072136903896885 216010699413012834740333)
                    ·
                      rfl

theorem cell23_1262038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1262038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262038 prefixEnd_1262038 := by exact prefixLift 1262038
  have htrace : WordTrace (prefixWord ++ tailWord_1262038) baseStart_1262038 baseEnd_1262038 := by
    simpa [prefixWord, tailWord_1262038, baseEnd_1262038] using wordTrace_append hprefix tailTrace_1262038
  have hstable : (prefixWord ++ tailWord_1262038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262038).length < 2 ^ (prefixWord ++ tailWord_1262038).sum := by decide
  have hdescent : baseEnd_1262038 < baseStart_1262038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262041 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_1262041 : Nat := 118140960795 + 1262041 * 2 ^ 59
def prefixEnd_1262041 : Nat := 4983230072969 + 3 ^ 40 * 1262041 * 2
def baseEnd_1262041 : Nat := 648033638681001992483485

theorem tailTrace_1262041 : CollatzResearch.WordTrace tailWord_1262041 prefixEnd_1262041 648033638681001992483485 := by
  unfold tailWord_1262041
  simp only [CollatzResearch.WordTrace]
  refine ⟨46030416820848471287937977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30686944547232314191958651 46030416820848471287937977)
  ·
    refine ⟨34522812615636353465953483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46030416820848471287937977 34522812615636353465953483)
    ·
      refine ⟨51784218923454530198930225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34522812615636353465953483 51784218923454530198930225)
      ·
        refine ⟨38838164192590897649197669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51784218923454530198930225 38838164192590897649197669)
        ·
          refine ⟨7282155786110793309224563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38838164192590897649197669 7282155786110793309224563)
          ·
            refine ⟨10923233679166189963836845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282155786110793309224563 10923233679166189963836845)
            ·
              refine ⟨4096212629687321236438817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10923233679166189963836845 4096212629687321236438817)
              ·
                refine ⟨3072159472265490927329113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096212629687321236438817 3072159472265490927329113)
                ·
                  refine ⟨2304119604199118195496835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072159472265490927329113 2304119604199118195496835)
                  ·
                    refine ⟨3456179406298677293245253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304119604199118195496835 3456179406298677293245253)
                    ·
                      refine ⟨648033638681001992483485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3456179406298677293245253 648033638681001992483485)
                      ·
                        rfl

theorem cell23_1262041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_1262041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262041 prefixEnd_1262041 := by exact prefixLift 1262041
  have htrace : WordTrace (prefixWord ++ tailWord_1262041) baseStart_1262041 baseEnd_1262041 := by
    simpa [prefixWord, tailWord_1262041, baseEnd_1262041] using wordTrace_append hprefix tailTrace_1262041
  have hstable : (prefixWord ++ tailWord_1262041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262041).length < 2 ^ (prefixWord ++ tailWord_1262041).sum := by decide
  have hdescent : baseEnd_1262041 < baseStart_1262041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262131 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4]
def baseStart_1262131 : Nat := 118140960795 + 1262131 * 2 ^ 59
def prefixEnd_1262131 : Nat := 4983230072969 + 3 ^ 40 * 1262131 * 2
def baseEnd_1262131 : Nat := 648079851939906640358071

theorem tailTrace_1262131 : CollatzResearch.WordTrace tailWord_1262131 prefixEnd_1262131 648079851939906640358071 := by
  unfold tailWord_1262131
  simp only [CollatzResearch.WordTrace]
  refine ⟨46033699390522416658714247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30689132927014944439142831 46033699390522416658714247)
  ·
    refine ⟨69050549085783624988071371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46033699390522416658714247 69050549085783624988071371)
    ·
      refine ⟨103575823628675437482107057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69050549085783624988071371 103575823628675437482107057)
      ·
        refine ⟨77681867721506578111580293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103575823628675437482107057 77681867721506578111580293)
        ·
          refine ⟨14565350197782483395921305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77681867721506578111580293 14565350197782483395921305)
          ·
            refine ⟨10924012648336862546940979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14565350197782483395921305 10924012648336862546940979)
            ·
              refine ⟨16386018972505293820411469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924012648336862546940979 16386018972505293820411469)
              ·
                refine ⟨6144757114689485182654301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16386018972505293820411469 6144757114689485182654301)
                ·
                  refine ⟨2304283918008556943495363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6144757114689485182654301 2304283918008556943495363)
                  ·
                    refine ⟨3456425877012835415243045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304283918008556943495363 3456425877012835415243045)
                    ·
                      refine ⟨648079851939906640358071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3456425877012835415243045 648079851939906640358071)
                      ·
                        rfl

theorem cell23_1262131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_1262131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262131 prefixEnd_1262131 := by exact prefixLift 1262131
  have htrace : WordTrace (prefixWord ++ tailWord_1262131) baseStart_1262131 baseEnd_1262131 := by
    simpa [prefixWord, tailWord_1262131, baseEnd_1262131] using wordTrace_append hprefix tailTrace_1262131
  have hstable : (prefixWord ++ tailWord_1262131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262131).length < 2 ^ (prefixWord ++ tailWord_1262131).sum := by decide
  have hdescent : baseEnd_1262131 < baseStart_1262131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262145 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1262145 : Nat := 118140960795 + 1262145 * 2 ^ 59
def prefixEnd_1262145 : Nat := 4983230072969 + 3 ^ 40 * 1262145 * 2
def baseEnd_1262145 : Nat := 216029013556356528527669

theorem tailTrace_1262145 : CollatzResearch.WordTrace tailWord_1262145 prefixEnd_1262145 216029013556356528527669 := by
  unfold tailWord_1262145
  simp only [CollatzResearch.WordTrace]
  refine ⟨46034210012471697049723889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30689473341647798033149259 46034210012471697049723889)
  ·
    refine ⟨34525657509353772787292917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46034210012471697049723889 34525657509353772787292917)
    ·
      refine ⟨3236780391501916198808711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34525657509353772787292917 3236780391501916198808711)
      ·
        refine ⟨4855170587252874298213067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3236780391501916198808711 4855170587252874298213067)
        ·
          refine ⟨7282755880879311447319601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855170587252874298213067 7282755880879311447319601)
          ·
            refine ⟨5462066910659483585489701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282755880879311447319601 5462066910659483585489701)
            ·
              refine ⟨1024137545748653172279319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5462066910659483585489701 1024137545748653172279319)
              ·
                refine ⟨1536206318622979758418979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024137545748653172279319 1536206318622979758418979)
                ·
                  refine ⟨2304309477934469637628469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536206318622979758418979 2304309477934469637628469)
                  ·
                    refine ⟨216029013556356528527669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2304309477934469637628469 216029013556356528527669)
                    ·
                      rfl

theorem cell23_1262145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1262145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262145 prefixEnd_1262145 := by exact prefixLift 1262145
  have htrace : WordTrace (prefixWord ++ tailWord_1262145) baseStart_1262145 baseEnd_1262145 := by
    simpa [prefixWord, tailWord_1262145, baseEnd_1262145] using wordTrace_append hprefix tailTrace_1262145
  have hstable : (prefixWord ++ tailWord_1262145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262145).length < 2 ^ (prefixWord ++ tailWord_1262145).sum := by decide
  have hdescent : baseEnd_1262145 < baseStart_1262145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262165 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1262165 : Nat := 118140960795 + 1262165 * 2 ^ 59
def prefixEnd_1262165 : Nat := 4983230072969 + 3 ^ 40 * 1262165 * 2
def baseEnd_1262165 : Nat := 648097310282159507332915

theorem tailTrace_1262165 : CollatzResearch.WordTrace tailWord_1262165 prefixEnd_1262165 648097310282159507332915 := by
  unfold tailWord_1262165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46034939472399240465451949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30689959648266160310301299 46034939472399240465451949)
  ·
    refine ⟨17263102302149715174544481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46034939472399240465451949 17263102302149715174544481)
    ·
      refine ⟨12947326726612286380908361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17263102302149715174544481 12947326726612286380908361)
      ·
        refine ⟨9710495044959214785681271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12947326726612286380908361 9710495044959214785681271)
        ·
          refine ⟨14565742567438822178521907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710495044959214785681271 14565742567438822178521907)
          ·
            refine ⟨21848613851158233267782861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14565742567438822178521907 21848613851158233267782861)
            ·
              refine ⟨8193230194184337475418573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21848613851158233267782861 8193230194184337475418573)
              ·
                refine ⟨3072461322819126553281965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8193230194184337475418573 3072461322819126553281965)
                ·
                  refine ⟨1152172996057172457480737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3072461322819126553281965 1152172996057172457480737)
                  ·
                    refine ⟨864129747042879343110553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1152172996057172457480737 864129747042879343110553)
                    ·
                      refine ⟨648097310282159507332915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864129747042879343110553 648097310282159507332915)
                      ·
                        rfl

theorem cell23_1262165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1262165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262165 prefixEnd_1262165 := by exact prefixLift 1262165
  have htrace : WordTrace (prefixWord ++ tailWord_1262165) baseStart_1262165 baseEnd_1262165 := by
    simpa [prefixWord, tailWord_1262165, baseEnd_1262165] using wordTrace_append hprefix tailTrace_1262165
  have hstable : (prefixWord ++ tailWord_1262165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262165).length < 2 ^ (prefixWord ++ tailWord_1262165).sum := by decide
  have hdescent : baseEnd_1262165 < baseStart_1262165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262210 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1262210 : Nat := 118140960795 + 1262210 * 2 ^ 59
def prefixEnd_1262210 : Nat := 4983230072969 + 3 ^ 40 * 1262210 * 2
def baseEnd_1262210 : Nat := 648120416911611831270209

theorem tailTrace_1262210 : CollatzResearch.WordTrace tailWord_1262210 prefixEnd_1262210 648120416911611831270209 := by
  unfold tailWord_1262210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509145189309053287710021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30691053838157475433893389 11509145189309053287710021)
  ·
    refine ⟨2157964722995447491445629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11509145189309053287710021 2157964722995447491445629)
    ·
      refine ⟨809236771123292809292111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2157964722995447491445629 809236771123292809292111)
      ·
        refine ⟨1213855156684939213938167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809236771123292809292111 1213855156684939213938167)
        ·
          refine ⟨1820782735027408820907251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213855156684939213938167 1820782735027408820907251)
          ·
            refine ⟨2731174102541113231360877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820782735027408820907251 2731174102541113231360877)
            ·
              refine ⟨1024190288452917461760329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731174102541113231360877 1024190288452917461760329)
              ·
                refine ⟨768142716339688096320247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024190288452917461760329 768142716339688096320247)
                ·
                  refine ⟨1152214074509532144480371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768142716339688096320247 1152214074509532144480371)
                  ·
                    refine ⟨1728321111764298216720557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152214074509532144480371 1728321111764298216720557)
                    ·
                      refine ⟨648120416911611831270209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1728321111764298216720557 648120416911611831270209)
                      ·
                        rfl

theorem cell23_1262210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1262210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262210 prefixEnd_1262210 := by exact prefixLift 1262210
  have htrace : WordTrace (prefixWord ++ tailWord_1262210) baseStart_1262210 baseEnd_1262210 := by
    simpa [prefixWord, tailWord_1262210, baseEnd_1262210] using wordTrace_append hprefix tailTrace_1262210
  have hstable : (prefixWord ++ tailWord_1262210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262210).length < 2 ^ (prefixWord ++ tailWord_1262210).sum := by decide
  have hdescent : baseEnd_1262210 < baseStart_1262210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262215 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1262215 : Nat := 118140960795 + 1262215 * 2 ^ 59
def prefixEnd_1262215 : Nat := 4983230072969 + 3 ^ 40 * 1262215 * 2
def baseEnd_1262215 : Nat := 648122984314884311707685

theorem tailTrace_1262215 : CollatzResearch.WordTrace tailWord_1262215 prefixEnd_1262215 648122984314884311707685 := by
  unfold tailWord_1262215
  simp only [CollatzResearch.WordTrace]
  refine ⟨46036763122218099004772099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30691175414812066003181399 46036763122218099004772099)
  ·
    refine ⟨69055144683327148507158149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46036763122218099004772099 69055144683327148507158149)
    ·
      refine ⟨12947839628123840345092153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69055144683327148507158149 12947839628123840345092153)
      ·
        refine ⟨9710879721092880258819115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12947839628123840345092153 9710879721092880258819115)
        ·
          refine ⟨14566319581639320388228673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710879721092880258819115 14566319581639320388228673)
          ·
            refine ⟨10924739686229490291171505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14566319581639320388228673 10924739686229490291171505)
            ·
              refine ⟨8193554764672117718378629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10924739686229490291171505 8193554764672117718378629)
              ·
                refine ⟨1536291518376022072195993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8193554764672117718378629 1536291518376022072195993)
                ·
                  refine ⟨1152218638782016554146995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536291518376022072195993 1152218638782016554146995)
                  ·
                    refine ⟨1728327958173024831220493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152218638782016554146995 1728327958173024831220493)
                    ·
                      refine ⟨648122984314884311707685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1728327958173024831220493 648122984314884311707685)
                      ·
                        rfl

theorem cell23_1262215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1262215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262215 prefixEnd_1262215 := by exact prefixLift 1262215
  have htrace : WordTrace (prefixWord ++ tailWord_1262215) baseStart_1262215 baseEnd_1262215 := by
    simpa [prefixWord, tailWord_1262215, baseEnd_1262215] using wordTrace_append hprefix tailTrace_1262215
  have hstable : (prefixWord ++ tailWord_1262215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262215).length < 2 ^ (prefixWord ++ tailWord_1262215).sum := by decide
  have hdescent : baseEnd_1262215 < baseStart_1262215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262231 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 8]
def baseStart_1262231 : Nat := 118140960795 + 1262231 * 2 ^ 59
def prefixEnd_1262231 : Nat := 4983230072969 + 3 ^ 40 * 1262231 * 2
def baseEnd_1262231 : Nat := 216043733335118749702537

theorem tailTrace_1262231 : CollatzResearch.WordTrace tailWord_1262231 prefixEnd_1262231 216043733335118749702537 := by
  unfold tailWord_1262231
  simp only [CollatzResearch.WordTrace]
  refine ⟨46037346690160133737354547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30691564460106755824903031 46037346690160133737354547)
  ·
    refine ⟨69056020035240200606031821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46037346690160133737354547 69056020035240200606031821)
    ·
      refine ⟨25896007513215075227261933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69056020035240200606031821 25896007513215075227261933)
      ·
        refine ⟨9711002817455653210223225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25896007513215075227261933 9711002817455653210223225)
        ·
          refine ⟨7283252113091739907667419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9711002817455653210223225 7283252113091739907667419)
          ·
            refine ⟨10924878169637609861501129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283252113091739907667419 10924878169637609861501129)
            ·
              refine ⟨8193658627228207396125847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10924878169637609861501129 8193658627228207396125847)
              ·
                refine ⟨12290487940842311094188771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8193658627228207396125847 12290487940842311094188771)
                ·
                  refine ⟨18435731911263466641283157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12290487940842311094188771 18435731911263466641283157)
                  ·
                    refine ⟨216043733335118749702537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18435731911263466641283157 216043733335118749702537)
                    ·
                      rfl

theorem cell23_1262231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_1262231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262231 prefixEnd_1262231 := by exact prefixLift 1262231
  have htrace : WordTrace (prefixWord ++ tailWord_1262231) baseStart_1262231 baseEnd_1262231 := by
    simpa [prefixWord, tailWord_1262231, baseEnd_1262231] using wordTrace_append hprefix tailTrace_1262231
  have hstable : (prefixWord ++ tailWord_1262231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262231).length < 2 ^ (prefixWord ++ tailWord_1262231).sum := by decide
  have hdescent : baseEnd_1262231 < baseStart_1262231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262255 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 4, 2]
def baseStart_1262255 : Nat := 118140960795 + 1262255 * 2 ^ 59
def prefixEnd_1262255 : Nat := 4983230072969 + 3 ^ 40 * 1262255 * 2
def baseEnd_1262255 : Nat := 648143523541064155207501

theorem tailTrace_1262255 : CollatzResearch.WordTrace tailWord_1262255 prefixEnd_1262255 648143523541064155207501 := by
  unfold tailWord_1262255
  simp only [CollatzResearch.WordTrace]
  refine ⟨46038222042073185836228219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30692148028048790557485479 46038222042073185836228219)
  ·
    refine ⟨69057333063109778754342329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46038222042073185836228219 69057333063109778754342329)
    ·
      refine ⟨51792999797332334065756747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69057333063109778754342329 51792999797332334065756747)
      ·
        refine ⟨77689499695998501098635121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51792999797332334065756747 77689499695998501098635121)
        ·
          refine ⟨58267124771998875823976341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77689499695998501098635121 58267124771998875823976341)
          ·
            refine ⟨2731271473687447304248891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58267124771998875823976341 2731271473687447304248891)
            ·
              refine ⟨4096907210531170956373337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731271473687447304248891 4096907210531170956373337)
              ·
                refine ⟨3072680407898378217280003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096907210531170956373337 3072680407898378217280003)
                ·
                  refine ⟨4609020611847567325920005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072680407898378217280003 4609020611847567325920005)
                  ·
                    refine ⟨864191364721418873610001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609020611847567325920005 864191364721418873610001)
                    ·
                      refine ⟨648143523541064155207501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864191364721418873610001 648143523541064155207501)
                      ·
                        rfl

theorem cell23_1262255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4, 2].length) (baseStart_1262255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262255 prefixEnd_1262255 := by exact prefixLift 1262255
  have htrace : WordTrace (prefixWord ++ tailWord_1262255) baseStart_1262255 baseEnd_1262255 := by
    simpa [prefixWord, tailWord_1262255, baseEnd_1262255] using wordTrace_append hprefix tailTrace_1262255
  have hstable : (prefixWord ++ tailWord_1262255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262255).length < 2 ^ (prefixWord ++ tailWord_1262255).sum := by decide
  have hdescent : baseEnd_1262255 < baseStart_1262255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262268 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1262268 : Nat := 118140960795 + 1262268 * 2 ^ 59
def prefixEnd_1262268 : Nat := 4983230072969 + 3 ^ 40 * 1262268 * 2
def baseEnd_1262268 : Nat := 648150198789572604344941

theorem tailTrace_1262268 : CollatzResearch.WordTrace tailWord_1262268 prefixEnd_1262268 648150198789572604344941 := by
  unfold tailWord_1262268
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019348095513044528225729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30692464127350726037634305 23019348095513044528225729)
  ·
    refine ⟨17264511071634783396169297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23019348095513044528225729 17264511071634783396169297)
    ·
      refine ⟨12948383303726087547126973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17264511071634783396169297 12948383303726087547126973)
      ·
        refine ⟨4855643738897282830172615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12948383303726087547126973 4855643738897282830172615)
        ·
          refine ⟨7283465608345924245258923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855643738897282830172615 7283465608345924245258923)
          ·
            refine ⟨10925198412518886367888385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283465608345924245258923 10925198412518886367888385)
            ·
              refine ⟨8193898809389164775916289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10925198412518886367888385 8193898809389164775916289)
              ·
                refine ⟨6145424107041873581937217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8193898809389164775916289 6145424107041873581937217)
                ·
                  refine ⟨4609068080281405186452913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145424107041873581937217 4609068080281405186452913)
                  ·
                    refine ⟨3456801060211053889839685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4609068080281405186452913 3456801060211053889839685)
                    ·
                      refine ⟨648150198789572604344941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3456801060211053889839685 648150198789572604344941)
                      ·
                        rfl

theorem cell23_1262268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1262268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262268 prefixEnd_1262268 := by exact prefixLift 1262268
  have htrace : WordTrace (prefixWord ++ tailWord_1262268) baseStart_1262268 baseEnd_1262268 := by
    simpa [prefixWord, tailWord_1262268, baseEnd_1262268] using wordTrace_append hprefix tailTrace_1262268
  have hstable : (prefixWord ++ tailWord_1262268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262268).length < 2 ^ (prefixWord ++ tailWord_1262268).sum := by decide
  have hdescent : baseEnd_1262268 < baseStart_1262268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262272 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2]
def baseStart_1262272 : Nat := 118140960795 + 1262272 * 2 ^ 59
def prefixEnd_1262272 : Nat := 4983230072969 + 3 ^ 40 * 1262272 * 2
def baseEnd_1262272 : Nat := 648152252712190588694923

theorem tailTrace_1262272 : CollatzResearch.WordTrace tailWord_1262272 prefixEnd_1262272 648152252712190588694923 := by
  unfold tailWord_1262272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019421041505798869798535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30692561388674398493064713 23019421041505798869798535)
  ·
    refine ⟨34529131562258698304697803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23019421041505798869798535 34529131562258698304697803)
    ·
      refine ⟨51793697343388047457046705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34529131562258698304697803 51793697343388047457046705)
      ·
        refine ⟨38845273007541035592785029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51793697343388047457046705 38845273007541035592785029)
        ·
          refine ⟨7283488688913944173647193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38845273007541035592785029 7283488688913944173647193)
          ·
            refine ⟨5462616516685458130235395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7283488688913944173647193 5462616516685458130235395)
            ·
              refine ⟨8193924775028187195353093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462616516685458130235395 8193924775028187195353093)
              ·
                refine ⟨1536360895317785099128705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8193924775028187195353093 1536360895317785099128705)
                ·
                  refine ⟨1152270671488338824346529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1536360895317785099128705 1152270671488338824346529)
                  ·
                    refine ⟨864203003616254118259897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1152270671488338824346529 864203003616254118259897)
                    ·
                      refine ⟨648152252712190588694923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864203003616254118259897 648152252712190588694923)
                      ·
                        rfl

theorem cell23_1262272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_1262272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262272 prefixEnd_1262272 := by exact prefixLift 1262272
  have htrace : WordTrace (prefixWord ++ tailWord_1262272) baseStart_1262272 baseEnd_1262272 := by
    simpa [prefixWord, tailWord_1262272, baseEnd_1262272] using wordTrace_append hprefix tailTrace_1262272
  have hstable : (prefixWord ++ tailWord_1262272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262272).length < 2 ^ (prefixWord ++ tailWord_1262272).sum := by decide
  have hdescent : baseEnd_1262272 < baseStart_1262272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262308 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1262308 : Nat := 118140960795 + 1262308 * 2 ^ 59
def prefixEnd_1262308 : Nat := 4983230072969 + 3 ^ 40 * 1262308 * 2
def baseEnd_1262308 : Nat := 216056912671917482614919

theorem tailTrace_1262308 : CollatzResearch.WordTrace tailWord_1262308 prefixEnd_1262308 216056912671917482614919 := by
  unfold tailWord_1262308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020077555440587943953789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30693436740587450591938385 23020077555440587943953789)
  ·
    refine ⟨8632529083290220478982671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23020077555440587943953789 8632529083290220478982671)
    ·
      refine ⟨12948793624935330718474007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8632529083290220478982671 12948793624935330718474007)
      ·
        refine ⟨19423190437402996077711011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12948793624935330718474007 19423190437402996077711011)
        ·
          refine ⟨29134785656104494116566517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19423190437402996077711011 29134785656104494116566517)
          ·
            refine ⟨2731386155259796323428111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29134785656104494116566517 2731386155259796323428111)
            ·
              refine ⟨4097079232889694485142167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731386155259796323428111 4097079232889694485142167)
              ·
                refine ⟨6145618849334541727713251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097079232889694485142167 6145618849334541727713251)
                ·
                  refine ⟨9218428274001812591569877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145618849334541727713251 9218428274001812591569877)
                  ·
                    refine ⟨216056912671917482614919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9218428274001812591569877 216056912671917482614919)
                    ·
                      rfl

theorem cell23_1262308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1262308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262308 prefixEnd_1262308 := by exact prefixLift 1262308
  have htrace : WordTrace (prefixWord ++ tailWord_1262308) baseStart_1262308 baseEnd_1262308 := by
    simpa [prefixWord, tailWord_1262308, baseEnd_1262308] using wordTrace_append hprefix tailTrace_1262308
  have hstable : (prefixWord ++ tailWord_1262308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262308).length < 2 ^ (prefixWord ++ tailWord_1262308).sum := by decide
  have hdescent : baseEnd_1262308 < baseStart_1262308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262312 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 5]
def baseStart_1262312 : Nat := 118140960795 + 1262312 * 2 ^ 59
def prefixEnd_1262312 : Nat := 4983230072969 + 3 ^ 40 * 1262312 * 2
def baseEnd_1262312 : Nat := 72019199104263381354971

theorem tailTrace_1262312 : CollatzResearch.WordTrace tailWord_1262312 prefixEnd_1262312 72019199104263381354971 := by
  unfold tailWord_1262312
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020150501433342285526595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30693534001911123047368793 23020150501433342285526595)
  ·
    refine ⟨34530225752150013428289893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23020150501433342285526595 34530225752150013428289893)
    ·
      refine ⟨6474417328528127517804355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34530225752150013428289893 6474417328528127517804355)
      ·
        refine ⟨9711625992792191276706533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6474417328528127517804355 9711625992792191276706533)
        ·
          refine ⟨1820929873648535864382475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9711625992792191276706533 1820929873648535864382475)
          ·
            refine ⟨2731394810472803796573713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820929873648535864382475 2731394810472803796573713)
            ·
              refine ⟨2048546107854602847430285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731394810472803796573713 2048546107854602847430285)
              ·
                refine ⟨768204790445476067786357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048546107854602847430285 768204790445476067786357)
                ·
                  refine ⟨72019199104263381354971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768204790445476067786357 72019199104263381354971)
                  ·
                    rfl

theorem cell23_1262312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 5].length) (baseStart_1262312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262312 prefixEnd_1262312 := by exact prefixLift 1262312
  have htrace : WordTrace (prefixWord ++ tailWord_1262312) baseStart_1262312 baseEnd_1262312 := by
    simpa [prefixWord, tailWord_1262312, baseEnd_1262312] using wordTrace_append hprefix tailTrace_1262312
  have hstable : (prefixWord ++ tailWord_1262312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262312).length < 2 ^ (prefixWord ++ tailWord_1262312).sum := by decide
  have hdescent : baseEnd_1262312 < baseStart_1262312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262328 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1262328 : Nat := 118140960795 + 1262328 * 2 ^ 59
def prefixEnd_1262328 : Nat := 4983230072969 + 3 ^ 40 * 1262328 * 2
def baseEnd_1262328 : Nat := 648181007628842369594665

theorem tailTrace_1262328 : CollatzResearch.WordTrace tailWord_1262328 prefixEnd_1262328 648181007628842369594665 := by
  unfold tailWord_1262328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23020442285404359651817819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30693923047205812869090425 23020442285404359651817819)
  ·
    refine ⟨34530663428106539477726729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23020442285404359651817819 34530663428106539477726729)
    ·
      refine ⟨25897997571079904608295047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34530663428106539477726729 25897997571079904608295047)
      ·
        refine ⟨38846996356619856912442571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25897997571079904608295047 38846996356619856912442571)
        ·
          refine ⟨58270494534929785368663857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38846996356619856912442571 58270494534929785368663857)
          ·
            refine ⟨43702870901197339026497893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58270494534929785368663857 43702870901197339026497893)
            ·
              refine ⟨8194288293974501067468355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43702870901197339026497893 8194288293974501067468355)
              ·
                refine ⟨12291432440961751601202533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194288293974501067468355 12291432440961751601202533)
                ·
                  refine ⟨2304643582680328425225475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12291432440961751601202533 2304643582680328425225475)
                  ·
                    refine ⟨3456965374020492637838213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304643582680328425225475 3456965374020492637838213)
                    ·
                      refine ⟨648181007628842369594665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3456965374020492637838213 648181007628842369594665)
                      ·
                        rfl

theorem cell23_1262328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1262328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262328 prefixEnd_1262328 := by exact prefixLift 1262328
  have htrace : WordTrace (prefixWord ++ tailWord_1262328) baseStart_1262328 baseEnd_1262328 := by
    simpa [prefixWord, tailWord_1262328, baseEnd_1262328] using wordTrace_append hprefix tailTrace_1262328
  have hstable : (prefixWord ++ tailWord_1262328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262328).length < 2 ^ (prefixWord ++ tailWord_1262328).sum := by decide
  have hdescent : baseEnd_1262328 < baseStart_1262328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262345 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 4, 2]
def baseStart_1262345 : Nat := 118140960795 + 1262345 * 2 ^ 59
def prefixEnd_1262345 : Nat := 4983230072969 + 3 ^ 40 * 1262345 * 2
def baseEnd_1262345 : Nat := 648189736799968803082087

theorem tailTrace_1262345 : CollatzResearch.WordTrace tailWord_1262345 prefixEnd_1262345 648189736799968803082087 := by
  unfold tailWord_1262345
  simp only [CollatzResearch.WordTrace]
  refine ⟨46041504611747131207004489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30694336407831420804669659 46041504611747131207004489)
  ·
    refine ⟨34531128458810348405253367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46041504611747131207004489 34531128458810348405253367)
    ·
      refine ⟨51796692688215522607880051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34531128458810348405253367 51796692688215522607880051)
      ·
        refine ⟨77695039032323283911820077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51796692688215522607880051 77695039032323283911820077)
        ·
          refine ⟨29135639637121231466932529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77695039032323283911820077 29135639637121231466932529)
          ·
            refine ⟨21851729727840923600199397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29135639637121231466932529 21851729727840923600199397)
            ·
              refine ⟨4097199323970173175037387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21851729727840923600199397 4097199323970173175037387)
              ·
                refine ⟨6145798985955259762556081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097199323970173175037387 6145798985955259762556081)
                ·
                  refine ⟨4609349239466444821917061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145798985955259762556081 4609349239466444821917061)
                  ·
                    refine ⟨864252982399958404109449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4609349239466444821917061 864252982399958404109449)
                    ·
                      refine ⟨648189736799968803082087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864252982399958404109449 648189736799968803082087)
                      ·
                        rfl

theorem cell23_1262345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4, 2].length) (baseStart_1262345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262345 prefixEnd_1262345 := by exact prefixLift 1262345
  have htrace : WordTrace (prefixWord ++ tailWord_1262345) baseStart_1262345 baseEnd_1262345 := by
    simpa [prefixWord, tailWord_1262345, baseEnd_1262345] using wordTrace_append hprefix tailTrace_1262345
  have hstable : (prefixWord ++ tailWord_1262345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262345).length < 2 ^ (prefixWord ++ tailWord_1262345).sum := by decide
  have hdescent : baseEnd_1262345 < baseStart_1262345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262368 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 8]
def baseStart_1262368 : Nat := 118140960795 + 1262368 * 2 ^ 59
def prefixEnd_1262368 : Nat := 4983230072969 + 3 ^ 40 * 1262368 * 2
def baseEnd_1262368 : Nat := 72022394095002468121609

theorem tailTrace_1262368 : CollatzResearch.WordTrace tailWord_1262368 prefixEnd_1262368 72022394095002468121609 := by
  unfold tailWord_1262368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23021171745331903067545879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30694895660442537423394505 23021171745331903067545879)
  ·
    refine ⟨34531757617997854601318819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23021171745331903067545879 34531757617997854601318819)
    ·
      refine ⟨51797636426996781901978229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34531757617997854601318819 51797636426996781901978229)
      ·
        refine ⟨4856028415030948303310459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51797636426996781901978229 4856028415030948303310459)
        ·
          refine ⟨7284042622546422454965689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856028415030948303310459 7284042622546422454965689)
          ·
            refine ⟨5463031966909816841224267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7284042622546422454965689 5463031966909816841224267)
            ·
              refine ⟨8194547950364725261836401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463031966909816841224267 8194547950364725261836401)
              ·
                refine ⟨6145910962773543946377301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8194547950364725261836401 6145910962773543946377301)
                ·
                  refine ⟨72022394095002468121609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6145910962773543946377301 72022394095002468121609)
                  ·
                    rfl

theorem cell23_1262368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_1262368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262368 prefixEnd_1262368 := by exact prefixLift 1262368
  have htrace : WordTrace (prefixWord ++ tailWord_1262368) baseStart_1262368 baseEnd_1262368 := by
    simpa [prefixWord, tailWord_1262368, baseEnd_1262368] using wordTrace_append hprefix tailTrace_1262368
  have hstable : (prefixWord ++ tailWord_1262368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262368).length < 2 ^ (prefixWord ++ tailWord_1262368).sum := by decide
  have hdescent : baseEnd_1262368 < baseStart_1262368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262382 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1262382 : Nat := 118140960795 + 1262382 * 2 ^ 59
def prefixEnd_1262382 : Nat := 4983230072969 + 3 ^ 40 * 1262382 * 2
def baseEnd_1262382 : Nat := 648208735584185158319417

theorem tailTrace_1262382 : CollatzResearch.WordTrace tailWord_1262382 prefixEnd_1262382 648208735584185158319417 := by
  unfold tailWord_1262382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755356764076635815762675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30695236075075391017400933 5755356764076635815762675)
  ·
    refine ⟨8633035146114953723644013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755356764076635815762675 8633035146114953723644013)
    ·
      refine ⟨3237388179793107646366505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8633035146114953723644013 3237388179793107646366505)
      ·
        refine ⟨2428041134844830734774879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3237388179793107646366505 2428041134844830734774879)
        ·
          refine ⟨3642061702267246102162319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428041134844830734774879 3642061702267246102162319)
          ·
            refine ⟨5463092553400869153243479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642061702267246102162319 5463092553400869153243479)
            ·
              refine ⟨8194638830101303729865219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463092553400869153243479 8194638830101303729865219)
              ·
                refine ⟨12291958245151955594797829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194638830101303729865219 12291958245151955594797829)
                ·
                  refine ⟨2304742170965991674024593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12291958245151955594797829 2304742170965991674024593)
                  ·
                    refine ⟨1728556628224493755518445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2304742170965991674024593 1728556628224493755518445)
                    ·
                      refine ⟨648208735584185158319417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1728556628224493755518445 648208735584185158319417)
                      ·
                        rfl

theorem cell23_1262382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1262382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262382 prefixEnd_1262382 := by exact prefixLift 1262382
  have htrace : WordTrace (prefixWord ++ tailWord_1262382) baseStart_1262382 baseEnd_1262382 := by
    simpa [prefixWord, tailWord_1262382, baseEnd_1262382] using wordTrace_append hprefix tailTrace_1262382
  have hstable : (prefixWord ++ tailWord_1262382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262382).length < 2 ^ (prefixWord ++ tailWord_1262382).sum := by decide
  have hdescent : baseEnd_1262382 < baseStart_1262382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262405 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_1262405 : Nat := 118140960795 + 1262405 * 2 ^ 59
def prefixEnd_1262405 : Nat := 4983230072969 + 3 ^ 40 * 1262405 * 2
def baseEnd_1262405 : Nat := 648220545639238568331811

theorem tailTrace_1262405 : CollatzResearch.WordTrace tailWord_1262405 prefixEnd_1262405 648220545639238568331811 := by
  unfold tailWord_1262405
  simp only [CollatzResearch.WordTrace]
  refine ⟨46043692991529761454188669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30695795327686507636125779 46043692991529761454188669)
  ·
    refine ⟨17266384871823660545320751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46043692991529761454188669 17266384871823660545320751)
    ·
      refine ⟨25899577307735490817981127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17266384871823660545320751 25899577307735490817981127)
      ·
        refine ⟨38849365961603236226971691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25899577307735490817981127 38849365961603236226971691)
        ·
          refine ⟨58274048942404854340457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38849365961603236226971691 58274048942404854340457537)
          ·
            refine ⟨43705536706803640755343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58274048942404854340457537 43705536706803640755343153)
            ·
              refine ⟨32779152530102730566507365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43705536706803640755343153 32779152530102730566507365)
              ·
                refine ⟨6146091099394261981220131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32779152530102730566507365 6146091099394261981220131)
                ·
                  refine ⟨9219136649091392971830197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6146091099394261981220131 9219136649091392971830197)
                  ·
                    refine ⟨864294060852318091109081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9219136649091392971830197 864294060852318091109081)
                    ·
                      refine ⟨648220545639238568331811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864294060852318091109081 648220545639238568331811)
                      ·
                        rfl

theorem cell23_1262405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_1262405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262405 prefixEnd_1262405 := by exact prefixLift 1262405
  have htrace : WordTrace (prefixWord ++ tailWord_1262405) baseStart_1262405 baseEnd_1262405 := by
    simpa [prefixWord, tailWord_1262405, baseEnd_1262405] using wordTrace_append hprefix tailTrace_1262405
  have hstable : (prefixWord ++ tailWord_1262405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262405).length < 2 ^ (prefixWord ++ tailWord_1262405).sum := by decide
  have hdescent : baseEnd_1262405 < baseStart_1262405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262432 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_1262432 : Nat := 118140960795 + 1262432 * 2 ^ 59
def prefixEnd_1262432 : Nat := 4983230072969 + 3 ^ 40 * 1262432 * 2
def baseEnd_1262432 : Nat := 216078136538969987564729

theorem tailTrace_1262432 : CollatzResearch.WordTrace tailWord_1262432 prefixEnd_1262432 216078136538969987564729 := by
  unfold tailWord_1262432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022338881215972532710775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30696451841621296710281033 23022338881215972532710775)
  ·
    refine ⟨34533508321823958799066163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23022338881215972532710775 34533508321823958799066163)
    ·
      refine ⟨51800262482735938198599245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34533508321823958799066163 51800262482735938198599245)
      ·
        refine ⟨19425098431025976824474717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51800262482735938198599245 19425098431025976824474717)
        ·
          refine ⟨7284411911634741309178019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19425098431025976824474717 7284411911634741309178019)
          ·
            refine ⟨10926617867452111963767029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284411911634741309178019 10926617867452111963767029)
            ·
              refine ⟨1024370425073635496603159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10926617867452111963767029 1024370425073635496603159)
              ·
                refine ⟨1536555637610453244904739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1024370425073635496603159 1536555637610453244904739)
                ·
                  refine ⟨2304833456415679867357109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536555637610453244904739 2304833456415679867357109)
                  ·
                    refine ⟨216078136538969987564729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2304833456415679867357109 216078136538969987564729)
                    ·
                      rfl

theorem cell23_1262432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_1262432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262432 prefixEnd_1262432 := by exact prefixLift 1262432
  have htrace : WordTrace (prefixWord ++ tailWord_1262432) baseStart_1262432 baseEnd_1262432 := by
    simpa [prefixWord, tailWord_1262432, baseEnd_1262432] using wordTrace_append hprefix tailTrace_1262432
  have hstable : (prefixWord ++ tailWord_1262432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262432).length < 2 ^ (prefixWord ++ tailWord_1262432).sum := by decide
  have hdescent : baseEnd_1262432 < baseStart_1262432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262448 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_1262448 : Nat := 118140960795 + 1262448 * 2 ^ 59
def prefixEnd_1262448 : Nat := 4983230072969 + 3 ^ 40 * 1262448 * 2
def baseEnd_1262448 : Nat := 648242625307381900094113

theorem tailTrace_1262448 : CollatzResearch.WordTrace tailWord_1262448 prefixEnd_1262448 648242625307381900094113 := by
  unfold tailWord_1262448
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022630665186989899001999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30696840886915986532002665 23022630665186989899001999)
  ·
    refine ⟨34533945997780484848502999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23022630665186989899001999 34533945997780484848502999)
    ·
      refine ⟨51800918996670727272754499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34533945997780484848502999 51800918996670727272754499)
      ·
        refine ⟨77701378495006090909131749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51800918996670727272754499 77701378495006090909131749)
        ·
          refine ⟨14569008467813642045462203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77701378495006090909131749 14569008467813642045462203)
          ·
            refine ⟨21853512701720463068193305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14569008467813642045462203 21853512701720463068193305)
            ·
              refine ⟨16390134526290347301144979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21853512701720463068193305 16390134526290347301144979)
              ·
                refine ⟨24585201789435520951717469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16390134526290347301144979 24585201789435520951717469)
                ·
                  refine ⟨9219450671038320356894051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24585201789435520951717469 9219450671038320356894051)
                  ·
                    refine ⟨13829176006557480535341077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9219450671038320356894051 13829176006557480535341077)
                    ·
                      refine ⟨648242625307381900094113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13829176006557480535341077 648242625307381900094113)
                      ·
                        rfl

theorem cell23_1262448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_1262448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262448 prefixEnd_1262448 := by exact prefixLift 1262448
  have htrace : WordTrace (prefixWord ++ tailWord_1262448) baseStart_1262448 baseEnd_1262448 := by
    simpa [prefixWord, tailWord_1262448, baseEnd_1262448] using wordTrace_append hprefix tailTrace_1262448
  have hstable : (prefixWord ++ tailWord_1262448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262448).length < 2 ^ (prefixWord ++ tailWord_1262448).sum := by decide
  have hdescent : baseEnd_1262448 < baseStart_1262448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262469 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_1262469 : Nat := 118140960795 + 1262469 * 2 ^ 59
def prefixEnd_1262469 : Nat := 4983230072969 + 3 ^ 40 * 1262469 * 2
def baseEnd_1262469 : Nat := 648253408401126317931517

theorem tailTrace_1262469 : CollatzResearch.WordTrace tailWord_1262469 prefixEnd_1262469 648253408401126317931517 := by
  unfold tailWord_1262469
  simp only [CollatzResearch.WordTrace]
  refine ⟨46046027263297900384518461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30697351508865266923012307 46046027263297900384518461)
  ·
    refine ⟨17267260223736712644194423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46046027263297900384518461 17267260223736712644194423)
    ·
      refine ⟨25900890335605068966291635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17267260223736712644194423 25900890335605068966291635)
      ·
        refine ⟨38851335503407603449437453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25900890335605068966291635 38851335503407603449437453)
        ·
          refine ⟨14569250813777851293539045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38851335503407603449437453 14569250813777851293539045)
          ·
            refine ⟨2731734527583347117538571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14569250813777851293539045 2731734527583347117538571)
            ·
              refine ⟨4097601791375020676307857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731734527583347117538571 4097601791375020676307857)
              ·
                refine ⟨3073201343531265507230893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097601791375020676307857 3073201343531265507230893)
                ·
                  refine ⟨1152450503824224565211585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3073201343531265507230893 1152450503824224565211585)
                  ·
                    refine ⟨864337877868168423908689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1152450503824224565211585 864337877868168423908689)
                    ·
                      refine ⟨648253408401126317931517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864337877868168423908689 648253408401126317931517)
                      ·
                        rfl

theorem cell23_1262469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_1262469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262469 prefixEnd_1262469 := by exact prefixLift 1262469
  have htrace : WordTrace (prefixWord ++ tailWord_1262469) baseStart_1262469 baseEnd_1262469 := by
    simpa [prefixWord, tailWord_1262469, baseEnd_1262469] using wordTrace_append hprefix tailTrace_1262469
  have hstable : (prefixWord ++ tailWord_1262469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262469).length < 2 ^ (prefixWord ++ tailWord_1262469).sum := by decide
  have hdescent : baseEnd_1262469 < baseStart_1262469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262472 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1262472 : Nat := 118140960795 + 1262472 * 2 ^ 59
def prefixEnd_1262472 : Nat := 4983230072969 + 3 ^ 40 * 1262472 * 2
def baseEnd_1262472 : Nat := 648254948843089806194003

theorem tailTrace_1262472 : CollatzResearch.WordTrace tailWord_1262472 prefixEnd_1262472 648254948843089806194003 := by
  unfold tailWord_1262472
  simp only [CollatzResearch.WordTrace]
  refine ⟨23023068341143515948438835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30697424454858021264585113 23023068341143515948438835)
  ·
    refine ⟨34534602511715273922658253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23023068341143515948438835 34534602511715273922658253)
    ·
      refine ⟨12950475941893227720996845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34534602511715273922658253 12950475941893227720996845)
      ·
        refine ⟨4856428478209960395373817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12950475941893227720996845 4856428478209960395373817)
        ·
          refine ⟨3642321358657470296530363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856428478209960395373817 3642321358657470296530363)
          ·
            refine ⟨5463482037986205444795545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642321358657470296530363 5463482037986205444795545)
            ·
              refine ⟨4097611528489654083596659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463482037986205444795545 4097611528489654083596659)
              ·
                refine ⟨6146417292734481125394989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097611528489654083596659 6146417292734481125394989)
                ·
                  refine ⟨2304906484775430422023121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6146417292734481125394989 2304906484775430422023121)
                  ·
                    refine ⟨1728679863581572816517341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2304906484775430422023121 1728679863581572816517341)
                    ·
                      refine ⟨648254948843089806194003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1728679863581572816517341 648254948843089806194003)
                      ·
                        rfl

theorem cell23_1262472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1262472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262472 prefixEnd_1262472 := by exact prefixLift 1262472
  have htrace : WordTrace (prefixWord ++ tailWord_1262472) baseStart_1262472 baseEnd_1262472 := by
    simpa [prefixWord, tailWord_1262472, baseEnd_1262472] using wordTrace_append hprefix tailTrace_1262472
  have hstable : (prefixWord ++ tailWord_1262472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262472).length < 2 ^ (prefixWord ++ tailWord_1262472).sum := by decide
  have hdescent : baseEnd_1262472 < baseStart_1262472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262516 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1262516 : Nat := 118140960795 + 1262516 * 2 ^ 59
def prefixEnd_1262516 : Nat := 4983230072969 + 3 ^ 40 * 1262516 * 2
def baseEnd_1262516 : Nat := 648277541991887634043801

theorem tailTrace_1262516 : CollatzResearch.WordTrace tailWord_1262516 prefixEnd_1262516 648277541991887634043801 := by
  unfold tailWord_1262516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23023870747063813705739701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30698494329418418274319601 23023870747063813705739701)
  ·
    refine ⟨2158487882537232534913097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23023870747063813705739701 2158487882537232534913097)
    ·
      refine ⟨1618865911902924401184823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158487882537232534913097 1618865911902924401184823)
      ·
        refine ⟨2428298867854386601777235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618865911902924401184823 2428298867854386601777235)
        ·
          refine ⟨3642448301781579902665853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428298867854386601777235 3642448301781579902665853)
          ·
            refine ⟨1365918113168092463499695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3642448301781579902665853 1365918113168092463499695)
            ·
              refine ⟨2048877169752138695249543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365918113168092463499695 2048877169752138695249543)
              ·
                refine ⟨3073315754628208042874315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048877169752138695249543 3073315754628208042874315)
                ·
                  refine ⟨4609973631942312064311473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073315754628208042874315 4609973631942312064311473)
                  ·
                    refine ⟨3457480223956734048233605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4609973631942312064311473 3457480223956734048233605)
                    ·
                      refine ⟨648277541991887634043801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3457480223956734048233605 648277541991887634043801)
                      ·
                        rfl

theorem cell23_1262516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1262516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262516 prefixEnd_1262516 := by exact prefixLift 1262516
  have htrace : WordTrace (prefixWord ++ tailWord_1262516) baseStart_1262516 baseEnd_1262516 := by
    simpa [prefixWord, tailWord_1262516, baseEnd_1262516] using wordTrace_append hprefix tailTrace_1262516
  have hstable : (prefixWord ++ tailWord_1262516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262516).length < 2 ^ (prefixWord ++ tailWord_1262516).sum := by decide
  have hdescent : baseEnd_1262516 < baseStart_1262516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262545 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_1262545 : Nat := 118140960795 + 1262545 * 2 ^ 59
def prefixEnd_1262545 : Nat := 4983230072969 + 3 ^ 40 * 1262545 * 2
def baseEnd_1262545 : Nat := 648292432930868020581167

theorem tailTrace_1262545 : CollatzResearch.WordTrace tailWord_1262545 prefixEnd_1262545 648292432930868020581167 := by
  unfold tailWord_1262545
  simp only [CollatzResearch.WordTrace]
  refine ⟨46048799211022565364285089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30699199474015043576190059 46048799211022565364285089)
  ·
    refine ⟨34536599408266924023213817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46048799211022565364285089 34536599408266924023213817)
    ·
      refine ⟨25902449556200193017410363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34536599408266924023213817 25902449556200193017410363)
      ·
        refine ⟨38853674334300289526115545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25902449556200193017410363 38853674334300289526115545)
        ·
          refine ⟨29140255750725217144586659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38853674334300289526115545 29140255750725217144586659)
          ·
            refine ⟨43710383626087825716879989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29140255750725217144586659 43710383626087825716879989)
            ·
              refine ⟨4097848464945733660957499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43710383626087825716879989 4097848464945733660957499)
              ·
                refine ⟨6146772697418600491436249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097848464945733660957499 6146772697418600491436249)
                ·
                  refine ⟨4610079523063950368577187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6146772697418600491436249 4610079523063950368577187)
                  ·
                    refine ⟨6915119284595925552865781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4610079523063950368577187 6915119284595925552865781)
                    ·
                      refine ⟨648292432930868020581167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6915119284595925552865781 648292432930868020581167)
                      ·
                        rfl

theorem cell23_1262545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_1262545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262545 prefixEnd_1262545 := by exact prefixLift 1262545
  have htrace : WordTrace (prefixWord ++ tailWord_1262545) baseStart_1262545 baseEnd_1262545 := by
    simpa [prefixWord, tailWord_1262545, baseEnd_1262545] using wordTrace_append hprefix tailTrace_1262545
  have hstable : (prefixWord ++ tailWord_1262545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262545).length < 2 ^ (prefixWord ++ tailWord_1262545).sum := by decide
  have hdescent : baseEnd_1262545 < baseStart_1262545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262546 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1262546 : Nat := 118140960795 + 1262546 * 2 ^ 59
def prefixEnd_1262546 : Nat := 4983230072969 + 3 ^ 40 * 1262546 * 2
def baseEnd_1262546 : Nat := 648292946411522516668663

theorem tailTrace_1262546 : CollatzResearch.WordTrace tailWord_1262546 prefixEnd_1262546 648292946411522516668663 := by
  unfold tailWord_1262546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512208921004735633767873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30699223789345961690047661 11512208921004735633767873)
  ·
    refine ⟨8634156690753551725325905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11512208921004735633767873 8634156690753551725325905)
    ·
      refine ⟨6475617518065163793994429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8634156690753551725325905 6475617518065163793994429)
      ·
        refine ⟨2428356569274436422747911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6475617518065163793994429 2428356569274436422747911)
        ·
          refine ⟨3642534853911654634121867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428356569274436422747911 3642534853911654634121867)
          ·
            refine ⟨5463802280867481951182801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642534853911654634121867 5463802280867481951182801)
            ·
              refine ⟨4097851710650611463387101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463802280867481951182801 4097851710650611463387101)
              ·
                refine ⟨1536694391493979298770163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4097851710650611463387101 1536694391493979298770163)
                ·
                  refine ⟨2305041587240968948155245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536694391493979298770163 2305041587240968948155245)
                  ·
                    refine ⟨864390595215363355558217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305041587240968948155245 864390595215363355558217)
                    ·
                      refine ⟨648292946411522516668663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864390595215363355558217 648292946411522516668663)
                      ·
                        rfl

theorem cell23_1262546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1262546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262546 prefixEnd_1262546 := by exact prefixLift 1262546
  have htrace : WordTrace (prefixWord ++ tailWord_1262546) baseStart_1262546 baseEnd_1262546 := by
    simpa [prefixWord, tailWord_1262546, baseEnd_1262546] using wordTrace_append hprefix tailTrace_1262546
  have hstable : (prefixWord ++ tailWord_1262546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262546).length < 2 ^ (prefixWord ++ tailWord_1262546).sum := by decide
  have hdescent : baseEnd_1262546 < baseStart_1262546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262616 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 5]
def baseStart_1262616 : Nat := 118140960795 + 1262616 * 2 ^ 59
def prefixEnd_1262616 : Nat := 4983230072969 + 3 ^ 40 * 1262616 * 2
def baseEnd_1262616 : Nat := 72036543339704138088149

theorem tailTrace_1262616 : CollatzResearch.WordTrace tailWord_1262616 prefixEnd_1262616 72036543339704138088149 := by
  unfold tailWord_1262616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23025694396882672245059851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30700925862510229660079801 23025694396882672245059851)
  ·
    refine ⟨34538541595324008367589777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23025694396882672245059851 34538541595324008367589777)
    ·
      refine ⟨25903906196493006275692333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34538541595324008367589777 25903906196493006275692333)
      ·
        refine ⟨9713964823684877353384625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25903906196493006275692333 9713964823684877353384625)
        ·
          refine ⟨7285473617763658015038469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713964823684877353384625 7285473617763658015038469)
          ·
            refine ⟨1366026303330685877819713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7285473617763658015038469 1366026303330685877819713)
            ·
              refine ⟨1024519727498014408364785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366026303330685877819713 1024519727498014408364785)
              ·
                refine ⟨768389795623510806273589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024519727498014408364785 768389795623510806273589)
                ·
                  refine ⟨72036543339704138088149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768389795623510806273589 72036543339704138088149)
                  ·
                    rfl

theorem cell23_1262616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 5].length) (baseStart_1262616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262616 prefixEnd_1262616 := by exact prefixLift 1262616
  have htrace : WordTrace (prefixWord ++ tailWord_1262616) baseStart_1262616 baseEnd_1262616 := by
    simpa [prefixWord, tailWord_1262616, baseEnd_1262616] using wordTrace_append hprefix tailTrace_1262616
  have hstable : (prefixWord ++ tailWord_1262616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262616).length < 2 ^ (prefixWord ++ tailWord_1262616).sum := by decide
  have hdescent : baseEnd_1262616 < baseStart_1262616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262646 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1262646 : Nat := 118140960795 + 1262646 * 2 ^ 59
def prefixEnd_1262646 : Nat := 4983230072969 + 3 ^ 40 * 1262646 * 2
def baseEnd_1262646 : Nat := 216114764825657375139401

theorem tailTrace_1262646 : CollatzResearch.WordTrace tailWord_1262646 prefixEnd_1262646 216114764825657375139401 := by
  unfold tailWord_1262646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878280186478541225856987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30701655322437773075807861 2878280186478541225856987)
  ·
    refine ⟨4317420279717811838785481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878280186478541225856987 4317420279717811838785481)
    ·
      refine ⟨3238065209788358879089111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4317420279717811838785481 3238065209788358879089111)
      ·
        refine ⟨4857097814682538318633667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238065209788358879089111 4857097814682538318633667)
        ·
          refine ⟨7285646722023807477950501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857097814682538318633667 7285646722023807477950501)
          ·
            refine ⟨1366058760379463902115719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7285646722023807477950501 1366058760379463902115719)
            ·
              refine ⟨2049088140569195853173579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366058760379463902115719 2049088140569195853173579)
              ·
                refine ⟨3073632210853793779760369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049088140569195853173579 3073632210853793779760369)
                ·
                  refine ⟨2305224158140345334820277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073632210853793779760369 2305224158140345334820277)
                  ·
                    refine ⟨216114764825657375139401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2305224158140345334820277 216114764825657375139401)
                    ·
                      rfl

theorem cell23_1262646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1262646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262646 prefixEnd_1262646 := by exact prefixLift 1262646
  have htrace : WordTrace (prefixWord ++ tailWord_1262646) baseStart_1262646 baseEnd_1262646 := by
    simpa [prefixWord, tailWord_1262646, baseEnd_1262646] using wordTrace_append hprefix tailTrace_1262646
  have hstable : (prefixWord ++ tailWord_1262646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262646).length < 2 ^ (prefixWord ++ tailWord_1262646).sum := by decide
  have hdescent : baseEnd_1262646 < baseStart_1262646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262649 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1262649 : Nat := 118140960795 + 1262649 * 2 ^ 59
def prefixEnd_1262649 : Nat := 4983230072969 + 3 ^ 40 * 1262649 * 2
def baseEnd_1262649 : Nat := 648345834918935613680689

theorem tailTrace_1262649 : CollatzResearch.WordTrace tailWord_1262649 prefixEnd_1262649 648345834918935613680689 := by
  unfold tailWord_1262649
  simp only [CollatzResearch.WordTrace]
  refine ⟨46052592402645791126071001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30701728268430527417380667 46052592402645791126071001)
  ·
    refine ⟨34539444301984343344553251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46052592402645791126071001 34539444301984343344553251)
    ·
      refine ⟨51809166452976515016829877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34539444301984343344553251 51809166452976515016829877)
      ·
        refine ⟨4857109354966548282827801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51809166452976515016829877 4857109354966548282827801)
        ·
          refine ⟨3642832016224911212120851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857109354966548282827801 3642832016224911212120851)
          ·
            refine ⟨5464248024337366818181277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642832016224911212120851 5464248024337366818181277)
            ·
              refine ⟨2049093009126512556817979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5464248024337366818181277 2049093009126512556817979)
              ·
                refine ⟨3073639513689768835226969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049093009126512556817979 3073639513689768835226969)
                ·
                  refine ⟨2305229635267326626420227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073639513689768835226969 2305229635267326626420227)
                  ·
                    refine ⟨3457844452900989939630341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305229635267326626420227 3457844452900989939630341)
                    ·
                      refine ⟨648345834918935613680689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3457844452900989939630341 648345834918935613680689)
                      ·
                        rfl

theorem cell23_1262649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1262649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262649 prefixEnd_1262649 := by exact prefixLift 1262649
  have htrace : WordTrace (prefixWord ++ tailWord_1262649) baseStart_1262649 baseEnd_1262649 := by
    simpa [prefixWord, tailWord_1262649, baseEnd_1262649] using wordTrace_append hprefix tailTrace_1262649
  have hstable : (prefixWord ++ tailWord_1262649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262649).length < 2 ^ (prefixWord ++ tailWord_1262649).sum := by decide
  have hdescent : baseEnd_1262649 < baseStart_1262649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262655 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 8]
def baseStart_1262655 : Nat := 118140960795 + 1262655 * 2 ^ 59
def prefixEnd_1262655 : Nat := 4983230072969 + 3 ^ 40 * 1262655 * 2
def baseEnd_1262655 : Nat := 72038768422540287800629

theorem tailTrace_1262655 : CollatzResearch.WordTrace tailWord_1262655 prefixEnd_1262655 72038768422540287800629 := by
  unfold tailWord_1262655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46052811240624054150789419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30701874160416036100526279 46052811240624054150789419)
  ·
    refine ⟨69079216860936081226184129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46052811240624054150789419 69079216860936081226184129)
    ·
      refine ⟨51809412645702060919638097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69079216860936081226184129 51809412645702060919638097)
      ·
        refine ⟨38857059484276545689728573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51809412645702060919638097 38857059484276545689728573)
        ·
          refine ⟨14571397306603704633648215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38857059484276545689728573 14571397306603704633648215)
          ·
            refine ⟨21857095959905556950472323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571397306603704633648215 21857095959905556950472323)
            ·
              refine ⟨32785643939858335425708485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21857095959905556950472323 32785643939858335425708485)
              ·
                refine ⟨6147308238723437892320341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32785643939858335425708485 6147308238723437892320341)
                ·
                  refine ⟨72038768422540287800629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6147308238723437892320341 72038768422540287800629)
                  ·
                    rfl

theorem cell23_1262655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 8].length) (baseStart_1262655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262655 prefixEnd_1262655 := by exact prefixLift 1262655
  have htrace : WordTrace (prefixWord ++ tailWord_1262655) baseStart_1262655 baseEnd_1262655 := by
    simpa [prefixWord, tailWord_1262655, baseEnd_1262655] using wordTrace_append hprefix tailTrace_1262655
  have hstable : (prefixWord ++ tailWord_1262655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262655).length < 2 ^ (prefixWord ++ tailWord_1262655).sum := by decide
  have hdescent : baseEnd_1262655 < baseStart_1262655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_1262675 : Nat := 118140960795 + 1262675 * 2 ^ 59
def prefixEnd_1262675 : Nat := 4983230072969 + 3 ^ 40 * 1262675 * 2
def baseEnd_1262675 : Nat := 648359185415952511955569

theorem tailTrace_1262675 : CollatzResearch.WordTrace tailWord_1262675 prefixEnd_1262675 648359185415952511955569 := by
  unfold tailWord_1262675
  simp only [CollatzResearch.WordTrace]
  refine ⟨46053540700551597566517479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30702360467034398377678319 46053540700551597566517479)
  ·
    refine ⟨69080311050827396349776219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46053540700551597566517479 69080311050827396349776219)
    ·
      refine ⟨103620466576241094524664329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69080311050827396349776219 103620466576241094524664329)
      ·
        refine ⟨77715349932180820893498247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103620466576241094524664329 77715349932180820893498247)
        ·
          refine ⟨116573024898271231340247371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77715349932180820893498247 116573024898271231340247371)
          ·
            refine ⟨174859537347406847010371057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116573024898271231340247371 174859537347406847010371057)
            ·
              refine ⟨131144653010555135257778293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174859537347406847010371057 131144653010555135257778293)
              ·
                refine ⟨12294811219739543930416715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131144653010555135257778293 12294811219739543930416715)
                ·
                  refine ⟨18442216829609315895625073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294811219739543930416715 18442216829609315895625073)
                  ·
                    refine ⟨13831662622206986921718805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18442216829609315895625073 13831662622206986921718805)
                    ·
                      refine ⟨648359185415952511955569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13831662622206986921718805 648359185415952511955569)
                      ·
                        rfl

theorem cell23_1262675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_1262675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262675 prefixEnd_1262675 := by exact prefixLift 1262675
  have htrace : WordTrace (prefixWord ++ tailWord_1262675) baseStart_1262675 baseEnd_1262675 := by
    simpa [prefixWord, tailWord_1262675, baseEnd_1262675] using wordTrace_append hprefix tailTrace_1262675
  have hstable : (prefixWord ++ tailWord_1262675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262675).length < 2 ^ (prefixWord ++ tailWord_1262675).sum := by decide
  have hdescent : baseEnd_1262675 < baseStart_1262675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262676 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1262676 : Nat := 118140960795 + 1262676 * 2 ^ 59
def prefixEnd_1262676 : Nat := 4983230072969 + 3 ^ 40 * 1262676 * 2
def baseEnd_1262676 : Nat := 216119899632202336014355

theorem tailTrace_1262676 : CollatzResearch.WordTrace tailWord_1262676 prefixEnd_1262676 216119899632202336014355 := by
  unfold tailWord_1262676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23026788586773987368651941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30702384782365316491535921 23026788586773987368651941)
  ·
    refine ⟨4317522860020122631622239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23026788586773987368651941 4317522860020122631622239)
    ·
      refine ⟨6476284290030183947433359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317522860020122631622239 6476284290030183947433359)
      ·
        refine ⟨9714426435045275921150039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476284290030183947433359 9714426435045275921150039)
        ·
          refine ⟨14571639652567913881725059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714426435045275921150039 14571639652567913881725059)
          ·
            refine ⟨21857459478851870822587589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571639652567913881725059 21857459478851870822587589)
            ·
              refine ⟨4098273652284725779235173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21857459478851870822587589 4098273652284725779235173)
              ·
                refine ⟨768426309803386083606595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4098273652284725779235173 768426309803386083606595)
                ·
                  refine ⟨1152639464705079125409893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768426309803386083606595 1152639464705079125409893)
                  ·
                    refine ⟨216119899632202336014355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1152639464705079125409893 216119899632202336014355)
                    ·
                      rfl

theorem cell23_1262676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1262676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262676 prefixEnd_1262676 := by exact prefixLift 1262676
  have htrace : WordTrace (prefixWord ++ tailWord_1262676) baseStart_1262676 baseEnd_1262676 := by
    simpa [prefixWord, tailWord_1262676, baseEnd_1262676] using wordTrace_append hprefix tailTrace_1262676
  have hstable : (prefixWord ++ tailWord_1262676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262676).length < 2 ^ (prefixWord ++ tailWord_1262676).sum := by decide
  have hdescent : baseEnd_1262676 < baseStart_1262676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262752 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1262752 : Nat := 118140960795 + 1262752 * 2 ^ 59
def prefixEnd_1262752 : Nat := 4983230072969 + 3 ^ 40 * 1262752 * 2
def baseEnd_1262752 : Nat := 648398723426348710692715

theorem tailTrace_1262752 : CollatzResearch.WordTrace tailWord_1262752 prefixEnd_1262752 648398723426348710692715 := by
  unfold tailWord_1262752
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028174560636319858535255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30704232747515093144713673 23028174560636319858535255)
  ·
    refine ⟨34542261840954479787802883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028174560636319858535255 34542261840954479787802883)
    ·
      refine ⟨51813392761431719681704325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34542261840954479787802883 51813392761431719681704325)
      ·
        refine ⟨9715011142768447440319561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51813392761431719681704325 9715011142768447440319561)
        ·
          refine ⟨7286258357076335580239671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9715011142768447440319561 7286258357076335580239671)
          ·
            refine ⟨10929387535614503370359507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286258357076335580239671 10929387535614503370359507)
            ·
              refine ⟨16394081303421755055539261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10929387535614503370359507 16394081303421755055539261)
              ·
                refine ⟨6147780488783158145827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16394081303421755055539261 6147780488783158145827223)
                ·
                  refine ⟨9221670733174737218740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147780488783158145827223 9221670733174737218740835)
                  ·
                    refine ⟨13832506099762105828111253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9221670733174737218740835 13832506099762105828111253)
                    ·
                      refine ⟨648398723426348710692715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13832506099762105828111253 648398723426348710692715)
                      ·
                        rfl

theorem cell23_1262752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1262752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262752 prefixEnd_1262752 := by exact prefixLift 1262752
  have htrace : WordTrace (prefixWord ++ tailWord_1262752) baseStart_1262752 baseEnd_1262752 := by
    simpa [prefixWord, tailWord_1262752, baseEnd_1262752] using wordTrace_append hprefix tailTrace_1262752
  have hstable : (prefixWord ++ tailWord_1262752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262752).length < 2 ^ (prefixWord ++ tailWord_1262752).sum := by decide
  have hdescent : baseEnd_1262752 < baseStart_1262752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262756 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_1262756 : Nat := 118140960795 + 1262756 * 2 ^ 59
def prefixEnd_1262756 : Nat := 4983230072969 + 3 ^ 40 * 1262756 * 2
def baseEnd_1262756 : Nat := 648400777348966695042697

theorem tailTrace_1262756 : CollatzResearch.WordTrace tailWord_1262756 prefixEnd_1262756 648400777348966695042697 := by
  unfold tailWord_1262756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028247506629074200108061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30704330008838765600144081 23028247506629074200108061)
  ·
    refine ⟨8635592814985902825040523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23028247506629074200108061 8635592814985902825040523)
    ·
      refine ⟨12953389222478854237560785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8635592814985902825040523 12953389222478854237560785)
      ·
        refine ⟨9715041916859140678170589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12953389222478854237560785 9715041916859140678170589)
        ·
          refine ⟨3643140718822177754313971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9715041916859140678170589 3643140718822177754313971)
          ·
            refine ⟨5464711078233266631470957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643140718822177754313971 5464711078233266631470957)
            ·
              refine ⟨2049266654337474986801609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5464711078233266631470957 2049266654337474986801609)
              ·
                refine ⟨1536949990753106240101207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049266654337474986801609 1536949990753106240101207)
                ·
                  refine ⟨2305424986129659360151811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536949990753106240101207 2305424986129659360151811)
                  ·
                    refine ⟨3458137479194489040227717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305424986129659360151811 3458137479194489040227717)
                    ·
                      refine ⟨648400777348966695042697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3458137479194489040227717 648400777348966695042697)
                      ·
                        rfl

theorem cell23_1262756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_1262756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262756 prefixEnd_1262756 := by exact prefixLift 1262756
  have htrace : WordTrace (prefixWord ++ tailWord_1262756) baseStart_1262756 baseEnd_1262756 := by
    simpa [prefixWord, tailWord_1262756, baseEnd_1262756] using wordTrace_append hprefix tailTrace_1262756
  have hstable : (prefixWord ++ tailWord_1262756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262756).length < 2 ^ (prefixWord ++ tailWord_1262756).sum := by decide
  have hdescent : baseEnd_1262756 < baseStart_1262756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262769 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1262769 : Nat := 118140960795 + 1262769 * 2 ^ 59
def prefixEnd_1262769 : Nat := 4983230072969 + 3 ^ 40 * 1262769 * 2
def baseEnd_1262769 : Nat := 648407452597475144180137

theorem tailTrace_1262769 : CollatzResearch.WordTrace tailWord_1262769 prefixEnd_1262769 648407452597475144180137 := by
  unfold tailWord_1262769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46056969162211051620439361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30704646108140701080292907 46056969162211051620439361)
  ·
    refine ⟨34542726871658288715329521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46056969162211051620439361 34542726871658288715329521)
    ·
      refine ⟨25907045153743716536497141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34542726871658288715329521 25907045153743716536497141)
      ·
        refine ⟨2428785483163473425296607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25907045153743716536497141 2428785483163473425296607)
        ·
          refine ⟨3643178224745210137944911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428785483163473425296607 3643178224745210137944911)
          ·
            refine ⟨5464767337117815206917367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643178224745210137944911 5464767337117815206917367)
            ·
              refine ⟨8197151005676722810376051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464767337117815206917367 8197151005676722810376051)
              ·
                refine ⟨12295726508515084215564077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197151005676722810376051 12295726508515084215564077)
                ·
                  refine ⟨4610897440693156580836529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12295726508515084215564077 4610897440693156580836529)
                  ·
                    refine ⟨3458173080519867435627397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610897440693156580836529 3458173080519867435627397)
                    ·
                      refine ⟨648407452597475144180137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3458173080519867435627397 648407452597475144180137)
                      ·
                        rfl

theorem cell23_1262769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1262769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262769 prefixEnd_1262769 := by exact prefixLift 1262769
  have htrace : WordTrace (prefixWord ++ tailWord_1262769) baseStart_1262769 baseEnd_1262769 := by
    simpa [prefixWord, tailWord_1262769, baseEnd_1262769] using wordTrace_append hprefix tailTrace_1262769
  have hstable : (prefixWord ++ tailWord_1262769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262769).length < 2 ^ (prefixWord ++ tailWord_1262769).sum := by decide
  have hdescent : baseEnd_1262769 < baseStart_1262769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262792 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1262792 : Nat := 118140960795 + 1262792 * 2 ^ 59
def prefixEnd_1262792 : Nat := 4983230072969 + 3 ^ 40 * 1262792 * 2
def baseEnd_1262792 : Nat := 216139754217509518064177

theorem tailTrace_1262792 : CollatzResearch.WordTrace tailWord_1262792 prefixEnd_1262792 216139754217509518064177 := by
  unfold tailWord_1262792
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028904020563863274263315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30705205360751817699017753 23028904020563863274263315)
  ·
    refine ⟨34543356030845794911394973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028904020563863274263315 34543356030845794911394973)
    ·
      refine ⟨12953758511567173091773115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34543356030845794911394973 12953758511567173091773115)
      ·
        refine ⟨19430637767350759637659673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953758511567173091773115 19430637767350759637659673)
        ·
          refine ⟨14572978325513069728244755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19430637767350759637659673 14572978325513069728244755)
          ·
            refine ⟨21859467488269604592367133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14572978325513069728244755 21859467488269604592367133)
            ·
              refine ⟨8197300308101101722137675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21859467488269604592367133 8197300308101101722137675)
              ·
                refine ⟨12295950462151652583206513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197300308101101722137675 12295950462151652583206513)
                ·
                  refine ⟨9221962846613739437404885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12295950462151652583206513 9221962846613739437404885)
                  ·
                    refine ⟨216139754217509518064177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9221962846613739437404885 216139754217509518064177)
                    ·
                      rfl

theorem cell23_1262792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1262792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262792 prefixEnd_1262792 := by exact prefixLift 1262792
  have htrace : WordTrace (prefixWord ++ tailWord_1262792) baseStart_1262792 baseEnd_1262792 := by
    simpa [prefixWord, tailWord_1262792, baseEnd_1262792] using wordTrace_append hprefix tailTrace_1262792
  have hstable : (prefixWord ++ tailWord_1262792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262792).length < 2 ^ (prefixWord ++ tailWord_1262792).sum := by decide
  have hdescent : baseEnd_1262792 < baseStart_1262792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262816 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2]
def baseStart_1262816 : Nat := 118140960795 + 1262816 * 2 ^ 59
def prefixEnd_1262816 : Nat := 4983230072969 + 3 ^ 40 * 1262816 * 2
def baseEnd_1262816 : Nat := 648431586188236460292421

theorem tailTrace_1262816 : CollatzResearch.WordTrace tailWord_1262816 prefixEnd_1262816 648431586188236460292421 := by
  unfold tailWord_1262816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23029341696520389323700151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30705788928693852431600201 23029341696520389323700151)
  ·
    refine ⟨34544012544780583985550227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23029341696520389323700151 34544012544780583985550227)
    ·
      refine ⟨51816018817170875978325341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34544012544780583985550227 51816018817170875978325341)
      ·
        refine ⟨19431007056439078491872003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51816018817170875978325341 19431007056439078491872003)
        ·
          refine ⟨29146510584658617737808005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19431007056439078491872003 29146510584658617737808005)
          ·
            refine ⟨5464970734623490825839001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29146510584658617737808005 5464970734623490825839001)
            ·
              refine ⟨4098728050967618119379251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464970734623490825839001 4098728050967618119379251)
              ·
                refine ⟨6148092076451427179068877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098728050967618119379251 6148092076451427179068877)
                ·
                  refine ⟨2305534528669285192150829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6148092076451427179068877 2305534528669285192150829)
                  ·
                    refine ⟨864575448250981947056561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305534528669285192150829 864575448250981947056561)
                    ·
                      refine ⟨648431586188236460292421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864575448250981947056561 648431586188236460292421)
                      ·
                        rfl

theorem cell23_1262816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_1262816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262816 prefixEnd_1262816 := by exact prefixLift 1262816
  have htrace : WordTrace (prefixWord ++ tailWord_1262816) baseStart_1262816 baseEnd_1262816 := by
    simpa [prefixWord, tailWord_1262816, baseEnd_1262816] using wordTrace_append hprefix tailTrace_1262816
  have hstable : (prefixWord ++ tailWord_1262816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262816).length < 2 ^ (prefixWord ++ tailWord_1262816).sum := by decide
  have hdescent : baseEnd_1262816 < baseStart_1262816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262859 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_1262859 : Nat := 118140960795 + 1262859 * 2 ^ 59
def prefixEnd_1262859 : Nat := 4983230072969 + 3 ^ 40 * 1262859 * 2
def baseEnd_1262859 : Nat := 648453665856379792054723

theorem tailTrace_1262859 : CollatzResearch.WordTrace tailWord_1262859 prefixEnd_1262859 648453665856379792054723 := by
  unfold tailWord_1262859
  simp only [CollatzResearch.WordTrace]
  refine ⟨46060251731884996991215631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30706834487923331327477087 46060251731884996991215631)
  ·
    refine ⟨69090377597827495486823447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46060251731884996991215631 69090377597827495486823447)
    ·
      refine ⟨103635566396741243230235171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69090377597827495486823447 103635566396741243230235171)
      ·
        refine ⟨155453349595111864845352757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103635566396741243230235171 155453349595111864845352757)
        ·
          refine ⟨14573751524541737329251821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155453349595111864845352757 14573751524541737329251821)
          ·
            refine ⟨5465156821703151498469433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14573751524541737329251821 5465156821703151498469433)
            ·
              refine ⟨4098867616277363623852075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5465156821703151498469433 4098867616277363623852075)
              ·
                refine ⟨6148301424416045435778113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098867616277363623852075 6148301424416045435778113)
                ·
                  refine ⟨4611226068312034076833585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148301424416045435778113 4611226068312034076833585)
                  ·
                    refine ⟨3458419551234025557625189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611226068312034076833585 3458419551234025557625189)
                    ·
                      refine ⟨648453665856379792054723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3458419551234025557625189 648453665856379792054723)
                      ·
                        rfl

theorem cell23_1262859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_1262859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262859 prefixEnd_1262859 := by exact prefixLift 1262859
  have htrace : WordTrace (prefixWord ++ tailWord_1262859) baseStart_1262859 baseEnd_1262859 := by
    simpa [prefixWord, tailWord_1262859, baseEnd_1262859] using wordTrace_append hprefix tailTrace_1262859
  have hstable : (prefixWord ++ tailWord_1262859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262859).length < 2 ^ (prefixWord ++ tailWord_1262859).sum := by decide
  have hdescent : baseEnd_1262859 < baseStart_1262859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262899 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 4, 5]
def baseStart_1262899 : Nat := 118140960795 + 1262899 * 2 ^ 59
def prefixEnd_1262899 : Nat := 4983230072969 + 3 ^ 40 * 1262899 * 2
def baseEnd_1262899 : Nat := 216158068360853211851513

theorem tailTrace_1262899 : CollatzResearch.WordTrace tailWord_1262899 prefixEnd_1262899 216158068360853211851513 := by
  unfold tailWord_1262899
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061710651740083822671751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30707807101160055881781167 46061710651740083822671751)
  ·
    refine ⟨69092565977610125734007627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46061710651740083822671751 69092565977610125734007627)
    ·
      refine ⟨103638848966415188601011441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69092565977610125734007627 103638848966415188601011441)
      ·
        refine ⟨77729136724811391450758581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103638848966415188601011441 77729136724811391450758581)
        ·
          refine ⟨7287106567951067948508617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77729136724811391450758581 7287106567951067948508617)
          ·
            refine ⟨5465329925963300961381463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7287106567951067948508617 5465329925963300961381463)
            ·
              refine ⟨8197994888944951442072195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465329925963300961381463 8197994888944951442072195)
              ·
                refine ⟨12296992333417427163108293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197994888944951442072195 12296992333417427163108293)
                ·
                  refine ⟨2305686062515767593082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12296992333417427163108293 2305686062515767593082805)
                  ·
                    refine ⟨216158068360853211851513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2305686062515767593082805 216158068360853211851513)
                    ·
                      rfl

theorem cell23_1262899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 5].length) (baseStart_1262899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262899 prefixEnd_1262899 := by exact prefixLift 1262899
  have htrace : WordTrace (prefixWord ++ tailWord_1262899) baseStart_1262899 baseEnd_1262899 := by
    simpa [prefixWord, tailWord_1262899, baseEnd_1262899] using wordTrace_append hprefix tailTrace_1262899
  have hstable : (prefixWord ++ tailWord_1262899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262899).length < 2 ^ (prefixWord ++ tailWord_1262899).sum := by decide
  have hdescent : baseEnd_1262899 < baseStart_1262899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262906 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_1262906 : Nat := 118140960795 + 1262906 * 2 ^ 59
def prefixEnd_1262906 : Nat := 4983230072969 + 3 ^ 40 * 1262906 * 2
def baseEnd_1262906 : Nat := 648477799447141108167007

theorem tailTrace_1262906 : CollatzResearch.WordTrace tailWord_1262906 prefixEnd_1262906 648477799447141108167007 := by
  unfold tailWord_1262906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515491490678681004544143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30707977308476482678784381 11515491490678681004544143)
  ·
    refine ⟨17273237236018021506816215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11515491490678681004544143 17273237236018021506816215)
    ·
      refine ⟨25909855854027032260224323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17273237236018021506816215 25909855854027032260224323)
      ·
        refine ⟨38864783781040548390336485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25909855854027032260224323 38864783781040548390336485)
        ·
          refine ⟨7287146958945102823188091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38864783781040548390336485 7287146958945102823188091)
          ·
            refine ⟨10930720438417654234782137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287146958945102823188091 10930720438417654234782137)
            ·
              refine ⟨8198040328813240676086603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10930720438417654234782137 8198040328813240676086603)
              ·
                refine ⟨12297060493219861014129905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198040328813240676086603 12297060493219861014129905)
                ·
                  refine ⟨9222795369914895760597429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12297060493219861014129905 9222795369914895760597429)
                  ·
                    refine ⟨864637065929521477556009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9222795369914895760597429 864637065929521477556009)
                    ·
                      refine ⟨648477799447141108167007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864637065929521477556009 648477799447141108167007)
                      ·
                        rfl

theorem cell23_1262906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_1262906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262906 prefixEnd_1262906 := by exact prefixLift 1262906
  have htrace : WordTrace (prefixWord ++ tailWord_1262906) baseStart_1262906 baseEnd_1262906 := by
    simpa [prefixWord, tailWord_1262906, baseEnd_1262906] using wordTrace_append hprefix tailTrace_1262906
  have hstable : (prefixWord ++ tailWord_1262906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262906).length < 2 ^ (prefixWord ++ tailWord_1262906).sum := by decide
  have hdescent : baseEnd_1262906 < baseStart_1262906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262936 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1262936 : Nat := 118140960795 + 1262936 * 2 ^ 59
def prefixEnd_1262936 : Nat := 4983230072969 + 3 ^ 40 * 1262936 * 2
def baseEnd_1262936 : Nat := 648493203866775990791869

theorem tailTrace_1262936 : CollatzResearch.WordTrace tailWord_1262936 prefixEnd_1262936 648493203866775990791869 := by
  unfold tailWord_1262936
  simp only [CollatzResearch.WordTrace]
  refine ⟨23031530076303019570884331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30708706768404026094512441 23031530076303019570884331)
  ·
    refine ⟨34547295114454529356326497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23031530076303019570884331 34547295114454529356326497)
    ·
      refine ⟨25910471335840897017244873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34547295114454529356326497 25910471335840897017244873)
      ·
        refine ⟨19432853501880672762933655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25910471335840897017244873 19432853501880672762933655)
        ·
          refine ⟨29149280252821009144400483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19432853501880672762933655 29149280252821009144400483)
          ·
            refine ⟨43723920379231513716600725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29149280252821009144400483 43723920379231513716600725)
            ·
              refine ⟨2049558767776477205465659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43723920379231513716600725 2049558767776477205465659)
              ·
                refine ⟨3074338151664715808198489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049558767776477205465659 3074338151664715808198489)
                ·
                  refine ⟨2305753613748536856148867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074338151664715808198489 2305753613748536856148867)
                  ·
                    refine ⟨3458630420622805284223301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305753613748536856148867 3458630420622805284223301)
                    ·
                      refine ⟨648493203866775990791869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3458630420622805284223301 648493203866775990791869)
                      ·
                        rfl

theorem cell23_1262936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1262936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262936 prefixEnd_1262936 := by exact prefixLift 1262936
  have htrace : WordTrace (prefixWord ++ tailWord_1262936) baseStart_1262936 baseEnd_1262936 := by
    simpa [prefixWord, tailWord_1262936, baseEnd_1262936] using wordTrace_append hprefix tailTrace_1262936
  have hstable : (prefixWord ++ tailWord_1262936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262936).length < 2 ^ (prefixWord ++ tailWord_1262936).sum := by decide
  have hdescent : baseEnd_1262936 < baseStart_1262936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262949 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1262949 : Nat := 118140960795 + 1262949 * 2 ^ 59
def prefixEnd_1262949 : Nat := 4983230072969 + 3 ^ 40 * 1262949 * 2
def baseEnd_1262949 : Nat := 648499879115284439929309

theorem tailTrace_1262949 : CollatzResearch.WordTrace tailWord_1262949 prefixEnd_1262949 648499879115284439929309 := by
  unfold tailWord_1262949
  simp only [CollatzResearch.WordTrace]
  refine ⟨46063534301558942361991901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30709022867705961574661267 46063534301558942361991901)
  ·
    refine ⟨17273825363084603385746963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46063534301558942361991901 17273825363084603385746963)
    ·
      refine ⟨25910738044626905078620445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17273825363084603385746963 25910738044626905078620445)
      ·
        refine ⟨9716526766735089404482667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25910738044626905078620445 9716526766735089404482667)
        ·
          refine ⟨14574790150102634106724001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716526766735089404482667 14574790150102634106724001)
          ·
            refine ⟨10931092612576975580043001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14574790150102634106724001 10931092612576975580043001)
            ·
              refine ⟨8198319459432731685032251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10931092612576975580043001 8198319459432731685032251)
              ·
                refine ⟨12297479189149097527548377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198319459432731685032251 12297479189149097527548377)
                ·
                  refine ⟨9223109391861823145661283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12297479189149097527548377 9223109391861823145661283)
                  ·
                    refine ⟨13834664087792734718491925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9223109391861823145661283 13834664087792734718491925)
                    ·
                      refine ⟨648499879115284439929309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13834664087792734718491925 648499879115284439929309)
                      ·
                        rfl

theorem cell23_1262949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1262949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262949 prefixEnd_1262949 := by exact prefixLift 1262949
  have htrace : WordTrace (prefixWord ++ tailWord_1262949) baseStart_1262949 baseEnd_1262949 := by
    simpa [prefixWord, tailWord_1262949, baseEnd_1262949] using wordTrace_append hprefix tailTrace_1262949
  have hstable : (prefixWord ++ tailWord_1262949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262949).length < 2 ^ (prefixWord ++ tailWord_1262949).sum := by decide
  have hdescent : baseEnd_1262949 < baseStart_1262949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1262999 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1262999 : Nat := 118140960795 + 1262999 * 2 ^ 59
def prefixEnd_1262999 : Nat := 4983230072969 + 3 ^ 40 * 1262999 * 2
def baseEnd_1262999 : Nat := 648525553148009244304079

theorem tailTrace_1262999 : CollatzResearch.WordTrace tailWord_1262999 prefixEnd_1262999 648525553148009244304079 := by
  unfold tailWord_1262999
  simp only [CollatzResearch.WordTrace]
  refine ⟨46065357951377800901312051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30710238634251867267541367 46065357951377800901312051)
  ·
    refine ⟨69098036927066701351968077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46065357951377800901312051 69098036927066701351968077)
    ·
      refine ⟨25911763847650013006988029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69098036927066701351968077 25911763847650013006988029)
      ·
        refine ⟨9716911442868754877620511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25911763847650013006988029 9716911442868754877620511)
        ·
          refine ⟨14575367164303132316430767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716911442868754877620511 14575367164303132316430767)
          ·
            refine ⟨21863050746454698474646151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14575367164303132316430767 21863050746454698474646151)
            ·
              refine ⟨32794576119682047711969227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21863050746454698474646151 32794576119682047711969227)
              ·
                refine ⟨49191864179523071567953841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32794576119682047711969227 49191864179523071567953841)
                ·
                  refine ⟨36893898134642303675965381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49191864179523071567953841 36893898134642303675965381)
                  ·
                    refine ⟨6917605900245431939243509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36893898134642303675965381 6917605900245431939243509)
                    ·
                      refine ⟨648525553148009244304079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6917605900245431939243509 648525553148009244304079)
                      ·
                        rfl

theorem cell23_1262999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1262999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1262999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1262999 prefixEnd_1262999 := by exact prefixLift 1262999
  have htrace : WordTrace (prefixWord ++ tailWord_1262999) baseStart_1262999 baseEnd_1262999 := by
    simpa [prefixWord, tailWord_1262999, baseEnd_1262999] using wordTrace_append hprefix tailTrace_1262999
  have hstable : (prefixWord ++ tailWord_1262999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1262999).length < 2 ^ (prefixWord ++ tailWord_1262999).sum := by decide
  have hdescent : baseEnd_1262999 < baseStart_1262999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1262999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263020 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_1263020 : Nat := 118140960795 + 1263020 * 2 ^ 59
def prefixEnd_1263020 : Nat := 4983230072969 + 3 ^ 40 * 1263020 * 2
def baseEnd_1263020 : Nat := 648536336241753662141483

theorem tailTrace_1263020 : CollatzResearch.WordTrace tailWord_1263020 prefixEnd_1263020 648536336241753662141483 := by
  unfold tailWord_1263020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23033061942150860743913257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30710749256201147658551009 23033061942150860743913257)
  ·
    refine ⟨17274796456613145557934943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23033061942150860743913257 17274796456613145557934943)
    ·
      refine ⟨25912194684919718336902415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17274796456613145557934943 25912194684919718336902415)
      ·
        refine ⟨38868292027379577505353623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25912194684919718336902415 38868292027379577505353623)
        ·
          refine ⟨58302438041069366258030435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38868292027379577505353623 58302438041069366258030435)
          ·
            refine ⟨87453657061604049387045653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58302438041069366258030435 87453657061604049387045653)
            ·
              refine ⟨4099390174762689815017765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87453657061604049387045653 4099390174762689815017765)
              ·
                refine ⟨768635657768004340315831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4099390174762689815017765 768635657768004340315831)
                ·
                  refine ⟨1152953486652006510473747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768635657768004340315831 1152953486652006510473747)
                  ·
                    refine ⟨1729430229978009765710621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1152953486652006510473747 1729430229978009765710621)
                    ·
                      refine ⟨648536336241753662141483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1729430229978009765710621 648536336241753662141483)
                      ·
                        rfl

theorem cell23_1263020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_1263020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263020 prefixEnd_1263020 := by exact prefixLift 1263020
  have htrace : WordTrace (prefixWord ++ tailWord_1263020) baseStart_1263020 baseEnd_1263020 := by
    simpa [prefixWord, tailWord_1263020, baseEnd_1263020] using wordTrace_append hprefix tailTrace_1263020
  have hstable : (prefixWord ++ tailWord_1263020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263020).length < 2 ^ (prefixWord ++ tailWord_1263020).sum := by decide
  have hdescent : baseEnd_1263020 < baseStart_1263020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263026 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1263026 : Nat := 118140960795 + 1263026 * 2 ^ 59
def prefixEnd_1263026 : Nat := 4983230072969 + 3 ^ 40 * 1263026 * 2
def baseEnd_1263026 : Nat := 648539417125680638666455

theorem tailTrace_1263026 : CollatzResearch.WordTrace tailWord_1263026 prefixEnd_1263026 648539417125680638666455 := by
  unfold tailWord_1263026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516585680569996128136233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30710895148186656341696621 11516585680569996128136233)
  ·
    refine ⟨8637439260427497096102175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11516585680569996128136233 8637439260427497096102175)
    ·
      refine ⟨12956158890641245644153263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8637439260427497096102175 12956158890641245644153263)
      ·
        refine ⟨19434238335961868466229895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12956158890641245644153263 19434238335961868466229895)
        ·
          refine ⟨29151357503942802699344843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19434238335961868466229895 29151357503942802699344843)
          ·
            refine ⟨43727036255914204049017265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29151357503942802699344843 43727036255914204049017265)
            ·
              refine ⟨32795277191935653036762949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43727036255914204049017265 32795277191935653036762949)
              ·
                refine ⟨6149114473487934944393053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32795277191935653036762949 6149114473487934944393053)
                ·
                  refine ⟨2305917927557975604147395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6149114473487934944393053 2305917927557975604147395)
                  ·
                    refine ⟨3458876891336963406221093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305917927557975604147395 3458876891336963406221093)
                    ·
                      refine ⟨648539417125680638666455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3458876891336963406221093 648539417125680638666455)
                      ·
                        rfl

theorem cell23_1263026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1263026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263026 prefixEnd_1263026 := by exact prefixLift 1263026
  have htrace : WordTrace (prefixWord ++ tailWord_1263026) baseStart_1263026 baseEnd_1263026 := by
    simpa [prefixWord, tailWord_1263026, baseEnd_1263026] using wordTrace_append hprefix tailTrace_1263026
  have hstable : (prefixWord ++ tailWord_1263026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263026).length < 2 ^ (prefixWord ++ tailWord_1263026).sum := by decide
  have hdescent : baseEnd_1263026 < baseStart_1263026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263066 : List Nat := [3, 1, 1, 2, 3, 4, 9]
def baseStart_1263066 : Nat := 118140960795 + 1263066 * 2 ^ 59
def prefixEnd_1263066 : Nat := 4983230072969 + 3 ^ 40 * 1263066 * 2
def baseEnd_1263066 : Nat := 8006913041380993606991

theorem tailTrace_1263066 : CollatzResearch.WordTrace tailWord_1263066 prefixEnd_1263066 8006913041380993606991 := by
  unfold tailWord_1263066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11516950410533767836000263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30711867761423380896000701 11516950410533767836000263)
  ·
    refine ⟨17275425615800651754000395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11516950410533767836000263 17275425615800651754000395)
    ·
      refine ⟨25913138423700977631000593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17275425615800651754000395 25913138423700977631000593)
      ·
        refine ⟨19434853817775733223250445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25913138423700977631000593 19434853817775733223250445)
        ·
          refine ⟨7288070181665899958718917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19434853817775733223250445 7288070181665899958718917)
          ·
            refine ⟨1366513159062356242259797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7288070181665899958718917 1366513159062356242259797)
            ·
              refine ⟨8006913041380993606991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1366513159062356242259797 8006913041380993606991)
              ·
                rfl

theorem cell23_1263066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 9].length) (baseStart_1263066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263066 prefixEnd_1263066 := by exact prefixLift 1263066
  have htrace : WordTrace (prefixWord ++ tailWord_1263066) baseStart_1263066 baseEnd_1263066 := by
    simpa [prefixWord, tailWord_1263066, baseEnd_1263066] using wordTrace_append hprefix tailTrace_1263066
  have hstable : (prefixWord ++ tailWord_1263066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263066).length < 2 ^ (prefixWord ++ tailWord_1263066).sum := by decide
  have hdescent : baseEnd_1263066 < baseStart_1263066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263077 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1263077 : Nat := 118140960795 + 1263077 * 2 ^ 59
def prefixEnd_1263077 : Nat := 4983230072969 + 3 ^ 40 * 1263077 * 2
def baseEnd_1263077 : Nat := 648565604639059939128721

theorem tailTrace_1263077 : CollatzResearch.WordTrace tailWord_1263077 prefixEnd_1263077 648565604639059939128721 := by
  unfold tailWord_1263077
  simp only [CollatzResearch.WordTrace]
  refine ⟨46068202845095220222651485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30712135230063480148434323 46068202845095220222651485)
  ·
    refine ⟨17275576066910707583494307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46068202845095220222651485 17275576066910707583494307)
    ·
      refine ⟨25913364100366061375241461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17275576066910707583494307 25913364100366061375241461)
      ·
        refine ⟨2429377884409318253928887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25913364100366061375241461 2429377884409318253928887)
        ·
          refine ⟨3644066826613977380893331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429377884409318253928887 3644066826613977380893331)
          ·
            refine ⟨5466100239920966071339997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644066826613977380893331 5466100239920966071339997)
            ·
              refine ⟨2049787589970362276752499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5466100239920966071339997 2049787589970362276752499)
              ·
                refine ⟨3074681384955543415128749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049787589970362276752499 3074681384955543415128749)
                ·
                  refine ⟨1153005519358328780673281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3074681384955543415128749 1153005519358328780673281)
                  ·
                    refine ⟨864754139518746585504961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153005519358328780673281 864754139518746585504961)
                    ·
                      refine ⟨648565604639059939128721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864754139518746585504961 648565604639059939128721)
                      ·
                        rfl

theorem cell23_1263077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1263077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263077 prefixEnd_1263077 := by exact prefixLift 1263077
  have htrace : WordTrace (prefixWord ++ tailWord_1263077) baseStart_1263077 baseEnd_1263077 := by
    simpa [prefixWord, tailWord_1263077, baseEnd_1263077] using wordTrace_append hprefix tailTrace_1263077
  have hstable : (prefixWord ++ tailWord_1263077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263077).length < 2 ^ (prefixWord ++ tailWord_1263077).sum := by decide
  have hdescent : baseEnd_1263077 < baseStart_1263077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263086 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1263086 : Nat := 118140960795 + 1263086 * 2 ^ 59
def prefixEnd_1263086 : Nat := 4983230072969 + 3 ^ 40 * 1263086 * 2
def baseEnd_1263086 : Nat := 648570225964950403916179

theorem tailTrace_1263086 : CollatzResearch.WordTrace tailWord_1263086 prefixEnd_1263086 648570225964950403916179 := by
  unfold tailWord_1263086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758566387757826844966139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30712354068041743173152741 5758566387757826844966139)
  ·
    refine ⟨8637849581636740267449209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5758566387757826844966139 8637849581636740267449209)
    ·
      refine ⟨6478387186227555200586907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8637849581636740267449209 6478387186227555200586907)
      ·
        refine ⟨9717580779341332800880361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6478387186227555200586907 9717580779341332800880361)
        ·
          refine ⟨7288185584505999600660271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9717580779341332800880361 7288185584505999600660271)
          ·
            refine ⟨10932278376758999400990407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288185584505999600660271 10932278376758999400990407)
            ·
              refine ⟨16398417565138499101485611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932278376758999400990407 16398417565138499101485611)
              ·
                refine ⟨24597626347707748652228417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16398417565138499101485611 24597626347707748652228417)
                ·
                  refine ⟨18448219760780811489171313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24597626347707748652228417 18448219760780811489171313)
                  ·
                    refine ⟨13836164820585608616878485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18448219760780811489171313 13836164820585608616878485)
                    ·
                      refine ⟨648570225964950403916179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13836164820585608616878485 648570225964950403916179)
                      ·
                        rfl

theorem cell23_1263086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1263086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263086 prefixEnd_1263086 := by exact prefixLift 1263086
  have htrace : WordTrace (prefixWord ++ tailWord_1263086) baseStart_1263086 baseEnd_1263086 := by
    simpa [prefixWord, tailWord_1263086, baseEnd_1263086] using wordTrace_append hprefix tailTrace_1263086
  have hstable : (prefixWord ++ tailWord_1263086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263086).length < 2 ^ (prefixWord ++ tailWord_1263086).sum := by decide
  have hdescent : baseEnd_1263086 < baseStart_1263086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263128 : List Nat := [2, 1, 2, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1263128 : Nat := 118140960795 + 1263128 * 2 ^ 59
def prefixEnd_1263128 : Nat := 4983230072969 + 3 ^ 40 * 1263128 * 2
def baseEnd_1263128 : Nat := 648591792152439239590987

theorem tailTrace_1263128 : CollatzResearch.WordTrace tailWord_1263128 prefixEnd_1263128 648591792152439239590987 := by
  unfold tailWord_1263128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035031483955227966379019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30713375311940303955172025 23035031483955227966379019)
  ·
    refine ⟨34552547225932841949568529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23035031483955227966379019 34552547225932841949568529)
    ·
      refine ⟨25914410419449631462176397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34552547225932841949568529 25914410419449631462176397)
      ·
        refine ⟨9717903907293611798316149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25914410419449631462176397 9717903907293611798316149)
        ·
          refine ⟨911053491308776106092139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9717903907293611798316149 911053491308776106092139)
          ·
            refine ⟨1366580236963164159138209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911053491308776106092139 1366580236963164159138209)
            ·
              refine ⟨1024935177722373119353657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1366580236963164159138209 1024935177722373119353657)
              ·
                refine ⟨768701383291779839515243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1024935177722373119353657 768701383291779839515243)
                ·
                  refine ⟨1153052074937669759272865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768701383291779839515243 1153052074937669759272865)
                  ·
                    refine ⟨864789056203252319454649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153052074937669759272865 864789056203252319454649)
                    ·
                      refine ⟨648591792152439239590987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864789056203252319454649 648591792152439239590987)
                      ·
                        rfl

theorem cell23_1263128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1263128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263128 prefixEnd_1263128 := by exact prefixLift 1263128
  have htrace : WordTrace (prefixWord ++ tailWord_1263128) baseStart_1263128 baseEnd_1263128 := by
    simpa [prefixWord, tailWord_1263128, baseEnd_1263128] using wordTrace_append hprefix tailTrace_1263128
  have hstable : (prefixWord ++ tailWord_1263128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263128).length < 2 ^ (prefixWord ++ tailWord_1263128).sum := by decide
  have hdescent : baseEnd_1263128 < baseStart_1263128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263134 : List Nat := [4, 3, 3, 1, 1, 2, 1, 8]
def baseStart_1263134 : Nat := 118140960795 + 1263134 * 2 ^ 59
def prefixEnd_1263134 : Nat := 4983230072969 + 3 ^ 40 * 1263134 * 2
def baseEnd_1263134 : Nat := 24022032334680230226517

theorem tailTrace_1263134 : CollatzResearch.WordTrace tailWord_1263134 prefixEnd_1263134 24022032334680230226517 := by
  unfold tailWord_1263134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5758785225736089869684557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30713521203925812638317637 5758785225736089869684557)
  ·
    refine ⟨2159544459651033701131709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5758785225736089869684557 2159544459651033701131709)
    ·
      refine ⟨809829172369137637924391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2159544459651033701131709 809829172369137637924391)
      ·
        refine ⟨1214743758553706456886587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809829172369137637924391 1214743758553706456886587)
        ·
          refine ⟨1822115637830559685329881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214743758553706456886587 1822115637830559685329881)
          ·
            refine ⟨1366586728372919763997411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822115637830559685329881 1366586728372919763997411)
            ·
              refine ⟨2049880092559379645996117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366586728372919763997411 2049880092559379645996117)
              ·
                refine ⟨24022032334680230226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2049880092559379645996117 24022032334680230226517)
                ·
                  rfl

theorem cell23_1263134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_1263134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263134 prefixEnd_1263134 := by exact prefixLift 1263134
  have htrace : WordTrace (prefixWord ++ tailWord_1263134) baseStart_1263134 baseEnd_1263134 := by
    simpa [prefixWord, tailWord_1263134, baseEnd_1263134] using wordTrace_append hprefix tailTrace_1263134
  have hstable : (prefixWord ++ tailWord_1263134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263134).length < 2 ^ (prefixWord ++ tailWord_1263134).sum := by decide
  have hdescent : baseEnd_1263134 < baseStart_1263134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263193 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 7, 2]
def baseStart_1263193 : Nat := 118140960795 + 1263193 * 2 ^ 59
def prefixEnd_1263193 : Nat := 4983230072969 + 3 ^ 40 * 1263193 * 2
def baseEnd_1263193 : Nat := 648625168394981485278187

theorem tailTrace_1263193 : CollatzResearch.WordTrace tailWord_1263193 prefixEnd_1263193 648625168394981485278187 := by
  unfold tailWord_1263193
  simp only [CollatzResearch.WordTrace]
  refine ⟨46072433712674972033874233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30714955808449981355916155 46072433712674972033874233)
  ·
    refine ⟨34554325284506229025405675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46072433712674972033874233 34554325284506229025405675)
    ·
      refine ⟨51831487926759343538108513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34554325284506229025405675 51831487926759343538108513)
      ·
        refine ⟨38873615945069507653581385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51831487926759343538108513 38873615945069507653581385)
        ·
          refine ⟨29155211958802130740186039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38873615945069507653581385 29155211958802130740186039)
          ·
            refine ⟨43732817938203196110279059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29155211958802130740186039 43732817938203196110279059)
            ·
              refine ⟨65599226907304794165418589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43732817938203196110279059 65599226907304794165418589)
              ·
                refine ⟨24599710090239297812031971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65599226907304794165418589 24599710090239297812031971)
                ·
                  refine ⟨36899565135358946718047957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24599710090239297812031971 36899565135358946718047957)
                  ·
                    refine ⟨864833557859975313704249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36899565135358946718047957 864833557859975313704249)
                    ·
                      refine ⟨648625168394981485278187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864833557859975313704249 648625168394981485278187)
                      ·
                        rfl

theorem cell23_1263193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_1263193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263193 prefixEnd_1263193 := by exact prefixLift 1263193
  have htrace : WordTrace (prefixWord ++ tailWord_1263193) baseStart_1263193 baseEnd_1263193 := by
    simpa [prefixWord, tailWord_1263193, baseEnd_1263193] using wordTrace_append hprefix tailTrace_1263193
  have hstable : (prefixWord ++ tailWord_1263193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263193).length < 2 ^ (prefixWord ++ tailWord_1263193).sum := by decide
  have hdescent : baseEnd_1263193 < baseStart_1263193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263223 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_1263223 : Nat := 118140960795 + 1263223 * 2 ^ 59
def prefixEnd_1263223 : Nat := 4983230072969 + 3 ^ 40 * 1263223 * 2
def baseEnd_1263223 : Nat := 648640572814616367903049

theorem tailTrace_1263223 : CollatzResearch.WordTrace tailWord_1263223 prefixEnd_1263223 648640572814616367903049 := by
  unfold tailWord_1263223
  simp only [CollatzResearch.WordTrace]
  refine ⟨46073527902566287157466323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30715685268377524771644215 46073527902566287157466323)
  ·
    refine ⟨69110291853849430736199485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46073527902566287157466323 69110291853849430736199485)
    ·
      refine ⟨25916359445193536526074807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69110291853849430736199485 25916359445193536526074807)
      ·
        refine ⟨38874539167790304789112211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25916359445193536526074807 38874539167790304789112211)
        ·
          refine ⟨58311808751685457183668317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38874539167790304789112211 58311808751685457183668317)
          ·
            refine ⟨21866928281882046443875619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58311808751685457183668317 21866928281882046443875619)
            ·
              refine ⟨32800392422823069665813429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21866928281882046443875619 32800392422823069665813429)
              ·
                refine ⟨3075036789639662781170009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32800392422823069665813429 3075036789639662781170009)
                ·
                  refine ⟨2306277592229747085877507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075036789639662781170009 2306277592229747085877507)
                  ·
                    refine ⟨3459416388344620628816261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306277592229747085877507 3459416388344620628816261)
                    ·
                      refine ⟨648640572814616367903049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3459416388344620628816261 648640572814616367903049)
                      ·
                        rfl

theorem cell23_1263223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_1263223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263223 prefixEnd_1263223 := by exact prefixLift 1263223
  have htrace : WordTrace (prefixWord ++ tailWord_1263223) baseStart_1263223 baseEnd_1263223 := by
    simpa [prefixWord, tailWord_1263223, baseEnd_1263223] using wordTrace_append hprefix tailTrace_1263223
  have hstable : (prefixWord ++ tailWord_1263223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263223).length < 2 ^ (prefixWord ++ tailWord_1263223).sum := by decide
  have hdescent : baseEnd_1263223 < baseStart_1263223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263277 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1263277 : Nat := 118140960795 + 1263277 * 2 ^ 59
def prefixEnd_1263277 : Nat := 4983230072969 + 3 ^ 40 * 1263277 * 2
def baseEnd_1263277 : Nat := 648668300769959156627801

theorem tailTrace_1263277 : CollatzResearch.WordTrace tailWord_1263277 prefixEnd_1263277 648668300769959156627801 := by
  unfold tailWord_1263277
  simp only [CollatzResearch.WordTrace]
  refine ⟨46075497444370654379932085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30716998296247102919954723 46075497444370654379932085)
  ·
    refine ⟨4319577885409748848118633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46075497444370654379932085 4319577885409748848118633)
    ·
      refine ⟨3239683414057311636088975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4319577885409748848118633 3239683414057311636088975)
      ·
        refine ⟨4859525121085967454133463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239683414057311636088975 4859525121085967454133463)
        ·
          refine ⟨7289287681628951181200195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859525121085967454133463 7289287681628951181200195)
          ·
            refine ⟨10933931522443426771800293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289287681628951181200195 10933931522443426771800293)
            ·
              refine ⟨2050112160458142519712555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10933931522443426771800293 2050112160458142519712555)
              ·
                refine ⟨3075168240687213779568833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050112160458142519712555 3075168240687213779568833)
                ·
                  refine ⟨2306376180515410334676625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075168240687213779568833 2306376180515410334676625)
                  ·
                    refine ⟨1729782135386557751007469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2306376180515410334676625 1729782135386557751007469)
                    ·
                      refine ⟨648668300769959156627801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1729782135386557751007469 648668300769959156627801)
                      ·
                        rfl

theorem cell23_1263277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1263277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263277 prefixEnd_1263277 := by exact prefixLift 1263277
  have htrace : WordTrace (prefixWord ++ tailWord_1263277) baseStart_1263277 baseEnd_1263277 := by
    simpa [prefixWord, tailWord_1263277, baseEnd_1263277] using wordTrace_append hprefix tailTrace_1263277
  have hstable : (prefixWord ++ tailWord_1263277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263277).length < 2 ^ (prefixWord ++ tailWord_1263277).sum := by decide
  have hdescent : baseEnd_1263277 < baseStart_1263277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263341 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1263341 : Nat := 118140960795 + 1263341 * 2 ^ 59
def prefixEnd_1263341 : Nat := 4983230072969 + 3 ^ 40 * 1263341 * 2
def baseEnd_1263341 : Nat := 648701163531846906227507

theorem tailTrace_1263341 : CollatzResearch.WordTrace tailWord_1263341 prefixEnd_1263341 648701163531846906227507 := by
  unfold tailWord_1263341
  simp only [CollatzResearch.WordTrace]
  refine ⟨46077831716138793310261877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30718554477425862206841251 46077831716138793310261877)
  ·
    refine ⟨4319796723388011872837051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46077831716138793310261877 4319796723388011872837051)
    ·
      refine ⟨6479695085082017809255577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4319796723388011872837051 6479695085082017809255577)
      ·
        refine ⟨4859771313811513356941683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479695085082017809255577 4859771313811513356941683)
        ·
          refine ⟨7289656970717270035412525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859771313811513356941683 7289656970717270035412525)
          ·
            refine ⟨2733621364018976263279697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7289656970717270035412525 2733621364018976263279697)
            ·
              refine ⟨2050216023014232197459773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733621364018976263279697 2050216023014232197459773)
              ·
                refine ⟨768831008630337074047415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2050216023014232197459773 768831008630337074047415)
                ·
                  refine ⟨1153246512945505611071123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768831008630337074047415 1153246512945505611071123)
                  ·
                    refine ⟨1729869769418258416606685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153246512945505611071123 1729869769418258416606685)
                    ·
                      refine ⟨648701163531846906227507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1729869769418258416606685 648701163531846906227507)
                      ·
                        rfl

theorem cell23_1263341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1263341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263341 prefixEnd_1263341 := by exact prefixLift 1263341
  have htrace : WordTrace (prefixWord ++ tailWord_1263341) baseStart_1263341 baseEnd_1263341 := by
    simpa [prefixWord, tailWord_1263341, baseEnd_1263341] using wordTrace_append hprefix tailTrace_1263341
  have hstable : (prefixWord ++ tailWord_1263341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263341).length < 2 ^ (prefixWord ++ tailWord_1263341).sum := by decide
  have hdescent : baseEnd_1263341 < baseStart_1263341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263347 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 1, 1, 4]
def baseStart_1263347 : Nat := 118140960795 + 1263347 * 2 ^ 59
def prefixEnd_1263347 : Nat := 4983230072969 + 3 ^ 40 * 1263347 * 2
def baseEnd_1263347 : Nat := 648704244415773882752479

theorem tailTrace_1263347 : CollatzResearch.WordTrace tailWord_1263347 prefixEnd_1263347 648704244415773882752479 := by
  unfold tailWord_1263347
  simp only [CollatzResearch.WordTrace]
  refine ⟨46078050554117056334980295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30718700369411370889986863 46078050554117056334980295)
  ·
    refine ⟨69117075831175584502470443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46078050554117056334980295 69117075831175584502470443)
    ·
      refine ⟨103675613746763376753705665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69117075831175584502470443 103675613746763376753705665)
      ·
        refine ⟨77756710310072532565279249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103675613746763376753705665 77756710310072532565279249)
        ·
          refine ⟨58317532732554399423959437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77756710310072532565279249 58317532732554399423959437)
          ·
            refine ⟨21869074774707899783984789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58317532732554399423959437 21869074774707899783984789)
            ·
              refine ⟨1025112880064432802374287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21869074774707899783984789 1025112880064432802374287)
              ·
                refine ⟨1537669320096649203561431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025112880064432802374287 1537669320096649203561431)
                ·
                  refine ⟨2306503980144973805342147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537669320096649203561431 2306503980144973805342147)
                  ·
                    refine ⟨3459755970217460708013221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306503980144973805342147 3459755970217460708013221)
                    ·
                      refine ⟨648704244415773882752479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3459755970217460708013221 648704244415773882752479)
                      ·
                        rfl

theorem cell23_1263347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 1, 4].length) (baseStart_1263347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263347 prefixEnd_1263347 := by exact prefixLift 1263347
  have htrace : WordTrace (prefixWord ++ tailWord_1263347) baseStart_1263347 baseEnd_1263347 := by
    simpa [prefixWord, tailWord_1263347, baseEnd_1263347] using wordTrace_append hprefix tailTrace_1263347
  have hstable : (prefixWord ++ tailWord_1263347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263347).length < 2 ^ (prefixWord ++ tailWord_1263347).sum := by decide
  have hdescent : baseEnd_1263347 < baseStart_1263347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263364 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_1263364 : Nat := 118140960795 + 1263364 * 2 ^ 59
def prefixEnd_1263364 : Nat := 4983230072969 + 3 ^ 40 * 1263364 * 2
def baseEnd_1263364 : Nat := 648712973586900316239901

theorem tailTrace_1263364 : CollatzResearch.WordTrace tailWord_1263364 prefixEnd_1263364 648712973586900316239901 := by
  unfold tailWord_1263364
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039335297527734119174573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30719113730036978825566097 23039335297527734119174573)
  ·
    refine ⟨8639750736572900294690465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23039335297527734119174573 8639750736572900294690465)
    ·
      refine ⟨6479813052429675221017849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8639750736572900294690465 6479813052429675221017849)
      ·
        refine ⟨4859859789322256415763387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479813052429675221017849 4859859789322256415763387)
        ·
          refine ⟨7289789683983384623645081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859859789322256415763387 7289789683983384623645081)
          ·
            refine ⟨5467342262987538467733811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7289789683983384623645081 5467342262987538467733811)
            ·
              refine ⟨8201013394481307701600717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467342262987538467733811 8201013394481307701600717)
              ·
                refine ⟨3075380022930490388100269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8201013394481307701600717 3075380022930490388100269)
                ·
                  refine ⟨1153267508598933895537601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3075380022930490388100269 1153267508598933895537601)
                  ·
                    refine ⟨864950631449200421653201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153267508598933895537601 864950631449200421653201)
                    ·
                      refine ⟨648712973586900316239901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 864950631449200421653201 648712973586900316239901)
                      ·
                        rfl

theorem cell23_1263364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_1263364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263364 prefixEnd_1263364 := by exact prefixLift 1263364
  have htrace : WordTrace (prefixWord ++ tailWord_1263364) baseStart_1263364 baseEnd_1263364 := by
    simpa [prefixWord, tailWord_1263364, baseEnd_1263364] using wordTrace_append hprefix tailTrace_1263364
  have hstable : (prefixWord ++ tailWord_1263364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263364).length < 2 ^ (prefixWord ++ tailWord_1263364).sum := by decide
  have hdescent : baseEnd_1263364 < baseStart_1263364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263367 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1263367 : Nat := 118140960795 + 1263367 * 2 ^ 59
def prefixEnd_1263367 : Nat := 4983230072969 + 3 ^ 40 * 1263367 * 2
def baseEnd_1263367 : Nat := 648714514028863804502387

theorem tailTrace_1263367 : CollatzResearch.WordTrace tailWord_1263367 prefixEnd_1263367 648714514028863804502387 := by
  unfold tailWord_1263367
  simp only [CollatzResearch.WordTrace]
  refine ⟨46078780014044599750708355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30719186676029733167138903 46078780014044599750708355)
  ·
    refine ⟨69118170021066899626062533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46078780014044599750708355 69118170021066899626062533)
    ·
      refine ⟨12959656878950043679886725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69118170021066899626062533 12959656878950043679886725)
      ·
        refine ⟨2429935664803133189978761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12959656878950043679886725 2429935664803133189978761)
        ·
          refine ⟨1822451748602349892484071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429935664803133189978761 1822451748602349892484071)
          ·
            refine ⟨2733677622903524838726107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822451748602349892484071 2733677622903524838726107)
            ·
              refine ⟨4100516434355287258089161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733677622903524838726107 4100516434355287258089161)
              ·
                refine ⟨3075387325766465443566871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100516434355287258089161 3075387325766465443566871)
                ·
                  refine ⟨4613080988649698165350307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075387325766465443566871 4613080988649698165350307)
                  ·
                    refine ⟨6919621482974547248025461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613080988649698165350307 6919621482974547248025461)
                    ·
                      refine ⟨648714514028863804502387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6919621482974547248025461 648714514028863804502387)
                      ·
                        rfl

theorem cell23_1263367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1263367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263367 prefixEnd_1263367 := by exact prefixLift 1263367
  have htrace : WordTrace (prefixWord ++ tailWord_1263367) baseStart_1263367 baseEnd_1263367 := by
    simpa [prefixWord, tailWord_1263367, baseEnd_1263367] using wordTrace_append hprefix tailTrace_1263367
  have hstable : (prefixWord ++ tailWord_1263367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263367).length < 2 ^ (prefixWord ++ tailWord_1263367).sum := by decide
  have hdescent : baseEnd_1263367 < baseStart_1263367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263397 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_1263397 : Nat := 118140960795 + 1263397 * 2 ^ 59
def prefixEnd_1263397 : Nat := 4983230072969 + 3 ^ 40 * 1263397 * 2
def baseEnd_1263397 : Nat := 648729918448498687127249

theorem tailTrace_1263397 : CollatzResearch.WordTrace tailWord_1263397 prefixEnd_1263397 648729918448498687127249 := by
  unfold tailWord_1263397
  simp only [CollatzResearch.WordTrace]
  refine ⟨46079874203935914874300445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30719916135957276582866963 46079874203935914874300445)
  ·
    refine ⟨17279952826475968077862667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46079874203935914874300445 17279952826475968077862667)
    ·
      refine ⟨25919929239713952116794001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17279952826475968077862667 25919929239713952116794001)
      ·
        refine ⟨19439946929785464087595501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25919929239713952116794001 19439946929785464087595501)
        ·
          refine ⟨7289980098669549032848313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19439946929785464087595501 7289980098669549032848313)
          ·
            refine ⟨5467485074002161774636235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7289980098669549032848313 5467485074002161774636235)
            ·
              refine ⟨8201227611003242661954353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467485074002161774636235 8201227611003242661954353)
              ·
                refine ⟨6150920708252431996465765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8201227611003242661954353 6150920708252431996465765)
                ·
                  refine ⟨1153297632797330999337331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6150920708252431996465765 1153297632797330999337331)
                  ·
                    refine ⟨1729946449195996499005997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153297632797330999337331 1729946449195996499005997)
                    ·
                      refine ⟨648729918448498687127249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1729946449195996499005997 648729918448498687127249)
                      ·
                        rfl

theorem cell23_1263397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_1263397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263397 prefixEnd_1263397 := by exact prefixLift 1263397
  have htrace : WordTrace (prefixWord ++ tailWord_1263397) baseStart_1263397 baseEnd_1263397 := by
    simpa [prefixWord, tailWord_1263397, baseEnd_1263397] using wordTrace_append hprefix tailTrace_1263397
  have hstable : (prefixWord ++ tailWord_1263397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263397).length < 2 ^ (prefixWord ++ tailWord_1263397).sum := by decide
  have hdescent : baseEnd_1263397 < baseStart_1263397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263441 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_1263441 : Nat := 118140960795 + 1263441 * 2 ^ 59
def prefixEnd_1263441 : Nat := 4983230072969 + 3 ^ 40 * 1263441 * 2
def baseEnd_1263441 : Nat := 648752511597296514977047

theorem tailTrace_1263441 : CollatzResearch.WordTrace tailWord_1263441 prefixEnd_1263441 648752511597296514977047 := by
  unfold tailWord_1263441
  simp only [CollatzResearch.WordTrace]
  refine ⟨46081479015776510388902177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30720986010517673592601451 46081479015776510388902177)
  ·
    refine ⟨34561109261832382791676633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46081479015776510388902177 34561109261832382791676633)
    ·
      refine ⟨25920831946374287093757475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34561109261832382791676633 25920831946374287093757475)
      ·
        refine ⟨38881247919561430640636213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25920831946374287093757475 38881247919561430640636213)
        ·
          refine ⟨3645116992458884122559645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38881247919561430640636213 3645116992458884122559645)
          ·
            refine ⟨1366918872172081545959867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3645116992458884122559645 1366918872172081545959867)
            ·
              refine ⟨2050378308258122318939801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366918872172081545959867 2050378308258122318939801)
              ·
                refine ⟨1537783731193591739204851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050378308258122318939801 1537783731193591739204851)
                ·
                  refine ⟨2306675596790387608807277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537783731193591739204851 2306675596790387608807277)
                  ·
                    refine ⟨865003348796395353302729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306675596790387608807277 865003348796395353302729)
                    ·
                      refine ⟨648752511597296514977047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865003348796395353302729 648752511597296514977047)
                      ·
                        rfl

theorem cell23_1263441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_1263441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263441 prefixEnd_1263441 := by exact prefixLift 1263441
  have htrace : WordTrace (prefixWord ++ tailWord_1263441) baseStart_1263441 baseEnd_1263441 := by
    simpa [prefixWord, tailWord_1263441, baseEnd_1263441] using wordTrace_append hprefix tailTrace_1263441
  have hstable : (prefixWord ++ tailWord_1263441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263441).length < 2 ^ (prefixWord ++ tailWord_1263441).sum := by decide
  have hdescent : baseEnd_1263441 < baseStart_1263441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263458 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1263458 : Nat := 118140960795 + 1263458 * 2 ^ 59
def prefixEnd_1263458 : Nat := 4983230072969 + 3 ^ 40 * 1263458 * 2
def baseEnd_1263458 : Nat := 648761240768422948464469

theorem tailTrace_1263458 : CollatzResearch.WordTrace tailWord_1263458 prefixEnd_1263458 648761240768422948464469 := by
  unfold tailWord_1263458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11520524764178730573067757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30721399371143281528180685 11520524764178730573067757)
  ·
    refine ⟨4320196786567023964900409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11520524764178730573067757 4320196786567023964900409)
    ·
      refine ⟨3240147589925267973675307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4320196786567023964900409 3240147589925267973675307)
      ·
        refine ⟨4860221384887901960512961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240147589925267973675307 4860221384887901960512961)
        ·
          refine ⟨3645166038665926470384721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860221384887901960512961 3645166038665926470384721)
          ·
            refine ⟨2733874528999444852788541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3645166038665926470384721 2733874528999444852788541)
            ·
              refine ⟨1025202948374791819795703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2733874528999444852788541 1025202948374791819795703)
              ·
                refine ⟨1537804422562187729693555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025202948374791819795703 1537804422562187729693555)
                ·
                  refine ⟨2306706633843281594540333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537804422562187729693555 2306706633843281594540333)
                  ·
                    refine ⟨865014987691230597952625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306706633843281594540333 865014987691230597952625)
                    ·
                      refine ⟨648761240768422948464469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865014987691230597952625 648761240768422948464469)
                      ·
                        rfl

theorem cell23_1263458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1263458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263458 prefixEnd_1263458 := by exact prefixLift 1263458
  have htrace : WordTrace (prefixWord ++ tailWord_1263458) baseStart_1263458 baseEnd_1263458 := by
    simpa [prefixWord, tailWord_1263458, baseEnd_1263458] using wordTrace_append hprefix tailTrace_1263458
  have hstable : (prefixWord ++ tailWord_1263458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263458).length < 2 ^ (prefixWord ++ tailWord_1263458).sum := by decide
  have hdescent : baseEnd_1263458 < baseStart_1263458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263497 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 5, 2]
def baseStart_1263497 : Nat := 118140960795 + 1263497 * 2 ^ 59
def prefixEnd_1263497 : Nat := 4983230072969 + 3 ^ 40 * 1263497 * 2
def baseEnd_1263497 : Nat := 648781266513948295876789

theorem tailTrace_1263497 : CollatzResearch.WordTrace tailWord_1263497 prefixEnd_1263497 648781266513948295876789 := by
  unfold tailWord_1263497
  simp only [CollatzResearch.WordTrace]
  refine ⟨46083521503573631952940745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30722347669049087968627163 46083521503573631952940745)
  ·
    refine ⟨34562641127680223964705559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46083521503573631952940745 34562641127680223964705559)
    ·
      refine ⟨51843961691520335947058339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34562641127680223964705559 51843961691520335947058339)
      ·
        refine ⟨77765942537280503920587509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51843961691520335947058339 77765942537280503920587509)
        ·
          refine ⟨7290557112870047242555079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77765942537280503920587509 7290557112870047242555079)
          ·
            refine ⟨10935835669305070863832619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7290557112870047242555079 10935835669305070863832619)
            ·
              refine ⟨16403753503957606295748929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10935835669305070863832619 16403753503957606295748929)
              ·
                refine ⟨12302815127968204721811697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16403753503957606295748929 12302815127968204721811697)
                ·
                  refine ⟨9227111345976153541358773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12302815127968204721811697 9227111345976153541358773)
                  ·
                    refine ⟨865041688685264394502385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9227111345976153541358773 865041688685264394502385)
                    ·
                      refine ⟨648781266513948295876789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865041688685264394502385 648781266513948295876789)
                      ·
                        rfl

theorem cell23_1263497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 5, 2].length) (baseStart_1263497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263497 prefixEnd_1263497 := by exact prefixLift 1263497
  have htrace : WordTrace (prefixWord ++ tailWord_1263497) baseStart_1263497 baseEnd_1263497 := by
    simpa [prefixWord, tailWord_1263497, baseEnd_1263497] using wordTrace_append hprefix tailTrace_1263497
  have hstable : (prefixWord ++ tailWord_1263497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263497).length < 2 ^ (prefixWord ++ tailWord_1263497).sum := by decide
  have hdescent : baseEnd_1263497 < baseStart_1263497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263581 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1263581 : Nat := 118140960795 + 1263581 * 2 ^ 59
def prefixEnd_1263581 : Nat := 4983230072969 + 3 ^ 40 * 1263581 * 2
def baseEnd_1263581 : Nat := 648824398888925967226403

theorem tailTrace_1263581 : CollatzResearch.WordTrace tailWord_1263581 prefixEnd_1263581 648824398888925967226403 := by
  unfold tailWord_1263581
  simp only [CollatzResearch.WordTrace]
  refine ⟨46086585235269314298998597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30724390156846209532665731 46086585235269314298998597)
  ·
    refine ⟨8641234731612996431062237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46086585235269314298998597 8641234731612996431062237)
    ·
      refine ⟨3240463024354873661648339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8641234731612996431062237 3240463024354873661648339)
      ·
        refine ⟨4860694536532310492472509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3240463024354873661648339 4860694536532310492472509)
        ·
          refine ⟨1822760451199616434677191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4860694536532310492472509 1822760451199616434677191)
          ·
            refine ⟨2734140676799424652015787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822760451199616434677191 2734140676799424652015787)
            ·
              refine ⟨4101211015199136978023681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734140676799424652015787 4101211015199136978023681)
              ·
                refine ⟨3075908261399352733517761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101211015199136978023681 3075908261399352733517761)
                ·
                  refine ⟨2306931196049514550138321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075908261399352733517761 2306931196049514550138321)
                  ·
                    refine ⟨1730198397037135912603741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2306931196049514550138321 1730198397037135912603741)
                    ·
                      refine ⟨648824398888925967226403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1730198397037135912603741 648824398888925967226403)
                      ·
                        rfl

theorem cell23_1263581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1263581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263581 prefixEnd_1263581 := by exact prefixLift 1263581
  have htrace : WordTrace (prefixWord ++ tailWord_1263581) baseStart_1263581 baseEnd_1263581 := by
    simpa [prefixWord, tailWord_1263581, baseEnd_1263581] using wordTrace_append hprefix tailTrace_1263581
  have hstable : (prefixWord ++ tailWord_1263581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263581).length < 2 ^ (prefixWord ++ tailWord_1263581).sum := by decide
  have hdescent : baseEnd_1263581 < baseStart_1263581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263601 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 6]
def baseStart_1263601 : Nat := 118140960795 + 1263601 * 2 ^ 59
def prefixEnd_1263601 : Nat := 4983230072969 + 3 ^ 40 * 1263601 * 2
def baseEnd_1263601 : Nat := 72092740944668432108479

theorem tailTrace_1263601 : CollatzResearch.WordTrace tailWord_1263601 prefixEnd_1263601 72092740944668432108479 := by
  unfold tailWord_1263601
  simp only [CollatzResearch.WordTrace]
  refine ⟨46087314695196857714726657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30724876463464571809817771 46087314695196857714726657)
  ·
    refine ⟨34565486021397643286044993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46087314695196857714726657 34565486021397643286044993)
    ·
      refine ⟨25924114516048232464533745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34565486021397643286044993 25924114516048232464533745)
      ·
        refine ⟨19443085887036174348400309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25924114516048232464533745 19443085887036174348400309)
        ·
          refine ⟨1822789301909641345162529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19443085887036174348400309 1822789301909641345162529)
          ·
            refine ⟨1367091976432231008871897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1822789301909641345162529 1367091976432231008871897)
            ·
              refine ⟨1025318982324173256653923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1367091976432231008871897 1025318982324173256653923)
              ·
                refine ⟨1537978473486259884980885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025318982324173256653923 1537978473486259884980885)
                ·
                  refine ⟨72092740944668432108479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1537978473486259884980885 72092740944668432108479)
                  ·
                    rfl

theorem cell23_1263601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_1263601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263601 prefixEnd_1263601 := by exact prefixLift 1263601
  have htrace : WordTrace (prefixWord ++ tailWord_1263601) baseStart_1263601 baseEnd_1263601 := by
    simpa [prefixWord, tailWord_1263601, baseEnd_1263601] using wordTrace_append hprefix tailTrace_1263601
  have hstable : (prefixWord ++ tailWord_1263601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263601).length < 2 ^ (prefixWord ++ tailWord_1263601).sum := by decide
  have hdescent : baseEnd_1263601 < baseStart_1263601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263621 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_1263621 : Nat := 118140960795 + 1263621 * 2 ^ 59
def prefixEnd_1263621 : Nat := 4983230072969 + 3 ^ 40 * 1263621 * 2
def baseEnd_1263621 : Nat := 648844938115105810726219

theorem tailTrace_1263621 : CollatzResearch.WordTrace tailWord_1263621 prefixEnd_1263621 648844938115105810726219 := by
  unfold tailWord_1263621
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088044155124401130454717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725362770082934086969811 46088044155124401130454717)
  ·
    refine ⟨17283016558171650423920519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46088044155124401130454717 17283016558171650423920519)
    ·
      refine ⟨25924524837257475635880779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17283016558171650423920519 25924524837257475635880779)
      ·
        refine ⟨38886787255886213453821169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25924524837257475635880779 38886787255886213453821169)
        ·
          refine ⟨29165090441914660090365877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38886787255886213453821169 29165090441914660090365877)
          ·
            refine ⟨2734227228929499383471801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29165090441914660090365877 2734227228929499383471801)
            ·
              refine ⟨2050670421697124537603851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734227228929499383471801 2050670421697124537603851)
              ·
                refine ⟨3076005632545686806405777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050670421697124537603851 3076005632545686806405777)
                ·
                  refine ⟨2307004224409265104804333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3076005632545686806405777 2307004224409265104804333)
                  ·
                    refine ⟨865126584153474414301625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307004224409265104804333 865126584153474414301625)
                    ·
                      refine ⟨648844938115105810726219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865126584153474414301625 648844938115105810726219)
                      ·
                        rfl

theorem cell23_1263621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_1263621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263621 prefixEnd_1263621 := by exact prefixLift 1263621
  have htrace : WordTrace (prefixWord ++ tailWord_1263621) baseStart_1263621 baseEnd_1263621 := by
    simpa [prefixWord, tailWord_1263621, baseEnd_1263621] using wordTrace_append hprefix tailTrace_1263621
  have hstable : (prefixWord ++ tailWord_1263621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263621).length < 2 ^ (prefixWord ++ tailWord_1263621).sum := by decide
  have hdescent : baseEnd_1263621 < baseStart_1263621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263627 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 6]
def baseStart_1263627 : Nat := 118140960795 + 1263627 * 2 ^ 59
def prefixEnd_1263627 : Nat := 4983230072969 + 3 ^ 40 * 1263627 * 2
def baseEnd_1263627 : Nat := 216282672999677595750397

theorem tailTrace_1263627 : CollatzResearch.WordTrace tailWord_1263627 prefixEnd_1263627 216282672999677595750397 := by
  unfold tailWord_1263627
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088262993102664155173135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725508662068442770115423 46088262993102664155173135)
  ·
    refine ⟨69132394489653996232759703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088262993102664155173135 69132394489653996232759703)
    ·
      refine ⟨103698591734480994349139555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69132394489653996232759703 103698591734480994349139555)
      ·
        refine ⟨155547887601721491523709333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103698591734480994349139555 155547887601721491523709333)
        ·
          refine ⟨7291307231330694915173875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155547887601721491523709333 7291307231330694915173875)
          ·
            refine ⟨10936960846996042372760813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291307231330694915173875 10936960846996042372760813)
            ·
              refine ⟨4101360317623515889785305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10936960846996042372760813 4101360317623515889785305)
              ·
                refine ⟨3076020238217636917338979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101360317623515889785305 3076020238217636917338979)
                ·
                  refine ⟨4614030357326455376008469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076020238217636917338979 4614030357326455376008469)
                  ·
                    refine ⟨216282672999677595750397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4614030357326455376008469 216282672999677595750397)
                    ·
                      rfl

theorem cell23_1263627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 6].length) (baseStart_1263627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263627 prefixEnd_1263627 := by exact prefixLift 1263627
  have htrace : WordTrace (prefixWord ++ tailWord_1263627) baseStart_1263627 baseEnd_1263627 := by
    simpa [prefixWord, tailWord_1263627, baseEnd_1263627] using wordTrace_append hprefix tailTrace_1263627
  have hstable : (prefixWord ++ tailWord_1263627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263627).length < 2 ^ (prefixWord ++ tailWord_1263627).sum := by decide
  have hdescent : baseEnd_1263627 < baseStart_1263627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263645 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_1263645 : Nat := 118140960795 + 1263645 * 2 ^ 59
def prefixEnd_1263645 : Nat := 4983230072969 + 3 ^ 40 * 1263645 * 2
def baseEnd_1263645 : Nat := 648857261650813716826109

theorem tailTrace_1263645 : CollatzResearch.WordTrace tailWord_1263645 prefixEnd_1263645 648857261650813716826109 := by
  unfold tailWord_1263645
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088919507037453229328389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725946338024968819552259 46088919507037453229328389)
  ·
    refine ⟨8641672407569522480499073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46088919507037453229328389 8641672407569522480499073)
    ·
      refine ⟨6481254305677141860374305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8641672407569522480499073 6481254305677141860374305)
      ·
        refine ⟨4860940729257856395280729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6481254305677141860374305 4860940729257856395280729)
        ·
          refine ⟨3645705546943392296460547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4860940729257856395280729 3645705546943392296460547)
          ·
            refine ⟨5468558320415088444690821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645705546943392296460547 5468558320415088444690821)
            ·
              refine ⟨1025354685077829083379529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5468558320415088444690821 1025354685077829083379529)
              ·
                refine ⟨769016013808371812534647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025354685077829083379529 769016013808371812534647)
                ·
                  refine ⟨1153524020712557718801971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769016013808371812534647 1153524020712557718801971)
                  ·
                    refine ⟨1730286031068836578202957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153524020712557718801971 1730286031068836578202957)
                    ·
                      refine ⟨648857261650813716826109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1730286031068836578202957 648857261650813716826109)
                      ·
                        rfl

theorem cell23_1263645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_1263645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263645 prefixEnd_1263645 := by exact prefixLift 1263645
  have htrace : WordTrace (prefixWord ++ tailWord_1263645) baseStart_1263645 baseEnd_1263645 := by
    simpa [prefixWord, tailWord_1263645, baseEnd_1263645] using wordTrace_append hprefix tailTrace_1263645
  have hstable : (prefixWord ++ tailWord_1263645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263645).length < 2 ^ (prefixWord ++ tailWord_1263645).sum := by decide
  have hdescent : baseEnd_1263645 < baseStart_1263645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263647 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1263647 : Nat := 118140960795 + 1263647 * 2 ^ 59
def prefixEnd_1263647 : Nat := 4983230072969 + 3 ^ 40 * 1263647 * 2
def baseEnd_1263647 : Nat := 648858288612122709001099

theorem tailTrace_1263647 : CollatzResearch.WordTrace tailWord_1263647 prefixEnd_1263647 648858288612122709001099 := by
  unfold tailWord_1263647
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088992453030207570901195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30725994968686805047267463 46088992453030207570901195)
  ·
    refine ⟨69133488679545311356351793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088992453030207570901195 69133488679545311356351793)
    ·
      refine ⟨51850116509658983517263845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69133488679545311356351793 51850116509658983517263845)
      ·
        refine ⟨9721896845561059409486971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51850116509658983517263845 9721896845561059409486971)
        ·
          refine ⟨14582845268341589114230457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9721896845561059409486971 14582845268341589114230457)
          ·
            refine ⟨10937133951256191835672843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14582845268341589114230457 10937133951256191835672843)
            ·
              refine ⟨16405700926884287753509265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937133951256191835672843 16405700926884287753509265)
              ·
                refine ⟨12304275695163215815131949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16405700926884287753509265 12304275695163215815131949)
                ·
                  refine ⟨4614103385686205930674481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12304275695163215815131949 4614103385686205930674481)
                  ·
                    refine ⟨3460577539264654448005861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614103385686205930674481 3460577539264654448005861)
                    ·
                      refine ⟨648858288612122709001099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3460577539264654448005861 648858288612122709001099)
                      ·
                        rfl

theorem cell23_1263647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1263647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263647 prefixEnd_1263647 := by exact prefixLift 1263647
  have htrace : WordTrace (prefixWord ++ tailWord_1263647) baseStart_1263647 baseEnd_1263647 := by
    simpa [prefixWord, tailWord_1263647, baseEnd_1263647] using wordTrace_append hprefix tailTrace_1263647
  have hstable : (prefixWord ++ tailWord_1263647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263647).length < 2 ^ (prefixWord ++ tailWord_1263647).sum := by decide
  have hdescent : baseEnd_1263647 < baseStart_1263647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263651 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 3, 2, 2]
def baseStart_1263651 : Nat := 118140960795 + 1263651 * 2 ^ 59
def prefixEnd_1263651 : Nat := 4983230072969 + 3 ^ 40 * 1263651 * 2
def baseEnd_1263651 : Nat := 648860342534740693351081

theorem tailTrace_1263651 : CollatzResearch.WordTrace tailWord_1263651 prefixEnd_1263651 648860342534740693351081 := by
  unfold tailWord_1263651
  simp only [CollatzResearch.WordTrace]
  refine ⟨46089138345015716254046807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30726092230010477502697871 46089138345015716254046807)
  ·
    refine ⟨69133707517523574381070211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46089138345015716254046807 69133707517523574381070211)
    ·
      refine ⟨103700561276285361571605317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69133707517523574381070211 103700561276285361571605317)
      ·
        refine ⟨19443855239303505294675997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103700561276285361571605317 19443855239303505294675997)
        ·
          refine ⟨7291445714738814485503499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19443855239303505294675997 7291445714738814485503499)
          ·
            refine ⟨10937168572108221728255249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291445714738814485503499 10937168572108221728255249)
            ·
              refine ⟨8202876429081166296191437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10937168572108221728255249 8202876429081166296191437)
              ·
                refine ⟨3076078660905437361071789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8202876429081166296191437 3076078660905437361071789)
                ·
                  refine ⟨1153529497839539010401921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3076078660905437361071789 1153529497839539010401921)
                  ·
                    refine ⟨865147123379654257801441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153529497839539010401921 865147123379654257801441)
                    ·
                      refine ⟨648860342534740693351081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865147123379654257801441 648860342534740693351081)
                      ·
                        rfl

theorem cell23_1263651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_1263651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263651 prefixEnd_1263651 := by exact prefixLift 1263651
  have htrace : WordTrace (prefixWord ++ tailWord_1263651) baseStart_1263651 baseEnd_1263651 := by
    simpa [prefixWord, tailWord_1263651, baseEnd_1263651] using wordTrace_append hprefix tailTrace_1263651
  have hstable : (prefixWord ++ tailWord_1263651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263651).length < 2 ^ (prefixWord ++ tailWord_1263651).sum := by decide
  have hdescent : baseEnd_1263651 < baseStart_1263651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263664 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_1263664 : Nat := 118140960795 + 1263664 * 2 ^ 59
def prefixEnd_1263664 : Nat := 4983230072969 + 3 ^ 40 * 1263664 * 2
def baseEnd_1263664 : Nat := 648867017783249142488521

theorem tailTrace_1263664 : CollatzResearch.WordTrace tailWord_1263664 prefixEnd_1263664 648867017783249142488521 := by
  unfold tailWord_1263664
  simp only [CollatzResearch.WordTrace]
  refine ⟨23044806246984309737135023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30726408329312412982846697 23044806246984309737135023)
  ·
    refine ⟨34567209370476464605702535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23044806246984309737135023 34567209370476464605702535)
    ·
      refine ⟨51850814055714696908553803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34567209370476464605702535 51850814055714696908553803)
      ·
        refine ⟨77776221083572045362830705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51850814055714696908553803 77776221083572045362830705)
        ·
          refine ⟨58332165812679034022123029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77776221083572045362830705 58332165812679034022123029)
          ·
            refine ⟨2734320272469329719787017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58332165812679034022123029 2734320272469329719787017)
            ·
              refine ⟨2050740204351997289840263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734320272469329719787017 2050740204351997289840263)
              ·
                refine ⟨3076110306527995934760395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050740204351997289840263 3076110306527995934760395)
                ·
                  refine ⟨4614165459791993902140593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076110306527995934760395 4614165459791993902140593)
                  ·
                    refine ⟨3460624094843995426605445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614165459791993902140593 3460624094843995426605445)
                    ·
                      refine ⟨648867017783249142488521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3460624094843995426605445 648867017783249142488521)
                      ·
                        rfl

theorem cell23_1263664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_1263664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263664 prefixEnd_1263664 := by exact prefixLift 1263664
  have htrace : WordTrace (prefixWord ++ tailWord_1263664) baseStart_1263664 baseEnd_1263664 := by
    simpa [prefixWord, tailWord_1263664, baseEnd_1263664] using wordTrace_append hprefix tailTrace_1263664
  have hstable : (prefixWord ++ tailWord_1263664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263664).length < 2 ^ (prefixWord ++ tailWord_1263664).sum := by decide
  have hdescent : baseEnd_1263664 < baseStart_1263664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263701 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1263701 : Nat := 118140960795 + 1263701 * 2 ^ 59
def prefixEnd_1263701 : Nat := 4983230072969 + 3 ^ 40 * 1263701 * 2
def baseEnd_1263701 : Nat := 648886016567465497725851

theorem tailTrace_1263701 : CollatzResearch.WordTrace tailWord_1263701 prefixEnd_1263701 648886016567465497725851 := by
  unfold tailWord_1263701
  simp only [CollatzResearch.WordTrace]
  refine ⟨46090961994834574793366957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30727307996556383195577971 46090961994834574793366957)
  ·
    refine ⟨17284110748062965547512609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46090961994834574793366957 17284110748062965547512609)
    ·
      refine ⟨12963083061047224160634457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17284110748062965547512609 12963083061047224160634457)
      ·
        refine ⟨9722312295785418120475843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12963083061047224160634457 9722312295785418120475843)
        ·
          refine ⟨14583468443678127180713765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9722312295785418120475843 14583468443678127180713765)
          ·
            refine ⟨2734400333189648846383831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14583468443678127180713765 2734400333189648846383831)
            ·
              refine ⟨4101600499784473269575747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734400333189648846383831 4101600499784473269575747)
              ·
                refine ⟨6152400749676709904363621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101600499784473269575747 6152400749676709904363621)
                ·
                  refine ⟨1153575140564383107068179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6152400749676709904363621 1153575140564383107068179)
                  ·
                    refine ⟨1730362710846574660602269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153575140564383107068179 1730362710846574660602269)
                    ·
                      refine ⟨648886016567465497725851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1730362710846574660602269 648886016567465497725851)
                      ·
                        rfl

theorem cell23_1263701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1263701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263701 prefixEnd_1263701 := by exact prefixLift 1263701
  have htrace : WordTrace (prefixWord ++ tailWord_1263701) baseStart_1263701 baseEnd_1263701 := by
    simpa [prefixWord, tailWord_1263701, baseEnd_1263701] using wordTrace_append hprefix tailTrace_1263701
  have hstable : (prefixWord ++ tailWord_1263701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263701).length < 2 ^ (prefixWord ++ tailWord_1263701).sum := by decide
  have hdescent : baseEnd_1263701 < baseStart_1263701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263702 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1263702 : Nat := 118140960795 + 1263702 * 2 ^ 59
def prefixEnd_1263702 : Nat := 4983230072969 + 3 ^ 40 * 1263702 * 2
def baseEnd_1263702 : Nat := 648886530048119993813347

theorem tailTrace_1263702 : CollatzResearch.WordTrace tailWord_1263702 prefixEnd_1263702 648886530048119993813347 := by
  unfold tailWord_1263702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880687404239434497759585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30727332311887301309435573 2880687404239434497759585)
  ·
    refine ⟨2160515553179575873319689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2880687404239434497759585 2160515553179575873319689)
    ·
      refine ⟨1620386664884681904989767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2160515553179575873319689 1620386664884681904989767)
      ·
        refine ⟨2430579997327022857484651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620386664884681904989767 2430579997327022857484651)
        ·
          refine ⟨3645869995990534286226977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430579997327022857484651 3645869995990534286226977)
          ·
            refine ⟨2734402496992900714670233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3645869995990534286226977 2734402496992900714670233)
            ·
              refine ⟨2050801872744675536002675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734402496992900714670233 2050801872744675536002675)
              ·
                refine ⟨3076202809117013304004013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050801872744675536002675 3076202809117013304004013)
                ·
                  refine ⟨1153576053418879989001505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3076202809117013304004013 1153576053418879989001505)
                  ·
                    refine ⟨865182040064159991751129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153576053418879989001505 865182040064159991751129)
                    ·
                      refine ⟨648886530048119993813347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865182040064159991751129 648886530048119993813347)
                      ·
                        rfl

theorem cell23_1263702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1263702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263702 prefixEnd_1263702 := by exact prefixLift 1263702
  have htrace : WordTrace (prefixWord ++ tailWord_1263702) baseStart_1263702 baseEnd_1263702 := by
    simpa [prefixWord, tailWord_1263702, baseEnd_1263702] using wordTrace_append hprefix tailTrace_1263702
  have hstable : (prefixWord ++ tailWord_1263702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263702).length < 2 ^ (prefixWord ++ tailWord_1263702).sum := by decide
  have hdescent : baseEnd_1263702 < baseStart_1263702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263728 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2]
def baseStart_1263728 : Nat := 118140960795 + 1263728 * 2 ^ 59
def prefixEnd_1263728 : Nat := 4983230072969 + 3 ^ 40 * 1263728 * 2
def baseEnd_1263728 : Nat := 648899880545136892088227

theorem tailTrace_1263728 : CollatzResearch.WordTrace tailWord_1263728 prefixEnd_1263728 648899880545136892088227 := by
  unfold tailWord_1263728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23045973382868379202299919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30727964510491172269733225 23045973382868379202299919)
  ·
    refine ⟨34568960074302568803449879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23045973382868379202299919 34568960074302568803449879)
    ·
      refine ⟨51853440111453853205174819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34568960074302568803449879 51853440111453853205174819)
      ·
        refine ⟨77780160167180779807762229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51853440111453853205174819 77780160167180779807762229)
        ·
          refine ⟨7291890015673198106977709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77780160167180779807762229 7291890015673198106977709)
          ·
            refine ⟨2734458755877449290116641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7291890015673198106977709 2734458755877449290116641)
            ·
              refine ⟨2050844066908086967587481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2734458755877449290116641 2050844066908086967587481)
              ·
                refine ⟨1538133050181065225690611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050844066908086967587481 1538133050181065225690611)
                ·
                  refine ⟨2307199575271597838535917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538133050181065225690611 2307199575271597838535917)
                  ·
                    refine ⟨865199840726849189450969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307199575271597838535917 865199840726849189450969)
                    ·
                      refine ⟨648899880545136892088227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865199840726849189450969 648899880545136892088227)
                      ·
                        rfl

theorem cell23_1263728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2].length) (baseStart_1263728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263728 prefixEnd_1263728 := by exact prefixLift 1263728
  have htrace : WordTrace (prefixWord ++ tailWord_1263728) baseStart_1263728 baseEnd_1263728 := by
    simpa [prefixWord, tailWord_1263728, baseEnd_1263728] using wordTrace_append hprefix tailTrace_1263728
  have hstable : (prefixWord ++ tailWord_1263728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263728).length < 2 ^ (prefixWord ++ tailWord_1263728).sum := by decide
  have hdescent : baseEnd_1263728 < baseStart_1263728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263775 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1263775 : Nat := 118140960795 + 1263775 * 2 ^ 59
def prefixEnd_1263775 : Nat := 4983230072969 + 3 ^ 40 * 1263775 * 2
def baseEnd_1263775 : Nat := 648924014135898208200511

theorem tailTrace_1263775 : CollatzResearch.WordTrace tailWord_1263775 prefixEnd_1263775 648924014135898208200511 := by
  unfold tailWord_1263775
  simp only [CollatzResearch.WordTrace]
  refine ⟨46093660996566485431560779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30729107331044323621040519 46093660996566485431560779)
  ·
    refine ⟨69140491494849728147341169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46093660996566485431560779 69140491494849728147341169)
    ·
      refine ⟨51855368621137296110505877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69140491494849728147341169 51855368621137296110505877)
      ·
        refine ⟨2430720404115810755179963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51855368621137296110505877 2430720404115810755179963)
        ·
          refine ⟨3646080606173716132769945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430720404115810755179963 3646080606173716132769945)
          ·
            refine ⟨2734560454630287099577459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646080606173716132769945 2734560454630287099577459)
            ·
              refine ⟨4101840681945430649366189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734560454630287099577459 4101840681945430649366189)
              ·
                refine ⟨1538190255729536493512321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4101840681945430649366189 1538190255729536493512321)
                ·
                  refine ⟨1153642691797152370134241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538190255729536493512321 1153642691797152370134241)
                  ·
                    refine ⟨865232018847864277600681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153642691797152370134241 865232018847864277600681)
                    ·
                      refine ⟨648924014135898208200511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865232018847864277600681 648924014135898208200511)
                      ·
                        rfl

theorem cell23_1263775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1263775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263775 prefixEnd_1263775 := by exact prefixLift 1263775
  have htrace : WordTrace (prefixWord ++ tailWord_1263775) baseStart_1263775 baseEnd_1263775 := by
    simpa [prefixWord, tailWord_1263775, baseEnd_1263775] using wordTrace_append hprefix tailTrace_1263775
  have hstable : (prefixWord ++ tailWord_1263775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263775).length < 2 ^ (prefixWord ++ tailWord_1263775).sum := by decide
  have hdescent : baseEnd_1263775 < baseStart_1263775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263796 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1263796 : Nat := 118140960795 + 1263796 * 2 ^ 59
def prefixEnd_1263796 : Nat := 4983230072969 + 3 ^ 40 * 1263796 * 2
def baseEnd_1263796 : Nat := 648934797229642626037915

theorem tailTrace_1263796 : CollatzResearch.WordTrace tailWord_1263796 prefixEnd_1263796 648934797229642626037915 := by
  unfold tailWord_1263796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047213464745203009037621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30729617952993604012050161 23047213464745203009037621)
  ·
    refine ⟨2160676262319862782097277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23047213464745203009037621 2160676262319862782097277)
    ·
      refine ⟨810253598369948543286479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2160676262319862782097277 810253598369948543286479)
      ·
        refine ⟨1215380397554922814929719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810253598369948543286479 1215380397554922814929719)
        ·
          refine ⟨1823070596332384222394579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215380397554922814929719 1823070596332384222394579)
          ·
            refine ⟨2734605894498576333591869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823070596332384222394579 2734605894498576333591869)
            ·
              refine ⟨1025477210436966125096951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2734605894498576333591869 1025477210436966125096951)
              ·
                refine ⟨1538215815655449187645427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025477210436966125096951 1538215815655449187645427)
                ·
                  refine ⟨2307323723483173781468141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538215815655449187645427 2307323723483173781468141)
                  ·
                    refine ⟨865246396306190168050553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307323723483173781468141 865246396306190168050553)
                    ·
                      refine ⟨648934797229642626037915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865246396306190168050553 648934797229642626037915)
                      ·
                        rfl

theorem cell23_1263796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1263796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263796 prefixEnd_1263796 := by exact prefixLift 1263796
  have htrace : WordTrace (prefixWord ++ tailWord_1263796) baseStart_1263796 baseEnd_1263796 := by
    simpa [prefixWord, tailWord_1263796, baseEnd_1263796] using wordTrace_append hprefix tailTrace_1263796
  have hstable : (prefixWord ++ tailWord_1263796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263796).length < 2 ^ (prefixWord ++ tailWord_1263796).sum := by decide
  have hdescent : baseEnd_1263796 < baseStart_1263796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263824 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_1263824 : Nat := 118140960795 + 1263824 * 2 ^ 59
def prefixEnd_1263824 : Nat := 4983230072969 + 3 ^ 40 * 1263824 * 2
def baseEnd_1263824 : Nat := 216316391562656172162595

theorem tailTrace_1263824 : CollatzResearch.WordTrace tailWord_1263824 prefixEnd_1263824 216316391562656172162595 := by
  unfold tailWord_1263824
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047724086694483400047263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30730298782259311200063017 23047724086694483400047263)
  ·
    refine ⟨34571586130041725100070895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23047724086694483400047263 34571586130041725100070895)
    ·
      refine ⟨51857379195062587650106343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34571586130041725100070895 51857379195062587650106343)
      ·
        refine ⟨77786068792593881475159515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51857379195062587650106343 77786068792593881475159515)
        ·
          refine ⟨116679103188890822212739273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77786068792593881475159515 116679103188890822212739273)
          ·
            refine ⟨87509327391668116659554455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116679103188890822212739273 87509327391668116659554455)
            ·
              refine ⟨131263991087502174989331683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87509327391668116659554455 131263991087502174989331683)
              ·
                refine ⟨196895986631253262483997525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131263991087502174989331683 196895986631253262483997525)
                ·
                  refine ⟨1153687421667499584867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 196895986631253262483997525 1153687421667499584867173)
                  ·
                    refine ⟨216316391562656172162595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153687421667499584867173 216316391562656172162595)
                    ·
                      rfl

theorem cell23_1263824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_1263824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263824 prefixEnd_1263824 := by exact prefixLift 1263824
  have htrace : WordTrace (prefixWord ++ tailWord_1263824) baseStart_1263824 baseEnd_1263824 := by
    simpa [prefixWord, tailWord_1263824, baseEnd_1263824] using wordTrace_append hprefix tailTrace_1263824
  have hstable : (prefixWord ++ tailWord_1263824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263824).length < 2 ^ (prefixWord ++ tailWord_1263824).sum := by decide
  have hdescent : baseEnd_1263824 < baseStart_1263824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263841 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1263841 : Nat := 118140960795 + 1263841 * 2 ^ 59
def prefixEnd_1263841 : Nat := 4983230072969 + 3 ^ 40 * 1263841 * 2
def baseEnd_1263841 : Nat := 216319301286364983325069

theorem tailTrace_1263841 : CollatzResearch.WordTrace tailWord_1263841 prefixEnd_1263841 216319301286364983325069 := by
  unfold tailWord_1263841
  simp only [CollatzResearch.WordTrace]
  refine ⟨46096068214327378703463377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30730712142884919135642251 46096068214327378703463377)
  ·
    refine ⟨34572051160745534027597533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46096068214327378703463377 34572051160745534027597533)
    ·
      refine ⟨12964519185279575260349075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34572051160745534027597533 12964519185279575260349075)
      ·
        refine ⟨19446778777919362890523613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12964519185279575260349075 19446778777919362890523613)
        ·
          refine ⟨7292542041719761083946355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19446778777919362890523613 7292542041719761083946355)
          ·
            refine ⟨10938813062579641625919533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7292542041719761083946355 10938813062579641625919533)
            ·
              refine ⟨4102054898467365609719825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10938813062579641625919533 4102054898467365609719825)
              ·
                refine ⟨3076541173850524207289869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102054898467365609719825 3076541173850524207289869)
                ·
                  refine ⟨1153702940193946577733701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3076541173850524207289869 1153702940193946577733701)
                  ·
                    refine ⟨216319301286364983325069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153702940193946577733701 216319301286364983325069)
                    ·
                      rfl

theorem cell23_1263841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1263841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263841 prefixEnd_1263841 := by exact prefixLift 1263841
  have htrace : WordTrace (prefixWord ++ tailWord_1263841) baseStart_1263841 baseEnd_1263841 := by
    simpa [prefixWord, tailWord_1263841, baseEnd_1263841] using wordTrace_append hprefix tailTrace_1263841
  have hstable : (prefixWord ++ tailWord_1263841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263841).length < 2 ^ (prefixWord ++ tailWord_1263841).sum := by decide
  have hdescent : baseEnd_1263841 < baseStart_1263841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263848 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1263848 : Nat := 118140960795 + 1263848 * 2 ^ 59
def prefixEnd_1263848 : Nat := 4983230072969 + 3 ^ 40 * 1263848 * 2
def baseEnd_1263848 : Nat := 648961498223676422587675

theorem tailTrace_1263848 : CollatzResearch.WordTrace tailWord_1263848 prefixEnd_1263848 648961498223676422587675 := by
  unfold tailWord_1263848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23048161762651009449484099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30730882350201345932645465 23048161762651009449484099)
  ·
    refine ⟨34572242643976514174226149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23048161762651009449484099 34572242643976514174226149)
    ·
      refine ⟨6482295495745596407667403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34572242643976514174226149 6482295495745596407667403)
      ·
        refine ⟨9723443243618394611501105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482295495745596407667403 9723443243618394611501105)
        ·
          refine ⟨7292582432713795958625829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9723443243618394611501105 7292582432713795958625829)
          ·
            refine ⟨1367359206133836742242343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7292582432713795958625829 1367359206133836742242343)
            ·
              refine ⟨2051038809200755113363515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367359206133836742242343 2051038809200755113363515)
              ·
                refine ⟨3076558213801132670045273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051038809200755113363515 3076558213801132670045273)
                ·
                  refine ⟨2307418660350849502533955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3076558213801132670045273 2307418660350849502533955)
                  ·
                    refine ⟨3461127990526274253800933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2307418660350849502533955 3461127990526274253800933)
                    ·
                      refine ⟨648961498223676422587675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3461127990526274253800933 648961498223676422587675)
                      ·
                        rfl

theorem cell23_1263848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1263848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263848 prefixEnd_1263848 := by exact prefixLift 1263848
  have htrace : WordTrace (prefixWord ++ tailWord_1263848) baseStart_1263848 baseEnd_1263848 := by
    simpa [prefixWord, tailWord_1263848, baseEnd_1263848] using wordTrace_append hprefix tailTrace_1263848
  have hstable : (prefixWord ++ tailWord_1263848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263848).length < 2 ^ (prefixWord ++ tailWord_1263848).sum := by decide
  have hdescent : baseEnd_1263848 < baseStart_1263848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263854 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_1263854 : Nat := 118140960795 + 1263854 * 2 ^ 59
def prefixEnd_1263854 : Nat := 4983230072969 + 3 ^ 40 * 1263854 * 2
def baseEnd_1263854 : Nat := 72107175456400377679183

theorem tailTrace_1263854 : CollatzResearch.WordTrace tailWord_1263854 prefixEnd_1263854 72107175456400377679183 := by
  unfold tailWord_1263854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762067795410035240460827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30731028242186854615791077 5762067795410035240460827)
  ·
    refine ⟨8643101693115052860691241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762067795410035240460827 8643101693115052860691241)
    ·
      refine ⟨6482326269836289645518431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643101693115052860691241 6482326269836289645518431)
      ·
        refine ⟨9723489404754434468277647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482326269836289645518431 9723489404754434468277647)
        ·
          refine ⟨14585234107131651702416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723489404754434468277647 14585234107131651702416471)
          ·
            refine ⟨21877851160697477553624707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585234107131651702416471 21877851160697477553624707)
            ·
              refine ⟨32816776741046216330437061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21877851160697477553624707 32816776741046216330437061)
              ·
                refine ⟨6153145638946165561956949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32816776741046216330437061 6153145638946165561956949)
                ·
                  refine ⟨72107175456400377679183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6153145638946165561956949 72107175456400377679183)
                  ·
                    rfl

theorem cell23_1263854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_1263854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263854 prefixEnd_1263854 := by exact prefixLift 1263854
  have htrace : WordTrace (prefixWord ++ tailWord_1263854) baseStart_1263854 baseEnd_1263854 := by
    simpa [prefixWord, tailWord_1263854, baseEnd_1263854] using wordTrace_append hprefix tailTrace_1263854
  have hstable : (prefixWord ++ tailWord_1263854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263854).length < 2 ^ (prefixWord ++ tailWord_1263854).sum := by decide
  have hdescent : baseEnd_1263854 < baseStart_1263854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263864 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1263864 : Nat := 118140960795 + 1263864 * 2 ^ 59
def prefixEnd_1263864 : Nat := 4983230072969 + 3 ^ 40 * 1263864 * 2
def baseEnd_1263864 : Nat := 648969713914148359987601

theorem tailTrace_1263864 : CollatzResearch.WordTrace tailWord_1263864 prefixEnd_1263864 648969713914148359987601 := by
  unfold tailWord_1263864
  simp only [CollatzResearch.WordTrace]
  refine ⟨23048453546622026815775323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30731271395496035754367097 23048453546622026815775323)
  ·
    refine ⟨34572680319933040223662985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23048453546622026815775323 34572680319933040223662985)
    ·
      refine ⟨25929510239949780167747239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34572680319933040223662985 25929510239949780167747239)
      ·
        refine ⟨38894265359924670251620859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25929510239949780167747239 38894265359924670251620859)
        ·
          refine ⟨58341398039887005377431289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38894265359924670251620859 58341398039887005377431289)
          ·
            refine ⟨43756048529915254033073467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58341398039887005377431289 43756048529915254033073467)
            ·
              refine ⟨65634072794872881049610201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43756048529915254033073467 65634072794872881049610201)
              ·
                refine ⟨49225554596154660787207651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65634072794872881049610201 49225554596154660787207651)
                ·
                  refine ⟨73838331894231991180811477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49225554596154660787207651 73838331894231991180811477)
                  ·
                    refine ⟨1730585903771062293300269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73838331894231991180811477 1730585903771062293300269)
                    ·
                      refine ⟨648969713914148359987601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1730585903771062293300269 648969713914148359987601)
                      ·
                        rfl

theorem cell23_1263864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1263864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263864 prefixEnd_1263864 := by exact prefixLift 1263864
  have htrace : WordTrace (prefixWord ++ tailWord_1263864) baseStart_1263864 baseEnd_1263864 := by
    simpa [prefixWord, tailWord_1263864, baseEnd_1263864] using wordTrace_append hprefix tailTrace_1263864
  have hstable : (prefixWord ++ tailWord_1263864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263864).length < 2 ^ (prefixWord ++ tailWord_1263864).sum := by decide
  have hdescent : baseEnd_1263864 < baseStart_1263864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263908 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_1263908 : Nat := 118140960795 + 1263908 * 2 ^ 59
def prefixEnd_1263908 : Nat := 4983230072969 + 3 ^ 40 * 1263908 * 2
def baseEnd_1263908 : Nat := 648992307062946187837399

theorem tailTrace_1263908 : CollatzResearch.WordTrace tailWord_1263908 prefixEnd_1263908 648992307062946187837399 := by
  unfold tailWord_1263908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049255952542324573076189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30732341270056432764101585 23049255952542324573076189)
  ·
    refine ⟨8643470982203371714903571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23049255952542324573076189 8643470982203371714903571)
    ·
      refine ⟨12965206473305057572355357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643470982203371714903571 12965206473305057572355357)
      ·
        refine ⟨4861952427489396589633259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12965206473305057572355357 4861952427489396589633259)
        ·
          refine ⟨7292928641234094884449889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4861952427489396589633259 7292928641234094884449889)
          ·
            refine ⟨5469696480925571163337417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7292928641234094884449889 5469696480925571163337417)
            ·
              refine ⟨4102272360694178372503063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469696480925571163337417 4102272360694178372503063)
              ·
                refine ⟨6153408541041267558754595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102272360694178372503063 6153408541041267558754595)
                ·
                  refine ⟨9230112811561901338131893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153408541041267558754595 9230112811561901338131893)
                  ·
                    refine ⟨865323076083928250449865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230112811561901338131893 865323076083928250449865)
                    ·
                      refine ⟨648992307062946187837399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865323076083928250449865 648992307062946187837399)
                      ·
                        rfl

theorem cell23_1263908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_1263908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263908 prefixEnd_1263908 := by exact prefixLift 1263908
  have htrace : WordTrace (prefixWord ++ tailWord_1263908) baseStart_1263908 baseEnd_1263908 := by
    simpa [prefixWord, tailWord_1263908, baseEnd_1263908] using wordTrace_append hprefix tailTrace_1263908
  have hstable : (prefixWord ++ tailWord_1263908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263908).length < 2 ^ (prefixWord ++ tailWord_1263908).sum := by decide
  have hdescent : baseEnd_1263908 < baseStart_1263908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263932 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_1263932 : Nat := 118140960795 + 1263932 * 2 ^ 59
def prefixEnd_1263932 : Nat := 4983230072969 + 3 ^ 40 * 1263932 * 2
def baseEnd_1263932 : Nat := 649004630598654093937289

theorem tailTrace_1263932 : CollatzResearch.WordTrace tailWord_1263932 prefixEnd_1263932 649004630598654093937289 := by
  unfold tailWord_1263932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049693628498850622513025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30732924837998467496684033 23049693628498850622513025)
  ·
    refine ⟨17287270221374137966884769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23049693628498850622513025 17287270221374137966884769)
    ·
      refine ⟨12965452666030603475163577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17287270221374137966884769 12965452666030603475163577)
      ·
        refine ⟨9724089499522952606372683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12965452666030603475163577 9724089499522952606372683)
        ·
          refine ⟨14586134249284428909559025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724089499522952606372683 14586134249284428909559025)
          ·
            refine ⟨10939600686963321682169269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14586134249284428909559025 10939600686963321682169269)
            ·
              refine ⟨1025587564402811407703369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10939600686963321682169269 1025587564402811407703369)
              ·
                refine ⟨769190673302108555777527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1025587564402811407703369 769190673302108555777527)
                ·
                  refine ⟨1153786009953162833666291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769190673302108555777527 1153786009953162833666291)
                  ·
                    refine ⟨1730679014929744250499437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1153786009953162833666291 1730679014929744250499437)
                    ·
                      refine ⟨649004630598654093937289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1730679014929744250499437 649004630598654093937289)
                      ·
                        rfl

theorem cell23_1263932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_1263932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263932 prefixEnd_1263932 := by exact prefixLift 1263932
  have htrace : WordTrace (prefixWord ++ tailWord_1263932) baseStart_1263932 baseEnd_1263932 := by
    simpa [prefixWord, tailWord_1263932, baseEnd_1263932] using wordTrace_append hprefix tailTrace_1263932
  have hstable : (prefixWord ++ tailWord_1263932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263932).length < 2 ^ (prefixWord ++ tailWord_1263932).sum := by decide
  have hdescent : baseEnd_1263932 < baseStart_1263932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263944 : List Nat := [2, 1, 3, 1, 1, 2, 3, 10]
def baseStart_1263944 : Nat := 118140960795 + 1263944 * 2 ^ 59
def prefixEnd_1263944 : Nat := 4983230072969 + 3 ^ 40 * 1263944 * 2
def baseEnd_1263944 : Nat := 24037436754315112851379

theorem tailTrace_1263944 : CollatzResearch.WordTrace tailWord_1263944 prefixEnd_1263944 24037436754315112851379 := by
  unfold tailWord_1263944
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049912466477113647231443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30733216621969484862975257 23049912466477113647231443)
  ·
    refine ⟨34574868699715670470847165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23049912466477113647231443 34574868699715670470847165)
    ·
      refine ⟨12965575762393376426567687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34574868699715670470847165 12965575762393376426567687)
      ·
        refine ⟨19448363643590064639851531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965575762393376426567687 19448363643590064639851531)
        ·
          refine ⟨29172545465385096959777297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19448363643590064639851531 29172545465385096959777297)
          ·
            refine ⟨21879409099038822719832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29172545465385096959777297 21879409099038822719832973)
            ·
              refine ⟨8204778412139558519937365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21879409099038822719832973 8204778412139558519937365)
              ·
                refine ⟨24037436754315112851379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8204778412139558519937365 24037436754315112851379)
                ·
                  rfl

theorem cell23_1263944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 10].length) (baseStart_1263944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263944 prefixEnd_1263944 := by exact prefixLift 1263944
  have htrace : WordTrace (prefixWord ++ tailWord_1263944) baseStart_1263944 baseEnd_1263944 := by
    simpa [prefixWord, tailWord_1263944, baseEnd_1263944] using wordTrace_append hprefix tailTrace_1263944
  have hstable : (prefixWord ++ tailWord_1263944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263944).length < 2 ^ (prefixWord ++ tailWord_1263944).sum := by decide
  have hdescent : baseEnd_1263944 < baseStart_1263944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263948 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_1263948 : Nat := 118140960795 + 1263948 * 2 ^ 59
def prefixEnd_1263948 : Nat := 4983230072969 + 3 ^ 40 * 1263948 * 2
def baseEnd_1263948 : Nat := 216337615429708677112405

theorem tailTrace_1263948 : CollatzResearch.WordTrace tailWord_1263948 prefixEnd_1263948 216337615429708677112405 := by
  unfold tailWord_1263948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049985412469867988804249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30733313883293157318405665 23049985412469867988804249)
  ·
    refine ⟨17287489059352400991603187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23049985412469867988804249 17287489059352400991603187)
    ·
      refine ⟨25931233589028601487404781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17287489059352400991603187 25931233589028601487404781)
      ·
        refine ⟨9724212595885725557776793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25931233589028601487404781 9724212595885725557776793)
        ·
          refine ⟨7293159446914294168332595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9724212595885725557776793 7293159446914294168332595)
          ·
            refine ⟨10939739170371441252498893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293159446914294168332595 10939739170371441252498893)
            ·
              refine ⟨4102402188889290469687085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10939739170371441252498893 4102402188889290469687085)
              ·
                refine ⟨1538400820833483926132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4102402188889290469687085 1538400820833483926132657)
                ·
                  refine ⟨1153800615625112944599493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538400820833483926132657 1153800615625112944599493)
                  ·
                    refine ⟨216337615429708677112405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1153800615625112944599493 216337615429708677112405)
                    ·
                      rfl

theorem cell23_1263948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_1263948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263948 prefixEnd_1263948 := by exact prefixLift 1263948
  have htrace : WordTrace (prefixWord ++ tailWord_1263948) baseStart_1263948 baseEnd_1263948 := by
    simpa [prefixWord, tailWord_1263948, baseEnd_1263948] using wordTrace_append hprefix tailTrace_1263948
  have hstable : (prefixWord ++ tailWord_1263948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263948).length < 2 ^ (prefixWord ++ tailWord_1263948).sum := by decide
  have hdescent : baseEnd_1263948 < baseStart_1263948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263968 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1263968 : Nat := 118140960795 + 1263968 * 2 ^ 59
def prefixEnd_1263968 : Nat := 4983230072969 + 3 ^ 40 * 1263968 * 2
def baseEnd_1263968 : Nat := 649023115902215953087123

theorem tailTrace_1263968 : CollatzResearch.WordTrace tailWord_1263968 prefixEnd_1263968 649023115902215953087123 := by
  unfold tailWord_1263968
  simp only [CollatzResearch.WordTrace]
  refine ⟨23050350142433639696668279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30733800189911519595557705 23050350142433639696668279)
  ·
    refine ⟨34575525213650459545002419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23050350142433639696668279 34575525213650459545002419)
    ·
      refine ⟨51863287820475689317503629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34575525213650459545002419 51863287820475689317503629)
      ·
        refine ⟨19448732932678383494063861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51863287820475689317503629 19448732932678383494063861)
        ·
          refine ⟨1823318712438598452568487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19448732932678383494063861 1823318712438598452568487)
          ·
            refine ⟨2734978068657897678852731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823318712438598452568487 2734978068657897678852731)
            ·
              refine ⟨4102467102986846518279097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734978068657897678852731 4102467102986846518279097)
              ·
                refine ⟨3076850327240134888709323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102467102986846518279097 3076850327240134888709323)
                ·
                  refine ⟨4615275490860202333063985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076850327240134888709323 4615275490860202333063985)
                  ·
                    refine ⟨3461456618145151749797989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615275490860202333063985 3461456618145151749797989)
                    ·
                      refine ⟨649023115902215953087123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3461456618145151749797989 649023115902215953087123)
                      ·
                        rfl

theorem cell23_1263968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1263968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263968 prefixEnd_1263968 := by exact prefixLift 1263968
  have htrace : WordTrace (prefixWord ++ tailWord_1263968) baseStart_1263968 baseEnd_1263968 := by
    simpa [prefixWord, tailWord_1263968, baseEnd_1263968] using wordTrace_append hprefix tailTrace_1263968
  have hstable : (prefixWord ++ tailWord_1263968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263968).length < 2 ^ (prefixWord ++ tailWord_1263968).sum := by decide
  have hdescent : baseEnd_1263968 < baseStart_1263968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263972 : List Nat := [2, 3, 1, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_1263972 : Nat := 118140960795 + 1263972 * 2 ^ 59
def prefixEnd_1263972 : Nat := 4983230072969 + 3 ^ 40 * 1263972 * 2
def baseEnd_1263972 : Nat := 649025169824833937437105

theorem tailTrace_1263972 : CollatzResearch.WordTrace tailWord_1263972 prefixEnd_1263972 649025169824833937437105 := by
  unfold tailWord_1263972
  simp only [CollatzResearch.WordTrace]
  refine ⟨23050423088426394038241085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30733897451235192050988113 23050423088426394038241085)
  ·
    refine ⟨8643908658159897764340407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23050423088426394038241085 8643908658159897764340407)
    ·
      refine ⟨12965862987239846646510611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643908658159897764340407 12965862987239846646510611)
      ·
        refine ⟨19448794480859769969765917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965862987239846646510611 19448794480859769969765917)
        ·
          refine ⟨7293297930322413738662219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19448794480859769969765917 7293297930322413738662219)
          ·
            refine ⟨10939946895483620607993329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293297930322413738662219 10939946895483620607993329)
            ·
              refine ⟨8204960171612715455994997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939946895483620607993329 8204960171612715455994997)
              ·
                refine ⟨769215016088692073999531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8204960171612715455994997 769215016088692073999531)
                ·
                  refine ⟨1153822524133038110999297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769215016088692073999531 1153822524133038110999297)
                  ·
                    refine ⟨865366893099778583249473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153822524133038110999297 865366893099778583249473)
                    ·
                      refine ⟨649025169824833937437105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865366893099778583249473 649025169824833937437105)
                      ·
                        rfl

theorem cell23_1263972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_1263972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263972 prefixEnd_1263972 := by exact prefixLift 1263972
  have htrace : WordTrace (prefixWord ++ tailWord_1263972) baseStart_1263972 baseEnd_1263972 := by
    simpa [prefixWord, tailWord_1263972, baseEnd_1263972] using wordTrace_append hprefix tailTrace_1263972
  have hstable : (prefixWord ++ tailWord_1263972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263972).length < 2 ^ (prefixWord ++ tailWord_1263972).sum := by decide
  have hdescent : baseEnd_1263972 < baseStart_1263972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1263989 : List Nat := [1, 3, 4, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1263989 : Nat := 118140960795 + 1263989 * 2 ^ 59
def prefixEnd_1263989 : Nat := 4983230072969 + 3 ^ 40 * 1263989 * 2
def baseEnd_1263989 : Nat := 649033898995960370924527

theorem tailTrace_1263989 : CollatzResearch.WordTrace tailWord_1263989 prefixEnd_1263989 649033898995960370924527 := by
  unfold tailWord_1263989
  simp only [CollatzResearch.WordTrace]
  refine ⟨46101466217791199979851021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30734310811860799986567347 46101466217791199979851021)
  ·
    refine ⟨17288049831671699992444133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46101466217791199979851021 17288049831671699992444133)
    ·
      refine ⟨3241509343438443748583275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17288049831671699992444133 3241509343438443748583275)
      ·
        refine ⟨4862264015157665622874913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241509343438443748583275 4862264015157665622874913)
        ·
          refine ⟨3646698011368249217156185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862264015157665622874913 3646698011368249217156185)
          ·
            refine ⟨2735023508526186912867139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3646698011368249217156185 2735023508526186912867139)
            ·
              refine ⟨4102535262789280369300709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735023508526186912867139 4102535262789280369300709)
              ·
                refine ⟨769225361772990069243883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4102535262789280369300709 769225361772990069243883)
                ·
                  refine ⟨1153838042659485103865825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769225361772990069243883 1153838042659485103865825)
                  ·
                    refine ⟨865378531994613827899369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153838042659485103865825 865378531994613827899369)
                    ·
                      refine ⟨649033898995960370924527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865378531994613827899369 649033898995960370924527)
                      ·
                        rfl

theorem cell23_1263989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1263989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1263989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1263989 prefixEnd_1263989 := by exact prefixLift 1263989
  have htrace : WordTrace (prefixWord ++ tailWord_1263989) baseStart_1263989 baseEnd_1263989 := by
    simpa [prefixWord, tailWord_1263989, baseEnd_1263989] using wordTrace_append hprefix tailTrace_1263989
  have hstable : (prefixWord ++ tailWord_1263989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1263989).length < 2 ^ (prefixWord ++ tailWord_1263989).sum := by decide
  have hdescent : baseEnd_1263989 < baseStart_1263989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1263989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264002 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1264002 : Nat := 118140960795 + 1264002 * 2 ^ 59
def prefixEnd_1264002 : Nat := 4983230072969 + 3 ^ 40 * 1264002 * 2
def baseEnd_1264002 : Nat := 649040574244468820061967

theorem tailTrace_1264002 : CollatzResearch.WordTrace tailWord_1264002 prefixEnd_1264002 649040574244468820061967 := by
  unfold tailWord_1264002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525485091686025800018565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30734626911162735466716173 11525485091686025800018565)
  ·
    refine ⟨2161028454691129837503481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11525485091686025800018565 2161028454691129837503481)
    ·
      refine ⟨1620771341018347378127611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2161028454691129837503481 1620771341018347378127611)
      ·
        refine ⟨2431157011527521067191417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620771341018347378127611 2431157011527521067191417)
        ·
          refine ⟨1823367758645640800393563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2431157011527521067191417 1823367758645640800393563)
          ·
            refine ⟨2735051637968461200590345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823367758645640800393563 2735051637968461200590345)
            ·
              refine ⟨2051288728476345900442759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735051637968461200590345 2051288728476345900442759)
              ·
                refine ⟨3076933092714518850664139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051288728476345900442759 3076933092714518850664139)
                ·
                  refine ⟨4615399639071778275996209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076933092714518850664139 4615399639071778275996209)
                  ·
                    refine ⟨3461549729303833706997157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615399639071778275996209 3461549729303833706997157)
                    ·
                      refine ⟨649040574244468820061967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3461549729303833706997157 649040574244468820061967)
                      ·
                        rfl

theorem cell23_1264002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1264002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264002 prefixEnd_1264002 := by exact prefixLift 1264002
  have htrace : WordTrace (prefixWord ++ tailWord_1264002) baseStart_1264002 baseEnd_1264002 := by
    simpa [prefixWord, tailWord_1264002, baseEnd_1264002] using wordTrace_append hprefix tailTrace_1264002
  have hstable : (prefixWord ++ tailWord_1264002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264002).length < 2 ^ (prefixWord ++ tailWord_1264002).sum := by decide
  have hdescent : baseEnd_1264002 < baseStart_1264002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264031 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1264031 : Nat := 118140960795 + 1264031 * 2 ^ 59
def prefixEnd_1264031 : Nat := 4983230072969 + 3 ^ 40 * 1264031 * 2
def baseEnd_1264031 : Nat := 649055465183449206599333

theorem tailTrace_1264031 : CollatzResearch.WordTrace tailWord_1264031 prefixEnd_1264031 649055465183449206599333 := by
  unfold tailWord_1264031
  simp only [CollatzResearch.WordTrace]
  refine ⟨46102998083639041152879947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30735332055759360768586631 46102998083639041152879947)
  ·
    refine ⟨69154497125458561729319921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46102998083639041152879947 69154497125458561729319921)
    ·
      refine ⟨51865872844093921296989941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69154497125458561729319921 51865872844093921296989941)
      ·
        refine ⟨4862425579133805121592807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51865872844093921296989941 4862425579133805121592807)
        ·
          refine ⟨7293638368700707682389211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862425579133805121592807 7293638368700707682389211)
          ·
            refine ⟨10940457553051061523583817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293638368700707682389211 10940457553051061523583817)
            ·
              refine ⟨8205343164788296142687863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10940457553051061523583817 8205343164788296142687863)
              ·
                refine ⟨12308014747182444214031795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205343164788296142687863 12308014747182444214031795)
                ·
                  refine ⟨18462022120773666321047693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12308014747182444214031795 18462022120773666321047693)
                  ·
                    refine ⟨6923258295290124870392885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18462022120773666321047693 6923258295290124870392885)
                    ·
                      refine ⟨649055465183449206599333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6923258295290124870392885 649055465183449206599333)
                      ·
                        rfl

theorem cell23_1264031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1264031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264031 prefixEnd_1264031 := by exact prefixLift 1264031
  have htrace : WordTrace (prefixWord ++ tailWord_1264031) baseStart_1264031 baseEnd_1264031 := by
    simpa [prefixWord, tailWord_1264031, baseEnd_1264031] using wordTrace_append hprefix tailTrace_1264031
  have hstable : (prefixWord ++ tailWord_1264031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264031).length < 2 ^ (prefixWord ++ tailWord_1264031).sum := by decide
  have hdescent : baseEnd_1264031 < baseStart_1264031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264032 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2]
def baseStart_1264032 : Nat := 118140960795 + 1264032 * 2 ^ 59
def prefixEnd_1264032 : Nat := 4983230072969 + 3 ^ 40 * 1264032 * 2
def baseEnd_1264032 : Nat := 649055978664103702686829

theorem tailTrace_1264032 : CollatzResearch.WordTrace tailWord_1264032 prefixEnd_1264032 649055978664103702686829 := by
  unfold tailWord_1264032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23051517278317709161833175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30735356371090278882444233 23051517278317709161833175)
  ·
    refine ⟨34577275917476563742749763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23051517278317709161833175 34577275917476563742749763)
    ·
      refine ⟨51865913876214845614124645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34577275917476563742749763 51865913876214845614124645)
      ·
        refine ⟨9724858851790283552648371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51865913876214845614124645 9724858851790283552648371)
        ·
          refine ⟨14587288277685425328972557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724858851790283552648371 14587288277685425328972557)
          ·
            refine ⟨5470233104132034498364709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14587288277685425328972557 5470233104132034498364709)
            ·
              refine ⟨1025668707024756468443383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5470233104132034498364709 1025668707024756468443383)
              ·
                refine ⟨1538503060537134702665075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1025668707024756468443383 1538503060537134702665075)
                ·
                  refine ⟨2307754590805702053997613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538503060537134702665075 2307754590805702053997613)
                  ·
                    refine ⟨865407971552138270249105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307754590805702053997613 865407971552138270249105)
                    ·
                      refine ⟨649055978664103702686829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865407971552138270249105 649055978664103702686829)
                      ·
                        rfl

theorem cell23_1264032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_1264032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264032 prefixEnd_1264032 := by exact prefixLift 1264032
  have htrace : WordTrace (prefixWord ++ tailWord_1264032) baseStart_1264032 baseEnd_1264032 := by
    simpa [prefixWord, tailWord_1264032, baseEnd_1264032] using wordTrace_append hprefix tailTrace_1264032
  have hstable : (prefixWord ++ tailWord_1264032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264032).length < 2 ^ (prefixWord ++ tailWord_1264032).sum := by decide
  have hdescent : baseEnd_1264032 < baseStart_1264032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264062 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_1264062 : Nat := 118140960795 + 1264062 * 2 ^ 59
def prefixEnd_1264062 : Nat := 4983230072969 + 3 ^ 40 * 1264062 * 2
def baseEnd_1264062 : Nat := 649071383083738585311691

theorem tailTrace_1264062 : CollatzResearch.WordTrace tailWord_1264062 prefixEnd_1264062 649071383083738585311691 := by
  unfold tailWord_1264062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763016093315841680907305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30736085831017822298172293 5763016093315841680907305)
  ·
    refine ⟨4322262069986881260680479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5763016093315841680907305 4322262069986881260680479)
    ·
      refine ⟨6483393104980321891020719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4322262069986881260680479 6483393104980321891020719)
      ·
        refine ⟨9725089657470482836531079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6483393104980321891020719 9725089657470482836531079)
        ·
          refine ⟨14587634486205724254796619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9725089657470482836531079 14587634486205724254796619)
          ·
            refine ⟨21881451729308586382194929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14587634486205724254796619 21881451729308586382194929)
            ·
              refine ⟨16411088796981439786646197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21881451729308586382194929 16411088796981439786646197)
              ·
                refine ⟨1538539574717009979998081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16411088796981439786646197 1538539574717009979998081)
                ·
                  refine ⟨1153904681037757484998561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1538539574717009979998081 1153904681037757484998561)
                  ·
                    refine ⟨865428510778318113748921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1153904681037757484998561 865428510778318113748921)
                    ·
                      refine ⟨649071383083738585311691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865428510778318113748921 649071383083738585311691)
                      ·
                        rfl

theorem cell23_1264062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_1264062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264062 prefixEnd_1264062 := by exact prefixLift 1264062
  have htrace : WordTrace (prefixWord ++ tailWord_1264062) baseStart_1264062 baseEnd_1264062 := by
    simpa [prefixWord, tailWord_1264062, baseEnd_1264062] using wordTrace_append hprefix tailTrace_1264062
  have hstable : (prefixWord ++ tailWord_1264062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264062).length < 2 ^ (prefixWord ++ tailWord_1264062).sum := by decide
  have hdescent : baseEnd_1264062 < baseStart_1264062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264081 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1264081 : Nat := 118140960795 + 1264081 * 2 ^ 59
def prefixEnd_1264081 : Nat := 4983230072969 + 3 ^ 40 * 1264081 * 2
def baseEnd_1264081 : Nat := 216360379738724670324701

theorem tailTrace_1264081 : CollatzResearch.WordTrace tailWord_1264081 prefixEnd_1264081 216360379738724670324701 := by
  unfold tailWord_1264081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46104821733457899692200097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30736547822305266461466731 46104821733457899692200097)
  ·
    refine ⟨34578616300093424769150073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46104821733457899692200097 34578616300093424769150073)
    ·
      refine ⟨25933962225070068576862555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34578616300093424769150073 25933962225070068576862555)
      ·
        refine ⟨38900943337605102865293833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25933962225070068576862555 38900943337605102865293833)
        ·
          refine ⟨29175707503203827148970375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38900943337605102865293833 29175707503203827148970375)
          ·
            refine ⟨43763561254805740723455563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29175707503203827148970375 43763561254805740723455563)
            ·
              refine ⟨65645341882208611085183345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43763561254805740723455563 65645341882208611085183345)
              ·
                refine ⟨49234006411656458313887509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65645341882208611085183345 49234006411656458313887509)
                ·
                  refine ⟨2307844050546396483463477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49234006411656458313887509 2307844050546396483463477)
                  ·
                    refine ⟨216360379738724670324701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2307844050546396483463477 216360379738724670324701)
                    ·
                      rfl

theorem cell23_1264081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1264081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264081 prefixEnd_1264081 := by exact prefixLift 1264081
  have htrace : WordTrace (prefixWord ++ tailWord_1264081) baseStart_1264081 baseEnd_1264081 := by
    simpa [prefixWord, tailWord_1264081, baseEnd_1264081] using wordTrace_append hprefix tailTrace_1264081
  have hstable : (prefixWord ++ tailWord_1264081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264081).length < 2 ^ (prefixWord ++ tailWord_1264081).sum := by decide
  have hdescent : baseEnd_1264081 < baseStart_1264081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264085 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 5]
def baseStart_1264085 : Nat := 118140960795 + 1264085 * 2 ^ 59
def prefixEnd_1264085 : Nat := 4983230072969 + 3 ^ 40 * 1264085 * 2
def baseEnd_1264085 : Nat := 72120354793199110591565

theorem tailTrace_1264085 : CollatzResearch.WordTrace tailWord_1264085 prefixEnd_1264085 72120354793199110591565 := by
  unfold tailWord_1264085
  simp only [CollatzResearch.WordTrace]
  refine ⟨46104967625443408375345709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30736645083628938916897139 46104967625443408375345709)
  ·
    refine ⟨17289362859541278140754641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46104967625443408375345709 17289362859541278140754641)
    ·
      refine ⟨12967022144655958605565981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17289362859541278140754641 12967022144655958605565981)
      ·
        refine ⟨4862633304245984477087243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12967022144655958605565981 4862633304245984477087243)
        ·
          refine ⟨7293949956368976715630865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862633304245984477087243 7293949956368976715630865)
          ·
            refine ⟨5470462467276732536723149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293949956368976715630865 5470462467276732536723149)
            ·
              refine ⟨2051423425228774701271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470462467276732536723149 2051423425228774701271181)
              ·
                refine ⟨769283784460790512976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2051423425228774701271181 769283784460790512976693)
                ·
                  refine ⟨72120354793199110591565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769283784460790512976693 72120354793199110591565)
                  ·
                    rfl

theorem cell23_1264085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_1264085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264085 prefixEnd_1264085 := by exact prefixLift 1264085
  have htrace : WordTrace (prefixWord ++ tailWord_1264085) baseStart_1264085 baseEnd_1264085 := by
    simpa [prefixWord, tailWord_1264085, baseEnd_1264085] using wordTrace_append hprefix tailTrace_1264085
  have hstable : (prefixWord ++ tailWord_1264085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264085).length < 2 ^ (prefixWord ++ tailWord_1264085).sum := by decide
  have hdescent : baseEnd_1264085 < baseStart_1264085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264088 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_1264088 : Nat := 118140960795 + 1264088 * 2 ^ 59
def prefixEnd_1264088 : Nat := 4983230072969 + 3 ^ 40 * 1264088 * 2
def baseEnd_1264088 : Nat := 649084733580755483586571

theorem tailTrace_1264088 : CollatzResearch.WordTrace tailWord_1264088 prefixEnd_1264088 649084733580755483586571 := by
  unfold tailWord_1264088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23052538522216269943852459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30736718029621693258469945 23052538522216269943852459)
  ·
    refine ⟨34578807783324404915778689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23052538522216269943852459 34578807783324404915778689)
    ·
      refine ⟨25934105837493303686834017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34578807783324404915778689 25934105837493303686834017)
      ·
        refine ⟨19450579378119977765125513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25934105837493303686834017 19450579378119977765125513)
        ·
          refine ⟨14587934533589983323844135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19450579378119977765125513 14587934533589983323844135)
          ·
            refine ⟨21881901800384974985766203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14587934533589983323844135 21881901800384974985766203)
            ·
              refine ⟨32822852700577462478649305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21881901800384974985766203 32822852700577462478649305)
              ·
                refine ⟨24617139525433096858986979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32822852700577462478649305 24617139525433096858986979)
                ·
                  refine ⟨36925709288149645288480469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24617139525433096858986979 36925709288149645288480469)
                  ·
                    refine ⟨865446311441007311448761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36925709288149645288480469 865446311441007311448761)
                    ·
                      refine ⟨649084733580755483586571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865446311441007311448761 649084733580755483586571)
                      ·
                        rfl

theorem cell23_1264088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_1264088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264088 prefixEnd_1264088 := by exact prefixLift 1264088
  have htrace : WordTrace (prefixWord ++ tailWord_1264088) baseStart_1264088 baseEnd_1264088 := by
    simpa [prefixWord, tailWord_1264088, baseEnd_1264088] using wordTrace_append hprefix tailTrace_1264088
  have hstable : (prefixWord ++ tailWord_1264088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264088).length < 2 ^ (prefixWord ++ tailWord_1264088).sum := by decide
  have hdescent : baseEnd_1264088 < baseStart_1264088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264208 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_1264208 : Nat := 118140960795 + 1264208 * 2 ^ 59
def prefixEnd_1264208 : Nat := 4983230072969 + 3 ^ 40 * 1264208 * 2
def baseEnd_1264208 : Nat := 649146351259295014086019

theorem tailTrace_1264208 : CollatzResearch.WordTrace tailWord_1264208 prefixEnd_1264208 649146351259295014086019 := by
  unfold tailWord_1264208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23054726901998900191036639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30739635869331866921382185 23054726901998900191036639)
  ·
    refine ⟨34582090352998350286554959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23054726901998900191036639 34582090352998350286554959)
    ·
      refine ⟨51873135529497525429832439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34582090352998350286554959 51873135529497525429832439)
      ·
        refine ⟨77809703294246288144748659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51873135529497525429832439 77809703294246288144748659)
        ·
          refine ⟨116714554941369432217122989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77809703294246288144748659 116714554941369432217122989)
          ·
            refine ⟨43767958103013537081421121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116714554941369432217122989 43767958103013537081421121)
            ·
              refine ⟨32825968577260152811065841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43767958103013537081421121 32825968577260152811065841)
              ·
                refine ⟨24619476432945114608299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32825968577260152811065841 24619476432945114608299381)
                ·
                  refine ⟨2308075915588604494528067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24619476432945114608299381 2308075915588604494528067)
                  ·
                    refine ⟨3462113873382906741792101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308075915588604494528067 3462113873382906741792101)
                    ·
                      refine ⟨649146351259295014086019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3462113873382906741792101 649146351259295014086019)
                      ·
                        rfl

theorem cell23_1264208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_1264208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264208 prefixEnd_1264208 := by exact prefixLift 1264208
  have htrace : WordTrace (prefixWord ++ tailWord_1264208) baseStart_1264208 baseEnd_1264208 := by
    simpa [prefixWord, tailWord_1264208, baseEnd_1264208] using wordTrace_append hprefix tailTrace_1264208
  have hstable : (prefixWord ++ tailWord_1264208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264208).length < 2 ^ (prefixWord ++ tailWord_1264208).sum := by decide
  have hdescent : baseEnd_1264208 < baseStart_1264208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264253 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_1264253 : Nat := 118140960795 + 1264253 * 2 ^ 59
def prefixEnd_1264253 : Nat := 4983230072969 + 3 ^ 40 * 1264253 * 2
def baseEnd_1264253 : Nat := 649169457888747338023313

theorem tailTrace_1264253 : CollatzResearch.WordTrace tailWord_1264253 prefixEnd_1264253 649169457888747338023313 := by
  unfold tailWord_1264253
  simp only [CollatzResearch.WordTrace]
  refine ⟨46111095088834773067461413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30740730059223182044974275 46111095088834773067461413)
  ·
    refine ⟨8645830329156519950149015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46111095088834773067461413 8645830329156519950149015)
    ·
      refine ⟨12968745493734779925223523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645830329156519950149015 12968745493734779925223523)
      ·
        refine ⟨19453118240602169887835285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968745493734779925223523 19453118240602169887835285)
        ·
          refine ⟨911864917528226713492279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19453118240602169887835285 911864917528226713492279)
          ·
            refine ⟨1367797376292340070238419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911864917528226713492279 1367797376292340070238419)
            ·
              refine ⟨2051696064438510105357629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1367797376292340070238419 2051696064438510105357629)
              ·
                refine ⟨769386024164441289509111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2051696064438510105357629 769386024164441289509111)
                ·
                  refine ⟨1154079036246661934263667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769386024164441289509111 1154079036246661934263667)
                  ·
                    refine ⟨1731118554369992901395501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154079036246661934263667 1731118554369992901395501)
                    ·
                      refine ⟨649169457888747338023313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731118554369992901395501 649169457888747338023313)
                      ·
                        rfl

theorem cell23_1264253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_1264253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264253 prefixEnd_1264253 := by exact prefixLift 1264253
  have htrace : WordTrace (prefixWord ++ tailWord_1264253) baseStart_1264253 baseEnd_1264253 := by
    simpa [prefixWord, tailWord_1264253, baseEnd_1264253] using wordTrace_append hprefix tailTrace_1264253
  have hstable : (prefixWord ++ tailWord_1264253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264253).length < 2 ^ (prefixWord ++ tailWord_1264253).sum := by decide
  have hdescent : baseEnd_1264253 < baseStart_1264253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264276 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1264276 : Nat := 118140960795 + 1264276 * 2 ^ 59
def prefixEnd_1264276 : Nat := 4983230072969 + 3 ^ 40 * 1264276 * 2
def baseEnd_1264276 : Nat := 649181267943800748035707

theorem tailTrace_1264276 : CollatzResearch.WordTrace tailWord_1264276 prefixEnd_1264276 649181267943800748035707 := by
  unfold tailWord_1264276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055966983875723997774341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30741289311834298663699121 23055966983875723997774341)
  ·
    refine ⟨4322993809476698249582689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23055966983875723997774341 4322993809476698249582689)
    ·
      refine ⟨3242245357107523687187017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4322993809476698249582689 3242245357107523687187017)
      ·
        refine ⟨2431684017830642765390263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242245357107523687187017 2431684017830642765390263)
        ·
          refine ⟨3647526026745964148085395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431684017830642765390263 3647526026745964148085395)
          ·
            refine ⟨5471289040118946222128093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647526026745964148085395 5471289040118946222128093)
            ·
              refine ⟨2051733390044604833298035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5471289040118946222128093 2051733390044604833298035)
              ·
                refine ⟨3077600085066907249947053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051733390044604833298035 3077600085066907249947053)
                ·
                  refine ⟨1154100031900090218730145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3077600085066907249947053 1154100031900090218730145)
                  ·
                    refine ⟨865575023925067664047609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1154100031900090218730145 865575023925067664047609)
                    ·
                      refine ⟨649181267943800748035707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865575023925067664047609 649181267943800748035707)
                      ·
                        rfl

theorem cell23_1264276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1264276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264276 prefixEnd_1264276 := by exact prefixLift 1264276
  have htrace : WordTrace (prefixWord ++ tailWord_1264276) baseStart_1264276 baseEnd_1264276 := by
    simpa [prefixWord, tailWord_1264276, baseEnd_1264276] using wordTrace_append hprefix tailTrace_1264276
  have hstable : (prefixWord ++ tailWord_1264276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264276).length < 2 ^ (prefixWord ++ tailWord_1264276).sum := by decide
  have hdescent : baseEnd_1264276 < baseStart_1264276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264282 : List Nat := [3, 1, 1, 6, 1, 1, 2, 8]
def baseStart_1264282 : Nat := 118140960795 + 1264282 * 2 ^ 59
def prefixEnd_1264282 : Nat := 4983230072969 + 3 ^ 40 * 1264282 * 2
def baseEnd_1264282 : Nat := 24043864771397323131877

theorem tailTrace_1264282 : CollatzResearch.WordTrace tailWord_1264282 prefixEnd_1264282 24043864771397323131877 := by
  unfold tailWord_1264282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11528038201432427755066775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30741435203819807346844733 11528038201432427755066775)
  ·
    refine ⟨17292057302148641632600163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11528038201432427755066775 17292057302148641632600163)
    ·
      refine ⟨25938085953222962448900245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17292057302148641632600163 25938085953222962448900245)
      ·
        refine ⟨1215847779057326364792199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25938085953222962448900245 1215847779057326364792199)
        ·
          refine ⟨1823771668585989547188299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215847779057326364792199 1823771668585989547188299)
          ·
            refine ⟨2735657502878984320782449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823771668585989547188299 2735657502878984320782449)
            ·
              refine ⟨2051743127159238240586837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735657502878984320782449 2051743127159238240586837)
              ·
                refine ⟨24043864771397323131877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2051743127159238240586837 24043864771397323131877)
                ·
                  rfl

theorem cell23_1264282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_1264282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264282 prefixEnd_1264282 := by exact prefixLift 1264282
  have htrace : WordTrace (prefixWord ++ tailWord_1264282) baseStart_1264282 baseEnd_1264282 := by
    simpa [prefixWord, tailWord_1264282, baseEnd_1264282] using wordTrace_append hprefix tailTrace_1264282
  have hstable : (prefixWord ++ tailWord_1264282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264282).length < 2 ^ (prefixWord ++ tailWord_1264282).sum := by decide
  have hdescent : baseEnd_1264282 < baseStart_1264282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264345 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_1264345 : Nat := 118140960795 + 1264345 * 2 ^ 59
def prefixEnd_1264345 : Nat := 4983230072969 + 3 ^ 40 * 1264345 * 2
def baseEnd_1264345 : Nat := 649216698108960978072889

theorem tailTrace_1264345 : CollatzResearch.WordTrace tailWord_1264345 prefixEnd_1264345 649216698108960978072889 := by
  unfold tailWord_1264345
  simp only [CollatzResearch.WordTrace]
  refine ⟨46114450604501472779810489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30742967069667648519873659 46114450604501472779810489)
  ·
    refine ⟨34585837953376104584857867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46114450604501472779810489 34585837953376104584857867)
    ·
      refine ⟨51878756930064156877286801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34585837953376104584857867 51878756930064156877286801)
      ·
        refine ⟨38909067697548117657965101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51878756930064156877286801 38909067697548117657965101)
        ·
          refine ⟨14590900386580544121736913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38909067697548117657965101 14590900386580544121736913)
          ·
            refine ⟨10943175289935408091302685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14590900386580544121736913 10943175289935408091302685)
            ·
              refine ⟨4103690733725778034238507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10943175289935408091302685 4103690733725778034238507)
              ·
                refine ⟨6155536100588667051357761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103690733725778034238507 6155536100588667051357761)
                ·
                  refine ⟨4616652075441500288518321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6155536100588667051357761 4616652075441500288518321)
                  ·
                    refine ⟨3462489056581125216388741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616652075441500288518321 3462489056581125216388741)
                    ·
                      refine ⟨649216698108960978072889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3462489056581125216388741 649216698108960978072889)
                      ·
                        rfl

theorem cell23_1264345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_1264345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264345 prefixEnd_1264345 := by exact prefixLift 1264345
  have htrace : WordTrace (prefixWord ++ tailWord_1264345) baseStart_1264345 baseEnd_1264345 := by
    simpa [prefixWord, tailWord_1264345, baseEnd_1264345] using wordTrace_append hprefix tailTrace_1264345
  have hstable : (prefixWord ++ tailWord_1264345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264345).length < 2 ^ (prefixWord ++ tailWord_1264345).sum := by decide
  have hdescent : baseEnd_1264345 < baseStart_1264345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264355 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 9]
def baseStart_1264355 : Nat := 118140960795 + 1264355 * 2 ^ 59
def prefixEnd_1264355 : Nat := 4983230072969 + 3 ^ 40 * 1264355 * 2
def baseEnd_1264355 : Nat := 72135759212833993216427

theorem tailTrace_1264355 : CollatzResearch.WordTrace tailWord_1264355 prefixEnd_1264355 72135759212833993216427 := by
  unfold tailWord_1264355
  simp only [CollatzResearch.WordTrace]
  refine ⟨46114815334465244487674519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30743210222976829658449679 46114815334465244487674519)
  ·
    refine ⟨69172223001697866731511779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46114815334465244487674519 69172223001697866731511779)
    ·
      refine ⟨103758334502546800097267669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69172223001697866731511779 103758334502546800097267669)
      ·
        refine ⟨2431835964903440627279711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 103758334502546800097267669 2431835964903440627279711)
        ·
          refine ⟨3647753947355160940919567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431835964903440627279711 3647753947355160940919567)
          ·
            refine ⟨5471630921032741411379351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647753947355160940919567 5471630921032741411379351)
            ·
              refine ⟨8207446381549112117069027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471630921032741411379351 8207446381549112117069027)
              ·
                refine ⟨12311169572323668175603541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8207446381549112117069027 12311169572323668175603541)
                ·
                  refine ⟨72135759212833993216427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12311169572323668175603541 72135759212833993216427)
                  ·
                    rfl

theorem cell23_1264355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 9].length) (baseStart_1264355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264355 prefixEnd_1264355 := by exact prefixLift 1264355
  have htrace : WordTrace (prefixWord ++ tailWord_1264355) baseStart_1264355 baseEnd_1264355 := by
    simpa [prefixWord, tailWord_1264355, baseEnd_1264355] using wordTrace_append hprefix tailTrace_1264355
  have hstable : (prefixWord ++ tailWord_1264355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264355).length < 2 ^ (prefixWord ++ tailWord_1264355).sum := by decide
  have hdescent : baseEnd_1264355 < baseStart_1264355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264385 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1264385 : Nat := 118140960795 + 1264385 * 2 ^ 59
def prefixEnd_1264385 : Nat := 4983230072969 + 3 ^ 40 * 1264385 * 2
def baseEnd_1264385 : Nat := 216412412445046940524235

theorem tailTrace_1264385 : CollatzResearch.WordTrace tailWord_1264385 prefixEnd_1264385 216412412445046940524235 := by
  unfold tailWord_1264385
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115909524356559611266609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30743939682904373074177739 46115909524356559611266609)
  ·
    refine ⟨34586932143267419708449957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46115909524356559611266609 34586932143267419708449957)
    ·
      refine ⟨6485049776862641195334367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34586932143267419708449957 6485049776862641195334367)
      ·
        refine ⟨9727574665293961793001551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485049776862641195334367 9727574665293961793001551)
        ·
          refine ⟨14591361997940942689502327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727574665293961793001551 14591361997940942689502327)
          ·
            refine ⟨21887042996911414034253491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14591361997940942689502327 21887042996911414034253491)
            ·
              refine ⟨32830564495367121051380237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21887042996911414034253491 32830564495367121051380237)
              ·
                refine ⟨12311461685762670394267589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32830564495367121051380237 12311461685762670394267589)
                ·
                  refine ⟨2308399066080500698925173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12311461685762670394267589 2308399066080500698925173)
                  ·
                    refine ⟨216412412445046940524235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2308399066080500698925173 216412412445046940524235)
                    ·
                      rfl

theorem cell23_1264385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1264385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264385 prefixEnd_1264385 := by exact prefixLift 1264385
  have htrace : WordTrace (prefixWord ++ tailWord_1264385) baseStart_1264385 baseEnd_1264385 := by
    simpa [prefixWord, tailWord_1264385, baseEnd_1264385] using wordTrace_append hprefix tailTrace_1264385
  have hstable : (prefixWord ++ tailWord_1264385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264385).length < 2 ^ (prefixWord ++ tailWord_1264385).sum := by decide
  have hdescent : baseEnd_1264385 < baseStart_1264385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264405 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1264405 : Nat := 118140960795 + 1264405 * 2 ^ 59
def prefixEnd_1264405 : Nat := 4983230072969 + 3 ^ 40 * 1264405 * 2
def baseEnd_1264405 : Nat := 649247506948230743322613

theorem tailTrace_1264405 : CollatzResearch.WordTrace tailWord_1264405 prefixEnd_1264405 649247506948230743322613 := by
  unfold tailWord_1264405
  simp only [CollatzResearch.WordTrace]
  refine ⟨46116638984284103026994669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30744425989522735351329779 46116638984284103026994669)
  ·
    refine ⟨17293739619106538635123001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46116638984284103026994669 17293739619106538635123001)
    ·
      refine ⟨12970304714329903976342251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17293739619106538635123001 12970304714329903976342251)
      ·
        refine ⟨19455457071494855964513377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12970304714329903976342251 19455457071494855964513377)
        ·
          refine ⟨14591592803621141973385033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19455457071494855964513377 14591592803621141973385033)
          ·
            refine ⟨10943694602715856480038775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14591592803621141973385033 10943694602715856480038775)
            ·
              refine ⟨16415541904073784720058163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943694602715856480038775 16415541904073784720058163)
              ·
                refine ⟨24623312856110677080087245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16415541904073784720058163 24623312856110677080087245)
                ·
                  refine ⟨9233742321041503905032717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24623312856110677080087245 9233742321041503905032717)
                  ·
                    refine ⟨3462653370390563964387269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9233742321041503905032717 3462653370390563964387269)
                    ·
                      refine ⟨649247506948230743322613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3462653370390563964387269 649247506948230743322613)
                      ·
                        rfl

theorem cell23_1264405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1264405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264405 prefixEnd_1264405 := by exact prefixLift 1264405
  have htrace : WordTrace (prefixWord ++ tailWord_1264405) baseStart_1264405 baseEnd_1264405 := by
    simpa [prefixWord, tailWord_1264405, baseEnd_1264405] using wordTrace_append hprefix tailTrace_1264405
  have hstable : (prefixWord ++ tailWord_1264405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264405).length < 2 ^ (prefixWord ++ tailWord_1264405).sum := by decide
  have hdescent : baseEnd_1264405 < baseStart_1264405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264476 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1264476 : Nat := 118140960795 + 1264476 * 2 ^ 59
def prefixEnd_1264476 : Nat := 4983230072969 + 3 ^ 40 * 1264476 * 2
def baseEnd_1264476 : Nat := 649283964074699965534787

theorem tailTrace_1264476 : CollatzResearch.WordTrace tailWord_1264476 prefixEnd_1264476 649283964074699965534787 := by
  unfold tailWord_1264476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059614283513441076414641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30746152378017921435219521 23059614283513441076414641)
  ·
    refine ⟨17294710712635080807310981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23059614283513441076414641 17294710712635080807310981)
    ·
      refine ⟨3242758258619077651370809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17294710712635080807310981 3242758258619077651370809)
      ·
        refine ⟨2432068693964308238528107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242758258619077651370809 2432068693964308238528107)
        ·
          refine ⟨3648103040946462357792161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432068693964308238528107 3648103040946462357792161)
          ·
            refine ⟨2736077280709846768344121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648103040946462357792161 2736077280709846768344121)
            ·
              refine ⟨2052057960532385076258091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736077280709846768344121 2052057960532385076258091)
              ·
                refine ⟨3078086940798577614387137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052057960532385076258091 3078086940798577614387137)
                ·
                  refine ⟨2308565205598933210790353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078086940798577614387137 2308565205598933210790353)
                  ·
                    refine ⟨1731423904199199908092765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2308565205598933210790353 1731423904199199908092765)
                    ·
                      refine ⟨649283964074699965534787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731423904199199908092765 649283964074699965534787)
                      ·
                        rfl

theorem cell23_1264476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1264476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264476 prefixEnd_1264476 := by exact prefixLift 1264476
  have htrace : WordTrace (prefixWord ++ tailWord_1264476) baseStart_1264476 baseEnd_1264476 := by
    simpa [prefixWord, tailWord_1264476, baseEnd_1264476] using wordTrace_append hprefix tailTrace_1264476
  have hstable : (prefixWord ++ tailWord_1264476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264476).length < 2 ^ (prefixWord ++ tailWord_1264476).sum := by decide
  have hdescent : baseEnd_1264476 < baseStart_1264476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264499 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 2, 3, 2]
def baseStart_1264499 : Nat := 118140960795 + 1264499 * 2 ^ 59
def prefixEnd_1264499 : Nat := 4983230072969 + 3 ^ 40 * 1264499 * 2
def baseEnd_1264499 : Nat := 649295774129753375547181

theorem tailTrace_1264499 : CollatzResearch.WordTrace tailWord_1264499 prefixEnd_1264499 649295774129753375547181 := by
  unfold tailWord_1264499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46120067445943557080916551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30746711630629038053944367 46120067445943557080916551)
  ·
    refine ⟨69180101168915335621374827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46120067445943557080916551 69180101168915335621374827)
    ·
      refine ⟨103770151753373003432062241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69180101168915335621374827 103770151753373003432062241)
      ·
        refine ⟨77827613815029752574046681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103770151753373003432062241 77827613815029752574046681)
        ·
          refine ⟨58370710361272314430535011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77827613815029752574046681 58370710361272314430535011)
          ·
            refine ⟨87556065541908471645802517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58370710361272314430535011 87556065541908471645802517)
            ·
              refine ⟨4104190572276959608396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87556065541908471645802517 4104190572276959608396993)
              ·
                refine ⟨3078142929207719706297745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104190572276959608396993 3078142929207719706297745)
                ·
                  refine ⟨2308607196905789779723309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078142929207719706297745 2308607196905789779723309)
                  ·
                    refine ⟨865727698839671167396241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308607196905789779723309 865727698839671167396241)
                    ·
                      refine ⟨649295774129753375547181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865727698839671167396241 649295774129753375547181)
                      ·
                        rfl

theorem cell23_1264499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 3, 2].length) (baseStart_1264499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264499 prefixEnd_1264499 := by exact prefixLift 1264499
  have htrace : WordTrace (prefixWord ++ tailWord_1264499) baseStart_1264499 baseEnd_1264499 := by
    simpa [prefixWord, tailWord_1264499, baseEnd_1264499] using wordTrace_append hprefix tailTrace_1264499
  have hstable : (prefixWord ++ tailWord_1264499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264499).length < 2 ^ (prefixWord ++ tailWord_1264499).sum := by decide
  have hdescent : baseEnd_1264499 < baseStart_1264499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264540 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1264540 : Nat := 118140960795 + 1264540 * 2 ^ 59
def prefixEnd_1264540 : Nat := 4983230072969 + 3 ^ 40 * 1264540 * 2
def baseEnd_1264540 : Nat := 649316826836587715134493

theorem tailTrace_1264540 : CollatzResearch.WordTrace tailWord_1264540 prefixEnd_1264540 649316826836587715134493 := by
  unfold tailWord_1264540
  simp only [CollatzResearch.WordTrace]
  refine ⟨23060781419397510541579537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30747708559196680722106049 23060781419397510541579537)
  ·
    refine ⟨17295586064548132906184653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23060781419397510541579537 17295586064548132906184653)
    ·
      refine ⟨6485844774205549839819245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17295586064548132906184653 6485844774205549839819245)
      ·
        refine ⟨2432191790327081189932217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6485844774205549839819245 2432191790327081189932217)
        ·
          refine ⟨1824143842745310892449163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432191790327081189932217 1824143842745310892449163)
          ·
            refine ⟨2736215764117966338673745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824143842745310892449163 2736215764117966338673745)
            ·
              refine ⟨2052161823088474754005309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736215764117966338673745 2052161823088474754005309)
              ·
                refine ⟨769560683658178032751991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052161823088474754005309 769560683658178032751991)
                ·
                  refine ⟨1154341025487267049127987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769560683658178032751991 1154341025487267049127987)
                  ·
                    refine ⟨1731511538230900573691981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154341025487267049127987 1731511538230900573691981)
                    ·
                      refine ⟨649316826836587715134493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731511538230900573691981 649316826836587715134493)
                      ·
                        rfl

theorem cell23_1264540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1264540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264540 prefixEnd_1264540 := by exact prefixLift 1264540
  have htrace : WordTrace (prefixWord ++ tailWord_1264540) baseStart_1264540 baseEnd_1264540 := by
    simpa [prefixWord, tailWord_1264540, baseEnd_1264540] using wordTrace_append hprefix tailTrace_1264540
  have hstable : (prefixWord ++ tailWord_1264540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264540).length < 2 ^ (prefixWord ++ tailWord_1264540).sum := by decide
  have hdescent : baseEnd_1264540 < baseStart_1264540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264546 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1264546 : Nat := 118140960795 + 1264546 * 2 ^ 59
def prefixEnd_1264546 : Nat := 4983230072969 + 3 ^ 40 * 1264546 * 2
def baseEnd_1264546 : Nat := 649319907720514691659465

theorem tailTrace_1264546 : CollatzResearch.WordTrace tailWord_1264546 prefixEnd_1264546 649319907720514691659465 := by
  unfold tailWord_1264546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530445419193321026969373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30747854451182189405251661 11530445419193321026969373)
  ·
    refine ⟨4323917032197495385113515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11530445419193321026969373 4323917032197495385113515)
    ·
      refine ⟨6485875548296243077670273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323917032197495385113515 6485875548296243077670273)
      ·
        refine ⟨4864406661222182308252705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6485875548296243077670273 4864406661222182308252705)
        ·
          refine ⟨3648304995916636731189529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864406661222182308252705 3648304995916636731189529)
          ·
            refine ⟨2736228746937477548392147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648304995916636731189529 2736228746937477548392147)
            ·
              refine ⟨4104343120406216322588221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736228746937477548392147 4104343120406216322588221)
              ·
                refine ⟨1539128670152331120970583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4104343120406216322588221 1539128670152331120970583)
                ·
                  refine ⟨2308693005228496681455875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539128670152331120970583 2308693005228496681455875)
                  ·
                    refine ⟨3463039507842745022183813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308693005228496681455875 3463039507842745022183813)
                    ·
                      refine ⟨649319907720514691659465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3463039507842745022183813 649319907720514691659465)
                      ·
                        rfl

theorem cell23_1264546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1264546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264546 prefixEnd_1264546 := by exact prefixLift 1264546
  have htrace : WordTrace (prefixWord ++ tailWord_1264546) baseStart_1264546 baseEnd_1264546 := by
    simpa [prefixWord, tailWord_1264546, baseEnd_1264546] using wordTrace_append hprefix tailTrace_1264546
  have hstable : (prefixWord ++ tailWord_1264546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264546).length < 2 ^ (prefixWord ++ tailWord_1264546).sum := by decide
  have hdescent : baseEnd_1264546 < baseStart_1264546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264562 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1264562 : Nat := 118140960795 + 1264562 * 2 ^ 59
def prefixEnd_1264562 : Nat := 4983230072969 + 3 ^ 40 * 1264562 * 2
def baseEnd_1264562 : Nat := 649328123410986629059391

theorem tailTrace_1264562 : CollatzResearch.WordTrace tailWord_1264562 prefixEnd_1264562 649328123410986629059391 := by
  unfold tailWord_1264562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530591311178829710114985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30748243496476879226973293 11530591311178829710114985)
  ·
    refine ⟨8647943483384122282586239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11530591311178829710114985 8647943483384122282586239)
    ·
      refine ⟨12971915225076183423879359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8647943483384122282586239 12971915225076183423879359)
      ·
        refine ⟨19457872837614275135819039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12971915225076183423879359 19457872837614275135819039)
        ·
          refine ⟨29186809256421412703728559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19457872837614275135819039 29186809256421412703728559)
          ·
            refine ⟨43780213884632119055592839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29186809256421412703728559 43780213884632119055592839)
            ·
              refine ⟨65670320826948178583389259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43780213884632119055592839 65670320826948178583389259)
              ·
                refine ⟨98505481240422267875083889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65670320826948178583389259 98505481240422267875083889)
                ·
                  refine ⟨73879110930316700906312917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98505481240422267875083889 73879110930316700906312917)
                  ·
                    refine ⟨1731541662429297677491709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73879110930316700906312917 1731541662429297677491709)
                    ·
                      refine ⟨649328123410986629059391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731541662429297677491709 649328123410986629059391)
                      ·
                        rfl

theorem cell23_1264562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1264562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264562 prefixEnd_1264562 := by exact prefixLift 1264562
  have htrace : WordTrace (prefixWord ++ tailWord_1264562) baseStart_1264562 baseEnd_1264562 := by
    simpa [prefixWord, tailWord_1264562, baseEnd_1264562] using wordTrace_append hprefix tailTrace_1264562
  have hstable : (prefixWord ++ tailWord_1264562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264562).length < 2 ^ (prefixWord ++ tailWord_1264562).sum := by decide
  have hdescent : baseEnd_1264562 < baseStart_1264562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264573 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_1264573 : Nat := 118140960795 + 1264573 * 2 ^ 59
def prefixEnd_1264573 : Nat := 4983230072969 + 3 ^ 40 * 1264573 * 2
def baseEnd_1264573 : Nat := 216444590566062028673947

theorem tailTrace_1264573 : CollatzResearch.WordTrace tailWord_1264573 prefixEnd_1264573 216444590566062028673947 := by
  unfold tailWord_1264573
  simp only [CollatzResearch.WordTrace]
  refine ⟨46122766447675467719110373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30748510965116978479406915 46122766447675467719110373)
  ·
    refine ⟨8648018708939150197333195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46122766447675467719110373 8648018708939150197333195)
    ·
      refine ⟨12972028063408725295999793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648018708939150197333195 12972028063408725295999793)
      ·
        refine ⟨9729021047556543971999845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12972028063408725295999793 9729021047556543971999845)
        ·
          refine ⟨1824191446416851994749971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9729021047556543971999845 1824191446416851994749971)
          ·
            refine ⟨2736287169625277992124957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824191446416851994749971 2736287169625277992124957)
            ·
              refine ⟨1026107688609479247046859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2736287169625277992124957 1026107688609479247046859)
              ·
                refine ⟨1539161532914218870570289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026107688609479247046859 1539161532914218870570289)
                ·
                  refine ⟨1154371149685664152927717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1539161532914218870570289 1154371149685664152927717)
                  ·
                    refine ⟨216444590566062028673947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154371149685664152927717 216444590566062028673947)
                    ·
                      rfl

theorem cell23_1264573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_1264573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264573 prefixEnd_1264573 := by exact prefixLift 1264573
  have htrace : WordTrace (prefixWord ++ tailWord_1264573) baseStart_1264573 baseEnd_1264573 := by
    simpa [prefixWord, tailWord_1264573, baseEnd_1264573] using wordTrace_append hprefix tailTrace_1264573
  have hstable : (prefixWord ++ tailWord_1264573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264573).length < 2 ^ (prefixWord ++ tailWord_1264573).sum := by decide
  have hdescent : baseEnd_1264573 < baseStart_1264573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264596 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1264596 : Nat := 118140960795 + 1264596 * 2 ^ 59
def prefixEnd_1264596 : Nat := 4983230072969 + 3 ^ 40 * 1264596 * 2
def baseEnd_1264596 : Nat := 649345581753239496034235

theorem tailTrace_1264596 : CollatzResearch.WordTrace tailWord_1264596 prefixEnd_1264596 649345581753239496034235 := by
  unfold tailWord_1264596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061802663296071323598821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30749070217728095098131761 23061802663296071323598821)
  ·
    refine ⟨4324087999368013373174779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23061802663296071323598821 4324087999368013373174779)
    ·
      refine ⟨6486131999052020059762169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324087999368013373174779 6486131999052020059762169)
      ·
        refine ⟨4864598999289015044821627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486131999052020059762169 4864598999289015044821627)
        ·
          refine ⟨7296898498933522567232441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4864598999289015044821627 7296898498933522567232441)
          ·
            refine ⟨5472673874200141925424331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7296898498933522567232441 5472673874200141925424331)
            ·
              refine ⟨8209010811300212888136497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472673874200141925424331 8209010811300212888136497)
              ·
                refine ⟨6156758108475159666102373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209010811300212888136497 6156758108475159666102373)
                ·
                  refine ⟨1154392145339092437394195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6156758108475159666102373 1154392145339092437394195)
                  ·
                    refine ⟨1731588218008638656091293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154392145339092437394195 1731588218008638656091293)
                    ·
                      refine ⟨649345581753239496034235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731588218008638656091293 649345581753239496034235)
                      ·
                        rfl

theorem cell23_1264596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1264596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264596 prefixEnd_1264596 := by exact prefixLift 1264596
  have htrace : WordTrace (prefixWord ++ tailWord_1264596) baseStart_1264596 baseEnd_1264596 := by
    simpa [prefixWord, tailWord_1264596, baseEnd_1264596] using wordTrace_append hprefix tailTrace_1264596
  have hstable : (prefixWord ++ tailWord_1264596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264596).length < 2 ^ (prefixWord ++ tailWord_1264596).sum := by decide
  have hdescent : baseEnd_1264596 < baseStart_1264596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264597 : List Nat := [1, 3, 2, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1264597 : Nat := 118140960795 + 1264597 * 2 ^ 59
def prefixEnd_1264597 : Nat := 4983230072969 + 3 ^ 40 * 1264597 * 2
def baseEnd_1264597 : Nat := 649346095233893992121731

theorem tailTrace_1264597 : CollatzResearch.WordTrace tailWord_1264597 prefixEnd_1264597 649346095233893992121731 := by
  unfold tailWord_1264597
  simp only [CollatzResearch.WordTrace]
  refine ⟨46123641799588519817984045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30749094533059013211989363 46123641799588519817984045)
  ·
    refine ⟨17296365674845694931744017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46123641799588519817984045 17296365674845694931744017)
    ·
      refine ⟨12972274256134271198808013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17296365674845694931744017 12972274256134271198808013)
      ·
        refine ⟨4864602846050351699553005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12972274256134271198808013 4864602846050351699553005)
        ·
          refine ⟨1824226067268881887332377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4864602846050351699553005 1824226067268881887332377)
          ·
            refine ⟨1368169550451661415499283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824226067268881887332377 1368169550451661415499283)
            ·
              refine ⟨2052254325677492123248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368169550451661415499283 2052254325677492123248925)
              ·
                refine ⟨769595372129059546218347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052254325677492123248925 769595372129059546218347)
                ·
                  refine ⟨1154393058193589319327521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769595372129059546218347 1154393058193589319327521)
                  ·
                    refine ⟨865794793645191989495641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1154393058193589319327521 865794793645191989495641)
                    ·
                      refine ⟨649346095233893992121731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865794793645191989495641 649346095233893992121731)
                      ·
                        rfl

theorem cell23_1264597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1264597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264597 prefixEnd_1264597 := by exact prefixLift 1264597
  have htrace : WordTrace (prefixWord ++ tailWord_1264597) baseStart_1264597 baseEnd_1264597 := by
    simpa [prefixWord, tailWord_1264597, baseEnd_1264597] using wordTrace_append hprefix tailTrace_1264597
  have hstable : (prefixWord ++ tailWord_1264597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264597).length < 2 ^ (prefixWord ++ tailWord_1264597).sum := by decide
  have hdescent : baseEnd_1264597 < baseStart_1264597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264612 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1264612 : Nat := 118140960795 + 1264612 * 2 ^ 59
def prefixEnd_1264612 : Nat := 4983230072969 + 3 ^ 40 * 1264612 * 2
def baseEnd_1264612 : Nat := 216451265814570477811387

theorem tailTrace_1264612 : CollatzResearch.WordTrace tailWord_1264612 prefixEnd_1264612 216451265814570477811387 := by
  unfold tailWord_1264612
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062094447267088689890045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30749459263022784919853393 23062094447267088689890045)
  ·
    refine ⟨8648285417725158258708767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23062094447267088689890045 8648285417725158258708767)
    ·
      refine ⟨12972428126587737388063151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648285417725158258708767 12972428126587737388063151)
      ·
        refine ⟨19458642189881606082094727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12972428126587737388063151 19458642189881606082094727)
        ·
          refine ⟨29187963284822409123142091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19458642189881606082094727 29187963284822409123142091)
          ·
            refine ⟨43781944927233613684713137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29187963284822409123142091 43781944927233613684713137)
            ·
              refine ⟨32836458695425210263534853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43781944927233613684713137 32836458695425210263534853)
              ·
                refine ⟨6156836005392226924412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32836458695425210263534853 6156836005392226924412785)
                ·
                  refine ⟨4617627004044170193309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6156836005392226924412785 4617627004044170193309589)
                  ·
                    refine ⟨216451265814570477811387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4617627004044170193309589 216451265814570477811387)
                    ·
                      rfl

theorem cell23_1264612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1264612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264612 prefixEnd_1264612 := by exact prefixLift 1264612
  have htrace : WordTrace (prefixWord ++ tailWord_1264612) baseStart_1264612 baseEnd_1264612 := by
    simpa [prefixWord, tailWord_1264612, baseEnd_1264612] using wordTrace_append hprefix tailTrace_1264612
  have hstable : (prefixWord ++ tailWord_1264612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264612).length < 2 ^ (prefixWord ++ tailWord_1264612).sum := by decide
  have hdescent : baseEnd_1264612 < baseStart_1264612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264630 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1264630 : Nat := 118140960795 + 1264630 * 2 ^ 59
def prefixEnd_1264630 : Nat := 4983230072969 + 3 ^ 40 * 1264630 * 2
def baseEnd_1264630 : Nat := 649363040095492363009079

theorem tailTrace_1264630 : CollatzResearch.WordTrace tailWord_1264630 prefixEnd_1264630 649363040095492363009079 := by
  unfold tailWord_1264630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882802838029310403370959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30749896938979310969290229 2882802838029310403370959)
  ·
    refine ⟨4324204257043965605056439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882802838029310403370959 4324204257043965605056439)
    ·
      refine ⟨6486306385565948407584659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324204257043965605056439 6486306385565948407584659)
      ·
        refine ⟨9729459578348922611376989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486306385565948407584659 9729459578348922611376989)
        ·
          refine ⟨3648547341880845979266371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9729459578348922611376989 3648547341880845979266371)
          ·
            refine ⟨5472821012821268968899557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648547341880845979266371 5472821012821268968899557)
            ·
              refine ⟨1026153939903987931668667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5472821012821268968899557 1026153939903987931668667)
              ·
                refine ⟨1539230909855981897503001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026153939903987931668667 1539230909855981897503001)
                ·
                  refine ⟨1154423182391986423127251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1539230909855981897503001 1154423182391986423127251)
                  ·
                    refine ⟨1731634773587979634690877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154423182391986423127251 1731634773587979634690877)
                    ·
                      refine ⟨649363040095492363009079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731634773587979634690877 649363040095492363009079)
                      ·
                        rfl

theorem cell23_1264630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1264630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264630 prefixEnd_1264630 := by exact prefixLift 1264630
  have htrace : WordTrace (prefixWord ++ tailWord_1264630) baseStart_1264630 baseEnd_1264630 := by
    simpa [prefixWord, tailWord_1264630, baseEnd_1264630] using wordTrace_append hprefix tailTrace_1264630
  have hstable : (prefixWord ++ tailWord_1264630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264630).length < 2 ^ (prefixWord ++ tailWord_1264630).sum := by decide
  have hdescent : baseEnd_1264630 < baseStart_1264630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264632 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1264632 : Nat := 118140960795 + 1264632 * 2 ^ 59
def prefixEnd_1264632 : Nat := 4983230072969 + 3 ^ 40 * 1264632 * 2
def baseEnd_1264632 : Nat := 649364067056801355184069

theorem tailTrace_1264632 : CollatzResearch.WordTrace tailWord_1264632 prefixEnd_1264632 649364067056801355184069 := by
  unfold tailWord_1264632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062459177230860397754075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30749945569641147197005433 23062459177230860397754075)
  ·
    refine ⟨34593688765846290596631113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23062459177230860397754075 34593688765846290596631113)
    ·
      refine ⟨25945266574384717947473335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34593688765846290596631113 25945266574384717947473335)
      ·
        refine ⟨38917899861577076921210003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25945266574384717947473335 38917899861577076921210003)
        ·
          refine ⟨58376849792365615381815005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38917899861577076921210003 58376849792365615381815005)
          ·
            refine ⟨21891318672137105768180627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58376849792365615381815005 21891318672137105768180627)
            ·
              refine ⟨32836978008205658652270941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21891318672137105768180627 32836978008205658652270941)
              ·
                refine ⟨12313866753077121994601603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32836978008205658652270941 12313866753077121994601603)
                ·
                  refine ⟨18470800129615682991902405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12313866753077121994601603 18470800129615682991902405)
                  ·
                    refine ⟨3463275024302940560981701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18470800129615682991902405 3463275024302940560981701)
                    ·
                      refine ⟨649364067056801355184069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3463275024302940560981701 649364067056801355184069)
                      ·
                        rfl

theorem cell23_1264632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1264632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264632 prefixEnd_1264632 := by exact prefixLift 1264632
  have htrace : WordTrace (prefixWord ++ tailWord_1264632) baseStart_1264632 baseEnd_1264632 := by
    simpa [prefixWord, tailWord_1264632, baseEnd_1264632] using wordTrace_append hprefix tailTrace_1264632
  have hstable : (prefixWord ++ tailWord_1264632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264632).length < 2 ^ (prefixWord ++ tailWord_1264632).sum := by decide
  have hdescent : baseEnd_1264632 < baseStart_1264632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264659 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 5]
def baseStart_1264659 : Nat := 118140960795 + 1264659 * 2 ^ 59
def prefixEnd_1264659 : Nat := 4983230072969 + 3 ^ 40 * 1264659 * 2
def baseEnd_1264659 : Nat := 72153103448274749949605

theorem tailTrace_1264659 : CollatzResearch.WordTrace tailWord_1264659 prefixEnd_1264659 72153103448274749949605 := by
  unfold tailWord_1264659
  simp only [CollatzResearch.WordTrace]
  refine ⟨46125903125363904406741031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30750602083575936271160687 46125903125363904406741031)
  ·
    refine ⟨69188854688045856610111547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46125903125363904406741031 69188854688045856610111547)
    ·
      refine ⟨103783282032068784915167321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69188854688045856610111547 103783282032068784915167321)
      ·
        refine ⟨77837461524051588686375491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103783282032068784915167321 77837461524051588686375491)
        ·
          refine ⟨116756192286077383029563237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77837461524051588686375491 116756192286077383029563237)
          ·
            refine ⟨21891786053639509318043107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116756192286077383029563237 21891786053639509318043107)
            ·
              refine ⟨32837679080459263977064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21891786053639509318043107 32837679080459263977064661)
              ·
                refine ⟨769633103448263999462453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32837679080459263977064661 769633103448263999462453)
                ·
                  refine ⟨72153103448274749949605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769633103448263999462453 72153103448274749949605)
                  ·
                    rfl

theorem cell23_1264659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 5].length) (baseStart_1264659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264659 prefixEnd_1264659 := by exact prefixLift 1264659
  have htrace : WordTrace (prefixWord ++ tailWord_1264659) baseStart_1264659 baseEnd_1264659 := by
    simpa [prefixWord, tailWord_1264659, baseEnd_1264659] using wordTrace_append hprefix tailTrace_1264659
  have hstable : (prefixWord ++ tailWord_1264659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264659).length < 2 ^ (prefixWord ++ tailWord_1264659).sum := by decide
  have hdescent : baseEnd_1264659 < baseStart_1264659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264686 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1264686 : Nat := 118140960795 + 1264686 * 2 ^ 59
def prefixEnd_1264686 : Nat := 4983230072969 + 3 ^ 40 * 1264686 * 2
def baseEnd_1264686 : Nat := 649391795012144143908821

theorem tailTrace_1264686 : CollatzResearch.WordTrace tailWord_1264686 prefixEnd_1264686 649391795012144143908821 := by
  unfold tailWord_1264686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765860987033261002246739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30751258597510725345315941 5765860987033261002246739)
  ·
    refine ⟨8648791480549891503370109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765860987033261002246739 8648791480549891503370109)
    ·
      refine ⟨3243296805206209313763791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8648791480549891503370109 3243296805206209313763791)
      ·
        refine ⟨4864945207809313970645687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243296805206209313763791 4864945207809313970645687)
        ·
          refine ⟨7297417811713970955968531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4864945207809313970645687 7297417811713970955968531)
          ·
            refine ⟨10946126717570956433952797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297417811713970955968531 10946126717570956433952797)
            ·
              refine ⟨4104797519089108662732299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10946126717570956433952797 4104797519089108662732299)
              ·
                refine ⟨6157196278633662994098449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104797519089108662732299 6157196278633662994098449)
                ·
                  refine ⟨4617897208975247245573837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157196278633662994098449 4617897208975247245573837)
                  ·
                    refine ⟨1731711453365717717090189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4617897208975247245573837 1731711453365717717090189)
                    ·
                      refine ⟨649391795012144143908821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731711453365717717090189 649391795012144143908821)
                      ·
                        rfl

theorem cell23_1264686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1264686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264686 prefixEnd_1264686 := by exact prefixLift 1264686
  have htrace : WordTrace (prefixWord ++ tailWord_1264686) baseStart_1264686 baseEnd_1264686 := by
    simpa [prefixWord, tailWord_1264686, baseEnd_1264686] using wordTrace_append hprefix tailTrace_1264686
  have hstable : (prefixWord ++ tailWord_1264686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264686).length < 2 ^ (prefixWord ++ tailWord_1264686).sum := by decide
  have hdescent : baseEnd_1264686 < baseStart_1264686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264710 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1264710 : Nat := 118140960795 + 1264710 * 2 ^ 59
def prefixEnd_1264710 : Nat := 4983230072969 + 3 ^ 40 * 1264710 * 2
def baseEnd_1264710 : Nat := 72156013171983561112079

theorem tailTrace_1264710 : CollatzResearch.WordTrace tailWord_1264710 prefixEnd_1264710 72156013171983561112079 := by
  unfold tailWord_1264710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441492601505598128651487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30751842165452760077898389 1441492601505598128651487)
  ·
    refine ⟨2162238902258397192977231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441492601505598128651487 2162238902258397192977231)
    ·
      refine ⟨3243358353387595789465847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162238902258397192977231 3243358353387595789465847)
      ·
        refine ⟨4865037530081393684198771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243358353387595789465847 4865037530081393684198771)
        ·
          refine ⟨7297556295122090526298157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865037530081393684198771 7297556295122090526298157)
          ·
            refine ⟨2736583610670783947361809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7297556295122090526298157 2736583610670783947361809)
            ·
              refine ⟨2052437708003087960521357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736583610670783947361809 2052437708003087960521357)
              ·
                refine ⟨769664140501157985195509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2052437708003087960521357 769664140501157985195509)
                ·
                  refine ⟨72156013171983561112079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 769664140501157985195509 72156013171983561112079)
                  ·
                    rfl

theorem cell23_1264710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1264710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264710 prefixEnd_1264710 := by exact prefixLift 1264710
  have htrace : WordTrace (prefixWord ++ tailWord_1264710) baseStart_1264710 baseEnd_1264710 := by
    simpa [prefixWord, tailWord_1264710, baseEnd_1264710] using wordTrace_append hprefix tailTrace_1264710
  have hstable : (prefixWord ++ tailWord_1264710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264710).length < 2 ^ (prefixWord ++ tailWord_1264710).sum := by decide
  have hdescent : baseEnd_1264710 < baseStart_1264710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264736 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_1264736 : Nat := 118140960795 + 1264736 * 2 ^ 59
def prefixEnd_1264736 : Nat := 4983230072969 + 3 ^ 40 * 1264736 * 2
def baseEnd_1264736 : Nat := 216472489681622982761197

theorem tailTrace_1264736 : CollatzResearch.WordTrace tailWord_1264736 prefixEnd_1264736 216472489681622982761197 := by
  unfold tailWord_1264736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23064355773042473278647031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30752474364056631038196041 23064355773042473278647031)
  ·
    refine ⟨34596533659563709917970547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23064355773042473278647031 34596533659563709917970547)
    ·
      refine ⟨51894800489345564876955821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34596533659563709917970547 51894800489345564876955821)
      ·
        refine ⟨19460550183504586828858433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51894800489345564876955821 19460550183504586828858433)
        ·
          refine ⟨14595412637628440121643825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19460550183504586828858433 14595412637628440121643825)
          ·
            refine ⟨10946559478221330091232869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14595412637628440121643825 10946559478221330091232869)
            ·
              refine ⟨2052479902166499392106163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10946559478221330091232869 2052479902166499392106163)
              ·
                refine ⟨3078719853249749088159245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052479902166499392106163 3078719853249749088159245)
                ·
                  refine ⟨1154519944968655908059717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3078719853249749088159245 1154519944968655908059717)
                  ·
                    refine ⟨216472489681622982761197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154519944968655908059717 216472489681622982761197)
                    ·
                      rfl

theorem cell23_1264736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_1264736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264736 prefixEnd_1264736 := by exact prefixLift 1264736
  have htrace : WordTrace (prefixWord ++ tailWord_1264736) baseStart_1264736 baseEnd_1264736 := by
    simpa [prefixWord, tailWord_1264736, baseEnd_1264736] using wordTrace_append hprefix tailTrace_1264736
  have hstable : (prefixWord ++ tailWord_1264736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264736).length < 2 ^ (prefixWord ++ tailWord_1264736).sum := by decide
  have hdescent : baseEnd_1264736 < baseStart_1264736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264746 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1264746 : Nat := 118140960795 + 1264746 * 2 ^ 59
def prefixEnd_1264746 : Nat := 4983230072969 + 3 ^ 40 * 1264746 * 2
def baseEnd_1264746 : Nat := 649422603851413909158545

theorem tailTrace_1264746 : CollatzResearch.WordTrace tailWord_1264746 prefixEnd_1264746 649422603851413909158545 := by
  unfold tailWord_1264746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11532269069012179566289523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30752717517365812176772061 11532269069012179566289523)
  ·
    refine ⟨17298403603518269349434285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11532269069012179566289523 17298403603518269349434285)
    ·
      refine ⟨6486901351319351006037857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17298403603518269349434285 6486901351319351006037857)
      ·
        refine ⟨4865176013489513254528393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486901351319351006037857 4865176013489513254528393)
        ·
          refine ⟨3648882010117134940896295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865176013489513254528393 3648882010117134940896295)
          ·
            refine ⟨5473323015175702411344443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648882010117134940896295 5473323015175702411344443)
            ·
              refine ⟨8209984522763553617016665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473323015175702411344443 8209984522763553617016665)
              ·
                refine ⟨6157488392072665212762499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209984522763553617016665 6157488392072665212762499)
                ·
                  refine ⟨9236232588108997819143749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157488392072665212762499 9236232588108997819143749)
                  ·
                    refine ⟨1731793610270437091089453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9236232588108997819143749 1731793610270437091089453)
                    ·
                      refine ⟨649422603851413909158545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731793610270437091089453 649422603851413909158545)
                      ·
                        rfl

theorem cell23_1264746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1264746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264746 prefixEnd_1264746 := by exact prefixLift 1264746
  have htrace : WordTrace (prefixWord ++ tailWord_1264746) baseStart_1264746 baseEnd_1264746 := by
    simpa [prefixWord, tailWord_1264746, baseEnd_1264746] using wordTrace_append hprefix tailTrace_1264746
  have hstable : (prefixWord ++ tailWord_1264746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264746).length < 2 ^ (prefixWord ++ tailWord_1264746).sum := by decide
  have hdescent : baseEnd_1264746 < baseStart_1264746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264759 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_1264759 : Nat := 118140960795 + 1264759 * 2 ^ 59
def prefixEnd_1264759 : Nat := 4983230072969 + 3 ^ 40 * 1264759 * 2
def baseEnd_1264759 : Nat := 649429279099922358295985

theorem tailTrace_1264759 : CollatzResearch.WordTrace tailWord_1264759 prefixEnd_1264759 649429279099922358295985 := by
  unfold tailWord_1264759
  simp only [CollatzResearch.WordTrace]
  refine ⟨46129550425001621485381331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30753033616667747656920887 46129550425001621485381331)
  ·
    refine ⟨69194325637502432228071997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46129550425001621485381331 69194325637502432228071997)
    ·
      refine ⟨25947872114063412085526999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69194325637502432228071997 25947872114063412085526999)
      ·
        refine ⟨38921808171095118128290499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25947872114063412085526999 38921808171095118128290499)
        ·
          refine ⟨58382712256642677192435749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38921808171095118128290499 58382712256642677192435749)
          ·
            refine ⟨10946758548120501973581703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58382712256642677192435749 10946758548120501973581703)
            ·
              refine ⟨16420137822180752960372555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946758548120501973581703 16420137822180752960372555)
              ·
                refine ⟨24630206733271129440558833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16420137822180752960372555 24630206733271129440558833)
                ·
                  refine ⟨18472655049953347080419125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24630206733271129440558833 18472655049953347080419125)
                  ·
                    refine ⟨1731811410933126288789293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18472655049953347080419125 1731811410933126288789293)
                    ·
                      refine ⟨649429279099922358295985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731811410933126288789293 649429279099922358295985)
                      ·
                        rfl

theorem cell23_1264759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_1264759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264759 prefixEnd_1264759 := by exact prefixLift 1264759
  have htrace : WordTrace (prefixWord ++ tailWord_1264759) baseStart_1264759 baseEnd_1264759 := by
    simpa [prefixWord, tailWord_1264759, baseEnd_1264759] using wordTrace_append hprefix tailTrace_1264759
  have hstable : (prefixWord ++ tailWord_1264759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264759).length < 2 ^ (prefixWord ++ tailWord_1264759).sum := by decide
  have hdescent : baseEnd_1264759 < baseStart_1264759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264813 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1264813 : Nat := 118140960795 + 1264813 * 2 ^ 59
def prefixEnd_1264813 : Nat := 4983230072969 + 3 ^ 40 * 1264813 * 2
def baseEnd_1264813 : Nat := 216485669018421715673579

theorem tailTrace_1264813 : CollatzResearch.WordTrace tailWord_1264813 prefixEnd_1264813 216485669018421715673579 := by
  unfold tailWord_1264813
  simp only [CollatzResearch.WordTrace]
  refine ⟨46131519966805988707847093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30754346644537325805231395 46131519966805988707847093)
  ·
    refine ⟨4324829996888061441360665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46131519966805988707847093 4324829996888061441360665)
    ·
      refine ⟨3243622497666046081020499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4324829996888061441360665 3243622497666046081020499)
      ·
        refine ⟨4865433746499069121530749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3243622497666046081020499 4865433746499069121530749)
        ·
          refine ⟨1824537654937150920574031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4865433746499069121530749 1824537654937150920574031)
          ·
            refine ⟨2736806482405726380861047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824537654937150920574031 2736806482405726380861047)
            ·
              refine ⟨4105209723608589571291571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736806482405726380861047 4105209723608589571291571)
              ·
                refine ⟨6157814585412884356937357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105209723608589571291571 6157814585412884356937357)
                ·
                  refine ⟨2309180469529831633851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6157814585412884356937357 2309180469529831633851509)
                  ·
                    refine ⟨216485669018421715673579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2309180469529831633851509 216485669018421715673579)
                    ·
                      rfl

theorem cell23_1264813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1264813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264813 prefixEnd_1264813 := by exact prefixLift 1264813
  have htrace : WordTrace (prefixWord ++ tailWord_1264813) baseStart_1264813 baseEnd_1264813 := by
    simpa [prefixWord, tailWord_1264813, baseEnd_1264813] using wordTrace_append hprefix tailTrace_1264813
  have hstable : (prefixWord ++ tailWord_1264813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264813).length < 2 ^ (prefixWord ++ tailWord_1264813).sum := by decide
  have hdescent : baseEnd_1264813 < baseStart_1264813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264819 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5]
def baseStart_1264819 : Nat := 118140960795 + 1264819 * 2 ^ 59
def prefixEnd_1264819 : Nat := 4983230072969 + 3 ^ 40 * 1264819 * 2
def baseEnd_1264819 : Nat := 649460087939192123545709

theorem tailTrace_1264819 : CollatzResearch.WordTrace tailWord_1264819 prefixEnd_1264819 649460087939192123545709 := by
  unfold tailWord_1264819
  simp only [CollatzResearch.WordTrace]
  refine ⟨46131738804784251732565511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30754492536522834488377007 46131738804784251732565511)
  ·
    refine ⟨69197608207176377598848267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46131738804784251732565511 69197608207176377598848267)
    ·
      refine ⟨103796412310764566398272401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69197608207176377598848267 103796412310764566398272401)
      ·
        refine ⟨77847309233073424798704301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103796412310764566398272401 77847309233073424798704301)
        ·
          refine ⟨29192740962402534299514113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77847309233073424798704301 29192740962402534299514113)
          ·
            refine ⟨21894555721801900724635585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29192740962402534299514113 21894555721801900724635585)
            ·
              refine ⟨16420916791351425543476689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21894555721801900724635585 16420916791351425543476689)
              ·
                refine ⟨12315687593513569157607517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16420916791351425543476689 12315687593513569157607517)
                ·
                  refine ⟨4618382847567588434102819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12315687593513569157607517 4618382847567588434102819)
                  ·
                    refine ⟨6927574271351382651154229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618382847567588434102819 6927574271351382651154229)
                    ·
                      refine ⟨649460087939192123545709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6927574271351382651154229 649460087939192123545709)
                      ·
                        rfl

theorem cell23_1264819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_1264819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264819 prefixEnd_1264819 := by exact prefixLift 1264819
  have htrace : WordTrace (prefixWord ++ tailWord_1264819) baseStart_1264819 baseEnd_1264819 := by
    simpa [prefixWord, tailWord_1264819, baseEnd_1264819] using wordTrace_append hprefix tailTrace_1264819
  have hstable : (prefixWord ++ tailWord_1264819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264819).length < 2 ^ (prefixWord ++ tailWord_1264819).sum := by decide
  have hdescent : baseEnd_1264819 < baseStart_1264819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264830 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1264830 : Nat := 118140960795 + 1264830 * 2 ^ 59
def prefixEnd_1264830 : Nat := 4983230072969 + 3 ^ 40 * 1264830 * 2
def baseEnd_1264830 : Nat := 216488578742130526836053

theorem tailTrace_1264830 : CollatzResearch.WordTrace tailWord_1264830 prefixEnd_1264830 216488578742130526836053 := by
  unfold tailWord_1264830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766517500968050076401993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30754760005162933740810629 5766517500968050076401993)
  ·
    refine ⟨4324888125726037557301495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766517500968050076401993 4324888125726037557301495)
    ·
      refine ⟨6487332188589056335952243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324888125726037557301495 6487332188589056335952243)
      ·
        refine ⟨9730998282883584503928365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487332188589056335952243 9730998282883584503928365)
        ·
          refine ⟨3649124356081344188973137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9730998282883584503928365 3649124356081344188973137)
          ·
            refine ⟨2736843267061008141729853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649124356081344188973137 2736843267061008141729853)
            ·
              refine ⟨1026316225147878053148695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2736843267061008141729853 1026316225147878053148695)
              ·
                refine ⟨1539474337721817079723043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026316225147878053148695 1539474337721817079723043)
                ·
                  refine ⟨2309211506582725619584565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539474337721817079723043 2309211506582725619584565)
                  ·
                    refine ⟨216488578742130526836053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2309211506582725619584565 216488578742130526836053)
                    ·
                      rfl

theorem cell23_1264830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1264830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264830 prefixEnd_1264830 := by exact prefixLift 1264830
  have htrace : WordTrace (prefixWord ++ tailWord_1264830) baseStart_1264830 baseEnd_1264830 := by
    simpa [prefixWord, tailWord_1264830, baseEnd_1264830] using wordTrace_append hprefix tailTrace_1264830
  have hstable : (prefixWord ++ tailWord_1264830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264830).length < 2 ^ (prefixWord ++ tailWord_1264830).sum := by decide
  have hdescent : baseEnd_1264830 < baseStart_1264830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264838 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1264838 : Nat := 118140960795 + 1264838 * 2 ^ 59
def prefixEnd_1264838 : Nat := 4983230072969 + 3 ^ 40 * 1264838 * 2
def baseEnd_1264838 : Nat := 216489948023875849736041

theorem tailTrace_1264838 : CollatzResearch.WordTrace tailWord_1264838 prefixEnd_1264838 216489948023875849736041 := by
  unfold tailWord_1264838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441638493491106811797099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30754954527810278651671445 1441638493491106811797099)
  ·
    refine ⟨2162457740236660217695649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441638493491106811797099 2162457740236660217695649)
    ·
      refine ⟨1621843305177495163271737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162457740236660217695649 1621843305177495163271737)
      ·
        refine ⟨1216382478883121372453803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621843305177495163271737 1216382478883121372453803)
        ·
          refine ⟨1824573718324682058680705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216382478883121372453803 1824573718324682058680705)
          ·
            refine ⟨1368430288743511544010529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1824573718324682058680705 1368430288743511544010529)
            ·
              refine ⟨1026322716557633658007897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368430288743511544010529 1026322716557633658007897)
              ·
                refine ⟨769742037418225243505923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026322716557633658007897 769742037418225243505923)
                ·
                  refine ⟨1154613056127337865258885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769742037418225243505923 1154613056127337865258885)
                  ·
                    refine ⟨216489948023875849736041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1154613056127337865258885 216489948023875849736041)
                    ·
                      rfl

theorem cell23_1264838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1264838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264838 prefixEnd_1264838 := by exact prefixLift 1264838
  have htrace : WordTrace (prefixWord ++ tailWord_1264838) baseStart_1264838 baseEnd_1264838 := by
    simpa [prefixWord, tailWord_1264838, baseEnd_1264838] using wordTrace_append hprefix tailTrace_1264838
  have hstable : (prefixWord ++ tailWord_1264838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264838).length < 2 ^ (prefixWord ++ tailWord_1264838).sum := by decide
  have hdescent : baseEnd_1264838 < baseStart_1264838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264850 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1264850 : Nat := 118140960795 + 1264850 * 2 ^ 59
def prefixEnd_1264850 : Nat := 4983230072969 + 3 ^ 40 * 1264850 * 2
def baseEnd_1264850 : Nat := 649476005839481502258067

theorem tailTrace_1264850 : CollatzResearch.WordTrace tailWord_1264850 prefixEnd_1264850 649476005839481502258067 := by
  unfold tailWord_1264850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533217366917986006736001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30755246311781296017962669 11533217366917986006736001)
  ·
    refine ⟨8649913025188489505052001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11533217366917986006736001 8649913025188489505052001)
    ·
      refine ⟨6487434768891367128789001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8649913025188489505052001 6487434768891367128789001)
      ·
        refine ⟨4865576076668525346591751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487434768891367128789001 4865576076668525346591751)
        ·
          refine ⟨7298364115002788019887627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865576076668525346591751 7298364115002788019887627)
          ·
            refine ⟨10947546172504182029831441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298364115002788019887627 10947546172504182029831441)
            ·
              refine ⟨8210659629378136522373581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10947546172504182029831441 8210659629378136522373581)
              ·
                refine ⟨3078997361016801195890093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8210659629378136522373581 3078997361016801195890093)
                ·
                  refine ⟨1154624010381300448458785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3078997361016801195890093 1154624010381300448458785)
                  ·
                    refine ⟨865968007785975336344089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1154624010381300448458785 865968007785975336344089)
                    ·
                      refine ⟨649476005839481502258067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 865968007785975336344089 649476005839481502258067)
                      ·
                        rfl

theorem cell23_1264850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1264850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264850 prefixEnd_1264850 := by exact prefixLift 1264850
  have htrace : WordTrace (prefixWord ++ tailWord_1264850) baseStart_1264850 baseEnd_1264850 := by
    simpa [prefixWord, tailWord_1264850, baseEnd_1264850] using wordTrace_append hprefix tailTrace_1264850
  have hstable : (prefixWord ++ tailWord_1264850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264850).length < 2 ^ (prefixWord ++ tailWord_1264850).sum := by decide
  have hdescent : baseEnd_1264850 < baseStart_1264850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264853 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1264853 : Nat := 118140960795 + 1264853 * 2 ^ 59
def prefixEnd_1264853 : Nat := 4983230072969 + 3 ^ 40 * 1264853 * 2
def baseEnd_1264853 : Nat := 649477546281444990520553

theorem tailTrace_1264853 : CollatzResearch.WordTrace tailWord_1264853 prefixEnd_1264853 649477546281444990520553 := by
  unfold tailWord_1264853
  simp only [CollatzResearch.WordTrace]
  refine ⟨46132978886661075539303213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30755319257774050359535475 46132978886661075539303213)
  ·
    refine ⟨17299867082497903327238705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46132978886661075539303213 17299867082497903327238705)
    ·
      refine ⟨12974900311873427495429029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17299867082497903327238705 12974900311873427495429029)
      ·
        refine ⟨2432793808476267655392943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12974900311873427495429029 2432793808476267655392943)
        ·
          refine ⟨3649190712714401483089415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432793808476267655392943 3649190712714401483089415)
          ·
            refine ⟨5473786069071602224634123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649190712714401483089415 5473786069071602224634123)
            ·
              refine ⟨8210679103607403336951185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473786069071602224634123 8210679103607403336951185)
              ·
                refine ⟨6158009327705552502713389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210679103607403336951185 6158009327705552502713389)
                ·
                  refine ⟨2309253497889582188517521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6158009327705552502713389 2309253497889582188517521)
                  ·
                    refine ⟨1731940123417186641388141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309253497889582188517521 1731940123417186641388141)
                    ·
                      refine ⟨649477546281444990520553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1731940123417186641388141 649477546281444990520553)
                      ·
                        rfl

theorem cell23_1264853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1264853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264853 prefixEnd_1264853 := by exact prefixLift 1264853
  have htrace : WordTrace (prefixWord ++ tailWord_1264853) baseStart_1264853 baseEnd_1264853 := by
    simpa [prefixWord, tailWord_1264853, baseEnd_1264853] using wordTrace_append hprefix tailTrace_1264853
  have hstable : (prefixWord ++ tailWord_1264853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264853).length < 2 ^ (prefixWord ++ tailWord_1264853).sum := by decide
  have hdescent : baseEnd_1264853 < baseStart_1264853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264884 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1264884 : Nat := 118140960795 + 1264884 * 2 ^ 59
def prefixEnd_1264884 : Nat := 4983230072969 + 3 ^ 40 * 1264884 * 2
def baseEnd_1264884 : Nat := 649493464181734369232911

theorem tailTrace_1264884 : CollatzResearch.WordTrace tailWord_1264884 prefixEnd_1264884 649493464181734369232911 := by
  unfold tailWord_1264884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067054774774383916840853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30756073033032511889121137 23067054774774383916840853)
  ·
    refine ⟨1081268192567549246101915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23067054774774383916840853 1081268192567549246101915)
    ·
      refine ⟨1621902288851323869152873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081268192567549246101915 1621902288851323869152873)
      ·
        refine ⟨1216426716638492901864655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621902288851323869152873 1216426716638492901864655)
        ·
          refine ⟨1824640074957739352796983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216426716638492901864655 1824640074957739352796983)
          ·
            refine ⟨2736960112436609029195475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824640074957739352796983 2736960112436609029195475)
            ·
              refine ⟨4105440168654913543793213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736960112436609029195475 4105440168654913543793213)
              ·
                refine ⟨1539540063245592578922455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4105440168654913543793213 1539540063245592578922455)
                ·
                  refine ⟨2309310094868388868383683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539540063245592578922455 2309310094868388868383683)
                  ·
                    refine ⟨3463965142302583302575525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309310094868388868383683 3463965142302583302575525)
                    ·
                      refine ⟨649493464181734369232911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3463965142302583302575525 649493464181734369232911)
                      ·
                        rfl

theorem cell23_1264884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1264884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264884 prefixEnd_1264884 := by exact prefixLift 1264884
  have htrace : WordTrace (prefixWord ++ tailWord_1264884) baseStart_1264884 baseEnd_1264884 := by
    simpa [prefixWord, tailWord_1264884, baseEnd_1264884] using wordTrace_append hprefix tailTrace_1264884
  have hstable : (prefixWord ++ tailWord_1264884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264884).length < 2 ^ (prefixWord ++ tailWord_1264884).sum := by decide
  have hdescent : baseEnd_1264884 < baseStart_1264884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264900 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1264900 : Nat := 118140960795 + 1264900 * 2 ^ 59
def prefixEnd_1264900 : Nat := 4983230072969 + 3 ^ 40 * 1264900 * 2
def baseEnd_1264900 : Nat := 649501679872206306632837

theorem tailTrace_1264900 : CollatzResearch.WordTrace tailWord_1264900 prefixEnd_1264900 649501679872206306632837 := by
  unfold tailWord_1264900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067346558745401283132077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30756462078327201710842769 23067346558745401283132077)
  ·
    refine ⟨8650254959529525481174529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23067346558745401283132077 8650254959529525481174529)
    ·
      refine ⟨6487691219647144110880897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8650254959529525481174529 6487691219647144110880897)
      ·
        refine ⟨4865768414735358083160673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487691219647144110880897 4865768414735358083160673)
        ·
          refine ⟨3649326311051518562370505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865768414735358083160673 3649326311051518562370505)
          ·
            refine ⟨2736994733288638921777879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649326311051518562370505 2736994733288638921777879)
            ·
              refine ⟨4105492099932958382666819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736994733288638921777879 4105492099932958382666819)
              ·
                refine ⟨6158238149899437574000229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105492099932958382666819 6158238149899437574000229)
                ·
                  refine ⟨1154669653106144545125043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6158238149899437574000229 1154669653106144545125043)
                  ·
                    refine ⟨1732004479659216817687565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154669653106144545125043 1732004479659216817687565)
                    ·
                      refine ⟨649501679872206306632837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732004479659216817687565 649501679872206306632837)
                      ·
                        rfl

theorem cell23_1264900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1264900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264900 prefixEnd_1264900 := by exact prefixLift 1264900
  have htrace : WordTrace (prefixWord ++ tailWord_1264900) baseStart_1264900 baseEnd_1264900 := by
    simpa [prefixWord, tailWord_1264900, baseEnd_1264900] using wordTrace_append hprefix tailTrace_1264900
  have hstable : (prefixWord ++ tailWord_1264900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264900).length < 2 ^ (prefixWord ++ tailWord_1264900).sum := by decide
  have hdescent : baseEnd_1264900 < baseStart_1264900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264914 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1264914 : Nat := 118140960795 + 1264914 * 2 ^ 59
def prefixEnd_1264914 : Nat := 4983230072969 + 3 ^ 40 * 1264914 * 2
def baseEnd_1264914 : Nat := 649508868601369251857773

theorem tailTrace_1264914 : CollatzResearch.WordTrace tailWord_1264914 prefixEnd_1264914 649508868601369251857773 := by
  unfold tailWord_1264914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533800934860020739318449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30756802492960055304849197 11533800934860020739318449)
  ·
    refine ⟨8650350701145015554488837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11533800934860020739318449 8650350701145015554488837)
    ·
      refine ⟨1621940756464690416466657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8650350701145015554488837 1621940756464690416466657)
      ·
        refine ⟨1216455567348517812349993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621940756464690416466657 1216455567348517812349993)
        ·
          refine ⟨912341675511388359262495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216455567348517812349993 912341675511388359262495)
          ·
            refine ⟨1368512513267082538893743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912341675511388359262495 1368512513267082538893743)
            ·
              refine ⟨2052768769900623808340615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368512513267082538893743 2052768769900623808340615)
              ·
                refine ⟨3079153154850935712510923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052768769900623808340615 3079153154850935712510923)
                ·
                  refine ⟨4618729732276403568766385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079153154850935712510923 4618729732276403568766385)
                  ·
                    refine ⟨3464047299207302676574789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618729732276403568766385 3464047299207302676574789)
                    ·
                      refine ⟨649508868601369251857773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3464047299207302676574789 649508868601369251857773)
                      ·
                        rfl

theorem cell23_1264914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1264914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264914 prefixEnd_1264914 := by exact prefixLift 1264914
  have htrace : WordTrace (prefixWord ++ tailWord_1264914) baseStart_1264914 baseEnd_1264914 := by
    simpa [prefixWord, tailWord_1264914, baseEnd_1264914] using wordTrace_append hprefix tailTrace_1264914
  have hstable : (prefixWord ++ tailWord_1264914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264914).length < 2 ^ (prefixWord ++ tailWord_1264914).sum := by decide
  have hdescent : baseEnd_1264914 < baseStart_1264914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264927 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 1, 3, 2]
def baseStart_1264927 : Nat := 118140960795 + 1264927 * 2 ^ 59
def prefixEnd_1264927 : Nat := 4983230072969 + 3 ^ 40 * 1264927 * 2
def baseEnd_1264927 : Nat := 649515543849877700995213

theorem tailTrace_1264927 : CollatzResearch.WordTrace tailWord_1264927 prefixEnd_1264927 649515543849877700995213 := by
  unfold tailWord_1264927
  simp only [CollatzResearch.WordTrace]
  refine ⟨46135677888392986177497035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30757118592261990784998023 46135677888392986177497035)
  ·
    refine ⟨69203516832589479266245553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46135677888392986177497035 69203516832589479266245553)
    ·
      refine ⟨51902637624442109449684165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69203516832589479266245553 51902637624442109449684165)
      ·
        refine ⟨9731744554582895521815781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51902637624442109449684165 9731744554582895521815781)
        ·
          refine ⟨1824702103984292910340459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9731744554582895521815781 1824702103984292910340459)
          ·
            refine ⟨2737053155976439365510689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824702103984292910340459 2737053155976439365510689)
            ·
              refine ⟨2052789866982329524133017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737053155976439365510689 2052789866982329524133017)
              ·
                refine ⟨1539592400236747143099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052789866982329524133017 1539592400236747143099763)
                ·
                  refine ⟨2309388600355120714649645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539592400236747143099763 2309388600355120714649645)
                  ·
                    refine ⟨866020725133170267993617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309388600355120714649645 866020725133170267993617)
                    ·
                      refine ⟨649515543849877700995213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866020725133170267993617 649515543849877700995213)
                      ·
                        rfl

theorem cell23_1264927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_1264927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264927 prefixEnd_1264927 := by exact prefixLift 1264927
  have htrace : WordTrace (prefixWord ++ tailWord_1264927) baseStart_1264927 baseEnd_1264927 := by
    simpa [prefixWord, tailWord_1264927, baseEnd_1264927] using wordTrace_append hprefix tailTrace_1264927
  have hstable : (prefixWord ++ tailWord_1264927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264927).length < 2 ^ (prefixWord ++ tailWord_1264927).sum := by decide
  have hdescent : baseEnd_1264927 < baseStart_1264927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1264976 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_1264976 : Nat := 118140960795 + 1264976 * 2 ^ 59
def prefixEnd_1264976 : Nat := 4983230072969 + 3 ^ 40 * 1264976 * 2
def baseEnd_1264976 : Nat := 216513568133982669760829

theorem tailTrace_1264976 : CollatzResearch.WordTrace tailWord_1264976 prefixEnd_1264976 216513568133982669760829 := by
  unfold tailWord_1264976
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068732532607733773015391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30758310043476978364020521 23068732532607733773015391)
  ·
    refine ⟨34603098798911600659523087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23068732532607733773015391 34603098798911600659523087)
    ·
      refine ⟨51904648198367400989284631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34603098798911600659523087 51904648198367400989284631)
      ·
        refine ⟨77856972297551101483926947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51904648198367400989284631 77856972297551101483926947)
        ·
          refine ⟨116785458446326652225890421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77856972297551101483926947 116785458446326652225890421)
          ·
            refine ⟨10948636729343123646177227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116785458446326652225890421 10948636729343123646177227)
            ·
              refine ⟨16422955094014685469265841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10948636729343123646177227 16422955094014685469265841)
              ·
                refine ⟨12317216320511014101949381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16422955094014685469265841 12317216320511014101949381)
                ·
                  refine ⟨2309478060095815144115509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12317216320511014101949381 2309478060095815144115509)
                  ·
                    refine ⟨216513568133982669760829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2309478060095815144115509 216513568133982669760829)
                    ·
                      rfl

theorem cell23_1264976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_1264976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1264976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1264976 prefixEnd_1264976 := by exact prefixLift 1264976
  have htrace : WordTrace (prefixWord ++ tailWord_1264976) baseStart_1264976 baseEnd_1264976 := by
    simpa [prefixWord, tailWord_1264976, baseEnd_1264976] using wordTrace_append hprefix tailTrace_1264976
  have hstable : (prefixWord ++ tailWord_1264976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1264976).length < 2 ^ (prefixWord ++ tailWord_1264976).sum := by decide
  have hdescent : baseEnd_1264976 < baseStart_1264976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1264976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265080 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_1265080 : Nat := 118140960795 + 1265080 * 2 ^ 59
def prefixEnd_1265080 : Nat := 4983230072969 + 3 ^ 40 * 1265080 * 2
def baseEnd_1265080 : Nat := 649594106390015602382009

theorem tailTrace_1265080 : CollatzResearch.WordTrace tailWord_1265080 prefixEnd_1265080 649594106390015602382009 := by
  unfold tailWord_1265080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070629128419346653908347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30760838837892462205211129 23070629128419346653908347)
  ·
    refine ⟨34605943692629019980862521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23070629128419346653908347 34605943692629019980862521)
    ·
      refine ⟨25954457769471764985646891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34605943692629019980862521 25954457769471764985646891)
      ·
        refine ⟨38931686654207647478470337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25954457769471764985646891 38931686654207647478470337)
        ·
          refine ⟨29198764990655735608852753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38931686654207647478470337 29198764990655735608852753)
          ·
            refine ⟨21899073742991801706639565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29198764990655735608852753 21899073742991801706639565)
            ·
              refine ⟨8212152653621925639989837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21899073742991801706639565 8212152653621925639989837)
              ·
                refine ⟨3079557245108222114996189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8212152653621925639989837 3079557245108222114996189)
                ·
                  refine ⟨1154833966915583293123571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3079557245108222114996189 1154833966915583293123571)
                  ·
                    refine ⟨1732250950373374939685357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154833966915583293123571 1732250950373374939685357)
                    ·
                      refine ⟨649594106390015602382009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732250950373374939685357 649594106390015602382009)
                      ·
                        rfl

theorem cell23_1265080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_1265080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265080 prefixEnd_1265080 := by exact prefixLift 1265080
  have htrace : WordTrace (prefixWord ++ tailWord_1265080) baseStart_1265080 baseEnd_1265080 := by
    simpa [prefixWord, tailWord_1265080, baseEnd_1265080] using wordTrace_append hprefix tailTrace_1265080
  have hstable : (prefixWord ++ tailWord_1265080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265080).length < 2 ^ (prefixWord ++ tailWord_1265080).sum := by decide
  have hdescent : baseEnd_1265080 < baseStart_1265080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265100 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_1265100 : Nat := 118140960795 + 1265100 * 2 ^ 59
def prefixEnd_1265100 : Nat := 4983230072969 + 3 ^ 40 * 1265100 * 2
def baseEnd_1265100 : Nat := 216534792001035174710639

theorem tailTrace_1265100 : CollatzResearch.WordTrace tailWord_1265100 prefixEnd_1265100 216534792001035174710639 := by
  unfold tailWord_1265100
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070993858383118361772377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30761325144510824482363169 23070993858383118361772377)
  ·
    refine ⟨17303245393787338771329283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23070993858383118361772377 17303245393787338771329283)
    ·
      refine ⟨25954868090681008156993925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17303245393787338771329283 25954868090681008156993925)
      ·
        refine ⟨4866537767002689029436361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25954868090681008156993925 4866537767002689029436361)
        ·
          refine ⟨3649903325252016772077271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866537767002689029436361 3649903325252016772077271)
          ·
            refine ⟨5474854987878025158115907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649903325252016772077271 5474854987878025158115907)
            ·
              refine ⟨8212282481817037737173861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474854987878025158115907 8212282481817037737173861)
              ·
                refine ⟨1539802965340694575720099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8212282481817037737173861 1539802965340694575720099)
                ·
                  refine ⟨2309704448011041863580149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539802965340694575720099 2309704448011041863580149)
                  ·
                    refine ⟨216534792001035174710639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2309704448011041863580149 216534792001035174710639)
                    ·
                      rfl

theorem cell23_1265100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_1265100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265100 prefixEnd_1265100 := by exact prefixLift 1265100
  have htrace : WordTrace (prefixWord ++ tailWord_1265100) baseStart_1265100 baseEnd_1265100 := by
    simpa [prefixWord, tailWord_1265100, baseEnd_1265100] using wordTrace_append hprefix tailTrace_1265100
  have hstable : (prefixWord ++ tailWord_1265100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265100).length < 2 ^ (prefixWord ++ tailWord_1265100).sum := by decide
  have hdescent : baseEnd_1265100 < baseStart_1265100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265103 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_1265103 : Nat := 118140960795 + 1265103 * 2 ^ 59
def prefixEnd_1265103 : Nat := 4983230072969 + 3 ^ 40 * 1265103 * 2
def baseEnd_1265103 : Nat := 649605916445069012394403

theorem tailTrace_1265103 : CollatzResearch.WordTrace tailWord_1265103 prefixEnd_1265103 649605916445069012394403 := by
  unfold tailWord_1265103
  simp only [CollatzResearch.WordTrace]
  refine ⟨46142097135755368235903963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30761398090503578823935975 46142097135755368235903963)
  ·
    refine ⟨69213145703633052353855945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46142097135755368235903963 69213145703633052353855945)
    ·
      refine ⟨51909859277724789265391959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69213145703633052353855945 51909859277724789265391959)
      ·
        refine ⟨77864788916587183898087939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51909859277724789265391959 77864788916587183898087939)
        ·
          refine ⟨116797183374880775847131909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77864788916587183898087939 116797183374880775847131909)
          ·
            refine ⟨21899471882790145471337233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116797183374880775847131909 21899471882790145471337233)
            ·
              refine ⟨16424603912092609103502925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21899471882790145471337233 16424603912092609103502925)
              ·
                refine ⟨6159226467034728413813597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16424603912092609103502925 6159226467034728413813597)
                ·
                  refine ⟨2309709925138023155180099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6159226467034728413813597 2309709925138023155180099)
                  ·
                    refine ⟨3464564887707034732770149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309709925138023155180099 3464564887707034732770149)
                    ·
                      refine ⟨649605916445069012394403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3464564887707034732770149 649605916445069012394403)
                      ·
                        rfl

theorem cell23_1265103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_1265103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265103 prefixEnd_1265103 := by exact prefixLift 1265103
  have htrace : WordTrace (prefixWord ++ tailWord_1265103) baseStart_1265103 baseEnd_1265103 := by
    simpa [prefixWord, tailWord_1265103, baseEnd_1265103] using wordTrace_append hprefix tailTrace_1265103
  have hstable : (prefixWord ++ tailWord_1265103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265103).length < 2 ^ (prefixWord ++ tailWord_1265103).sum := by decide
  have hdescent : baseEnd_1265103 < baseStart_1265103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265114 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_1265114 : Nat := 118140960795 + 1265114 * 2 ^ 59
def prefixEnd_1265114 : Nat := 4983230072969 + 3 ^ 40 * 1265114 * 2
def baseEnd_1265114 : Nat := 649611564732268469356853

theorem tailTrace_1265114 : CollatzResearch.WordTrace tailWord_1265114 prefixEnd_1265114 649611564732268469356853 := by
  unfold tailWord_1265114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535624584678879278638599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30761665559143678076369597 11535624584678879278638599)
  ·
    refine ⟨17303436877018318917957899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11535624584678879278638599 17303436877018318917957899)
    ·
      refine ⟨25955155315527478376936849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17303436877018318917957899 25955155315527478376936849)
      ·
        refine ⟨19466366486645608782702637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25955155315527478376936849 19466366486645608782702637)
        ·
          refine ⟨7299887432492103293513489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19466366486645608782702637 7299887432492103293513489)
          ·
            refine ⟨5474915574369077470135117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7299887432492103293513489 5474915574369077470135117)
            ·
              refine ⟨2053093340388404051300669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5474915574369077470135117 2053093340388404051300669)
              ·
                refine ⟨769910002645651519237751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053093340388404051300669 769910002645651519237751)
                ·
                  refine ⟨1154865003968477278856627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 769910002645651519237751 1154865003968477278856627)
                  ·
                    refine ⟨1732297505952715918284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154865003968477278856627 1732297505952715918284941)
                    ·
                      refine ⟨649611564732268469356853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732297505952715918284941 649611564732268469356853)
                      ·
                        rfl

theorem cell23_1265114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_1265114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265114 prefixEnd_1265114 := by exact prefixLift 1265114
  have htrace : WordTrace (prefixWord ++ tailWord_1265114) baseStart_1265114 baseEnd_1265114 := by
    simpa [prefixWord, tailWord_1265114, baseEnd_1265114] using wordTrace_append hprefix tailTrace_1265114
  have hstable : (prefixWord ++ tailWord_1265114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265114).length < 2 ^ (prefixWord ++ tailWord_1265114).sum := by decide
  have hdescent : baseEnd_1265114 < baseStart_1265114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265154 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1265154 : Nat := 118140960795 + 1265154 * 2 ^ 59
def prefixEnd_1265154 : Nat := 4983230072969 + 3 ^ 40 * 1265154 * 2
def baseEnd_1265154 : Nat := 649632103958448312856669

theorem tailTrace_1265154 : CollatzResearch.WordTrace tailWord_1265154 prefixEnd_1265154 649632103958448312856669 := by
  unfold tailWord_1265154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11535989314642650986502629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30762638172380402630673677 11535989314642650986502629)
  ·
    refine ⟨2162997996495497059969243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11535989314642650986502629 2162997996495497059969243)
    ·
      refine ⟨3244496994743245589953865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162997996495497059969243 3244496994743245589953865)
      ·
        refine ⟨2433372746057434192465399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244496994743245589953865 2433372746057434192465399)
        ·
          refine ⟨3650059119086151288698099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433372746057434192465399 3650059119086151288698099)
          ·
            refine ⟨5475088678629226933047149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650059119086151288698099 5475088678629226933047149)
            ·
              refine ⟨2053158254485960099892681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475088678629226933047149 2053158254485960099892681)
              ·
                refine ⟨1539868690864470074919511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053158254485960099892681 1539868690864470074919511)
                ·
                  refine ⟨2309803036296705112379267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539868690864470074919511 2309803036296705112379267)
                  ·
                    refine ⟨3464704554445057668568901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309803036296705112379267 3464704554445057668568901)
                    ·
                      refine ⟨649632103958448312856669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3464704554445057668568901 649632103958448312856669)
                      ·
                        rfl

theorem cell23_1265154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1265154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265154 prefixEnd_1265154 := by exact prefixLift 1265154
  have htrace : WordTrace (prefixWord ++ tailWord_1265154) baseStart_1265154 baseEnd_1265154 := by
    simpa [prefixWord, tailWord_1265154, baseEnd_1265154] using wordTrace_append hprefix tailTrace_1265154
  have hstable : (prefixWord ++ tailWord_1265154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265154).length < 2 ^ (prefixWord ++ tailWord_1265154).sum := by decide
  have hdescent : baseEnd_1265154 < baseStart_1265154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265183 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1265183 : Nat := 118140960795 + 1265183 * 2 ^ 59
def prefixEnd_1265183 : Nat := 4983230072969 + 3 ^ 40 * 1265183 * 2
def baseEnd_1265183 : Nat := 649646994897428699394035

theorem tailTrace_1265183 : CollatzResearch.WordTrace tailWord_1265183 prefixEnd_1265183 649646994897428699394035 := by
  unfold tailWord_1265183
  simp only [CollatzResearch.WordTrace]
  refine ⟨46145014975465541898816203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30763343316977027932544135 46145014975465541898816203)
  ·
    refine ⟨69217522463198312848224305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46145014975465541898816203 69217522463198312848224305)
    ·
      refine ⟨51913141847398734636168229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69217522463198312848224305 51913141847398734636168229)
      ·
        refine ⟨9733714096387262744281543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51913141847398734636168229 9733714096387262744281543)
        ·
          refine ⟨14600571144580894116422315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733714096387262744281543 14600571144580894116422315)
          ·
            refine ⟨21900856716871341174633473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600571144580894116422315 21900856716871341174633473)
            ·
              refine ⟨16425642537653505880975105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21900856716871341174633473 16425642537653505880975105)
              ·
                refine ⟨12319231903240129410731329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16425642537653505880975105 12319231903240129410731329)
                ·
                  refine ⟨9239423927430097058048497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12319231903240129410731329 9239423927430097058048497)
                  ·
                    refine ⟨6929567945572572793536373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9239423927430097058048497 6929567945572572793536373)
                    ·
                      refine ⟨649646994897428699394035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6929567945572572793536373 649646994897428699394035)
                      ·
                        rfl

theorem cell23_1265183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1265183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265183 prefixEnd_1265183 := by exact prefixLift 1265183
  have htrace : WordTrace (prefixWord ++ tailWord_1265183) baseStart_1265183 baseEnd_1265183 := by
    simpa [prefixWord, tailWord_1265183, baseEnd_1265183] using wordTrace_append hprefix tailTrace_1265183
  have hstable : (prefixWord ++ tailWord_1265183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265183).length < 2 ^ (prefixWord ++ tailWord_1265183).sum := by decide
  have hdescent : baseEnd_1265183 < baseStart_1265183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265203 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 8]
def baseStart_1265203 : Nat := 118140960795 + 1265203 * 2 ^ 59
def prefixEnd_1265203 : Nat := 4983230072969 + 3 ^ 40 * 1265203 * 2
def baseEnd_1265203 : Nat := 216552421503506207047981

theorem tailTrace_1265203 : CollatzResearch.WordTrace tailWord_1265203 prefixEnd_1265203 216552421503506207047981 := by
  unfold tailWord_1265203
  simp only [CollatzResearch.WordTrace]
  refine ⟨46145744435393085314544263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30763829623595390209696175 46145744435393085314544263)
  ·
    refine ⟨69218616653089627971816395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46145744435393085314544263 69218616653089627971816395)
    ·
      refine ⟨103827924979634441957724593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69218616653089627971816395 103827924979634441957724593)
      ·
        refine ⟨77870943734725831468293445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103827924979634441957724593 77870943734725831468293445)
        ·
          refine ⟨14600801950261093400305021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77870943734725831468293445 14600801950261093400305021)
          ·
            refine ⟨5475300731347910025114383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14600801950261093400305021 5475300731347910025114383)
            ·
              refine ⟨8212951097021865037671575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475300731347910025114383 8212951097021865037671575)
              ·
                refine ⟨12319426645532797556507363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8212951097021865037671575 12319426645532797556507363)
                ·
                  refine ⟨18479139968299196334761045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12319426645532797556507363 18479139968299196334761045)
                  ·
                    refine ⟨216552421503506207047981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18479139968299196334761045 216552421503506207047981)
                    ·
                      rfl

theorem cell23_1265203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 8].length) (baseStart_1265203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265203 prefixEnd_1265203 := by exact prefixLift 1265203
  have htrace : WordTrace (prefixWord ++ tailWord_1265203) baseStart_1265203 baseEnd_1265203 := by
    simpa [prefixWord, tailWord_1265203, baseEnd_1265203] using wordTrace_append hprefix tailTrace_1265203
  have hstable : (prefixWord ++ tailWord_1265203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265203).length < 2 ^ (prefixWord ++ tailWord_1265203).sum := by decide
  have hdescent : baseEnd_1265203 < baseStart_1265203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265227 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 4, 2, 2]
def baseStart_1265227 : Nat := 118140960795 + 1265227 * 2 ^ 59
def prefixEnd_1265227 : Nat := 4983230072969 + 3 ^ 40 * 1265227 * 2
def baseEnd_1265227 : Nat := 649669588046226527243833

theorem tailTrace_1265227 : CollatzResearch.WordTrace tailWord_1265227 prefixEnd_1265227 649669588046226527243833 := by
  unfold tailWord_1265227
  simp only [CollatzResearch.WordTrace]
  refine ⟨46146619787306137413417935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30764413191537424942278623 46146619787306137413417935)
  ·
    refine ⟨69219929680959206120126903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46146619787306137413417935 69219929680959206120126903)
    ·
      refine ⟨103829894521438809180190355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69219929680959206120126903 103829894521438809180190355)
      ·
        refine ⟨155744841782158213770285533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103829894521438809180190355 155744841782158213770285533)
        ·
          refine ⟨58404315668309330163857075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155744841782158213770285533 58404315668309330163857075)
          ·
            refine ⟨87606473502463995245785613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58404315668309330163857075 87606473502463995245785613)
            ·
              refine ⟨32852427563423998217169605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87606473502463995245785613 32852427563423998217169605)
              ·
                refine ⟨6159830168141999665719301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32852427563423998217169605 6159830168141999665719301)
                ·
                  refine ⟨1154968156526624937322369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6159830168141999665719301 1154968156526624937322369)
                  ·
                    refine ⟨866226117394968702991777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1154968156526624937322369 866226117394968702991777)
                    ·
                      refine ⟨649669588046226527243833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866226117394968702991777 649669588046226527243833)
                      ·
                        rfl

theorem cell23_1265227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 2, 2].length) (baseStart_1265227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265227 prefixEnd_1265227 := by exact prefixLift 1265227
  have htrace : WordTrace (prefixWord ++ tailWord_1265227) baseStart_1265227 baseEnd_1265227 := by
    simpa [prefixWord, tailWord_1265227, baseEnd_1265227] using wordTrace_append hprefix tailTrace_1265227
  have hstable : (prefixWord ++ tailWord_1265227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265227).length < 2 ^ (prefixWord ++ tailWord_1265227).sum := by decide
  have hdescent : baseEnd_1265227 < baseStart_1265227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265233 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 9]
def baseStart_1265233 : Nat := 118140960795 + 1265233 * 2 ^ 59
def prefixEnd_1265233 : Nat := 4983230072969 + 3 ^ 40 * 1265233 * 2
def baseEnd_1265233 : Nat := 72185852103350389307645

theorem tailTrace_1265233 : CollatzResearch.WordTrace tailWord_1265233 prefixEnd_1265233 72185852103350389307645 := by
  unfold tailWord_1265233
  simp only [CollatzResearch.WordTrace]
  refine ⟨46146838625284400438136353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30764559083522933625424235 46146838625284400438136353)
  ·
    refine ⟨34610128968963300328602265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46146838625284400438136353 34610128968963300328602265)
    ·
      refine ⟨25957596726722475246451699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34610128968963300328602265 25957596726722475246451699)
      ·
        refine ⟨38936395090083712869677549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25957596726722475246451699 38936395090083712869677549)
        ·
          refine ⟨14601148158781392326129081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38936395090083712869677549 14601148158781392326129081)
          ·
            refine ⟨10950861119086044244596811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14601148158781392326129081 10950861119086044244596811)
            ·
              refine ⟨16426291678629066366895217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10950861119086044244596811 16426291678629066366895217)
              ·
                refine ⟨12319718758971799775171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16426291678629066366895217 12319718758971799775171413)
                ·
                  refine ⟨72185852103350389307645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12319718758971799775171413 72185852103350389307645)
                  ·
                    rfl

theorem cell23_1265233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_1265233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265233 prefixEnd_1265233 := by exact prefixLift 1265233
  have htrace : WordTrace (prefixWord ++ tailWord_1265233) baseStart_1265233 baseEnd_1265233 := by
    simpa [prefixWord, tailWord_1265233, baseEnd_1265233] using wordTrace_append hprefix tailTrace_1265233
  have hstable : (prefixWord ++ tailWord_1265233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265233).length < 2 ^ (prefixWord ++ tailWord_1265233).sum := by decide
  have hdescent : baseEnd_1265233 < baseStart_1265233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265238 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1265238 : Nat := 118140960795 + 1265238 * 2 ^ 59
def prefixEnd_1265238 : Nat := 4983230072969 + 3 ^ 40 * 1265238 * 2
def baseEnd_1265238 : Nat := 649675236333425984206283

theorem tailTrace_1265238 : CollatzResearch.WordTrace tailWord_1265238 prefixEnd_1265238 649675236333425984206283 := by
  unfold tailWord_1265238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884188811891642893254273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30764680660177524194712245 2884188811891642893254273)
  ·
    refine ⟨2163141608918732169940705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2884188811891642893254273 2163141608918732169940705)
    ·
      refine ⟨1622356206689049127455529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163141608918732169940705 1622356206689049127455529)
      ·
        refine ⟨1216767155016786845591647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1622356206689049127455529 1216767155016786845591647)
        ·
          refine ⟨1825150732525180268387471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216767155016786845591647 1825150732525180268387471)
          ·
            refine ⟨2737726098787770402581207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825150732525180268387471 2737726098787770402581207)
            ·
              refine ⟨4106589148181655603871811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737726098787770402581207 4106589148181655603871811)
              ·
                refine ⟨6159883722272483405807717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106589148181655603871811 6159883722272483405807717)
                ·
                  refine ⟨1154978197926090638588947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6159883722272483405807717 1154978197926090638588947)
                  ·
                    refine ⟨1732467296889135957883421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1154978197926090638588947 1732467296889135957883421)
                    ·
                      refine ⟨649675236333425984206283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732467296889135957883421 649675236333425984206283)
                      ·
                        rfl

theorem cell23_1265238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1265238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265238 prefixEnd_1265238 := by exact prefixLift 1265238
  have htrace : WordTrace (prefixWord ++ tailWord_1265238) baseStart_1265238 baseEnd_1265238 := by
    simpa [prefixWord, tailWord_1265238, baseEnd_1265238] using wordTrace_append hprefix tailTrace_1265238
  have hstable : (prefixWord ++ tailWord_1265238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265238).length < 2 ^ (prefixWord ++ tailWord_1265238).sum := by decide
  have hdescent : baseEnd_1265238 < baseStart_1265238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265261 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1265261 : Nat := 118140960795 + 1265261 * 2 ^ 59
def prefixEnd_1265261 : Nat := 4983230072969 + 3 ^ 40 * 1265261 * 2
def baseEnd_1265261 : Nat := 649687046388479394218677

theorem tailTrace_1265261 : CollatzResearch.WordTrace tailWord_1265261 prefixEnd_1265261 649687046388479394218677 := by
  unfold tailWord_1265261
  simp only [CollatzResearch.WordTrace]
  refine ⟨46147859869182961220155637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30765239912788640813437091 46147859869182961220155637)
  ·
    refine ⟨4326361862735902614389591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46147859869182961220155637 4326361862735902614389591)
    ·
      refine ⟨6489542794103853921584387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4326361862735902614389591 6489542794103853921584387)
      ·
        refine ⟨9734314191155780882376581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6489542794103853921584387 9734314191155780882376581)
        ·
          refine ⟨1825183910841708915445609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9734314191155780882376581 1825183910841708915445609)
          ·
            refine ⟨1368887933131281686584207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825183910841708915445609 1368887933131281686584207)
            ·
              refine ⟨2053331899696922529876311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1368887933131281686584207 2053331899696922529876311)
              ·
                refine ⟨3079997849545383794814467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053331899696922529876311 3079997849545383794814467)
                ·
                  refine ⟨4619996774318075692221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079997849545383794814467 4619996774318075692221701)
                  ·
                    refine ⟨866249395184639192291569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619996774318075692221701 866249395184639192291569)
                    ·
                      refine ⟨649687046388479394218677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866249395184639192291569 649687046388479394218677)
                      ·
                        rfl

theorem cell23_1265261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1265261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265261 prefixEnd_1265261 := by exact prefixLift 1265261
  have htrace : WordTrace (prefixWord ++ tailWord_1265261) baseStart_1265261 baseEnd_1265261 := by
    simpa [prefixWord, tailWord_1265261, baseEnd_1265261] using wordTrace_append hprefix tailTrace_1265261
  have hstable : (prefixWord ++ tailWord_1265261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265261).length < 2 ^ (prefixWord ++ tailWord_1265261).sum := by decide
  have hdescent : baseEnd_1265261 < baseStart_1265261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265280 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_1265280 : Nat := 118140960795 + 1265280 * 2 ^ 59
def prefixEnd_1265280 : Nat := 4983230072969 + 3 ^ 40 * 1265280 * 2
def baseEnd_1265280 : Nat := 216565600840304939960363

theorem tailTrace_1265280 : CollatzResearch.WordTrace tailWord_1265280 prefixEnd_1265280 216565600840304939960363 := by
  unfold tailWord_1265280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23074276428057063732548647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30765701904076084976731529 23074276428057063732548647)
  ·
    refine ⟨34611414642085595598822971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23074276428057063732548647 34611414642085595598822971)
    ·
      refine ⟨51917121963128393398234457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34611414642085595598822971 51917121963128393398234457)
      ·
        refine ⟨38937841472346295048675843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51917121963128393398234457 38937841472346295048675843)
        ·
          refine ⟨58406762208519442573013765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38937841472346295048675843 58406762208519442573013765)
          ·
            refine ⟨10951267914097395482440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58406762208519442573013765 10951267914097395482440081)
            ·
              refine ⟨8213450935573046611830061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10951267914097395482440081 8213450935573046611830061)
              ·
                refine ⟨3080044100839892479436273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8213450935573046611830061 3080044100839892479436273)
                ·
                  refine ⟨2310033075629919359577205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080044100839892479436273 2310033075629919359577205)
                  ·
                    refine ⟨216565600840304939960363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2310033075629919359577205 216565600840304939960363)
                    ·
                      rfl

theorem cell23_1265280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_1265280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265280 prefixEnd_1265280 := by exact prefixLift 1265280
  have htrace : WordTrace (prefixWord ++ tailWord_1265280) baseStart_1265280 baseEnd_1265280 := by
    simpa [prefixWord, tailWord_1265280, baseEnd_1265280] using wordTrace_append hprefix tailTrace_1265280
  have hstable : (prefixWord ++ tailWord_1265280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265280).length < 2 ^ (prefixWord ++ tailWord_1265280).sum := by decide
  have hdescent : baseEnd_1265280 < baseStart_1265280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265317 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_1265317 : Nat := 118140960795 + 1265317 * 2 ^ 59
def prefixEnd_1265317 : Nat := 4983230072969 + 3 ^ 40 * 1265317 * 2
def baseEnd_1265317 : Nat := 649715801305131175118419

theorem tailTrace_1265317 : CollatzResearch.WordTrace tailWord_1265317 prefixEnd_1265317 649715801305131175118419 := by
  unfold tailWord_1265317
  simp only [CollatzResearch.WordTrace]
  refine ⟨46149902356980082784194205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30766601571320055189462803 46149902356980082784194205)
  ·
    refine ⟨17306213383867531044072827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46149902356980082784194205 17306213383867531044072827)
    ·
      refine ⟨25959320075801296566109241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17306213383867531044072827 25959320075801296566109241)
      ·
        refine ⟨19469490056850972424581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25959320075801296566109241 19469490056850972424581931)
        ·
          refine ⟨29204235085276458636872897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19469490056850972424581931 29204235085276458636872897)
          ·
            refine ⟨21903176313957343977654673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29204235085276458636872897 21903176313957343977654673)
            ·
              refine ⟨16427382235468007983241005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21903176313957343977654673 16427382235468007983241005)
              ·
                refine ⟨6160268338300502993715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16427382235468007983241005 6160268338300502993715377)
                ·
                  refine ⟨4620201253725377245286533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160268338300502993715377 4620201253725377245286533)
                  ·
                    refine ⟨866287735073508233491225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4620201253725377245286533 866287735073508233491225)
                    ·
                      refine ⟨649715801305131175118419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866287735073508233491225 649715801305131175118419)
                      ·
                        rfl

theorem cell23_1265317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_1265317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265317 prefixEnd_1265317 := by exact prefixLift 1265317
  have htrace : WordTrace (prefixWord ++ tailWord_1265317) baseStart_1265317 baseEnd_1265317 := by
    simpa [prefixWord, tailWord_1265317, baseEnd_1265317] using wordTrace_append hprefix tailTrace_1265317
  have hstable : (prefixWord ++ tailWord_1265317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265317).length < 2 ^ (prefixWord ++ tailWord_1265317).sum := by decide
  have hdescent : baseEnd_1265317 < baseStart_1265317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265330 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1265330 : Nat := 118140960795 + 1265330 * 2 ^ 59
def prefixEnd_1265330 : Nat := 4983230072969 + 3 ^ 40 * 1265330 * 2
def baseEnd_1265330 : Nat := 649722476553639624255859

theorem tailTrace_1265330 : CollatzResearch.WordTrace tailWord_1265330 prefixEnd_1265330 649722476553639624255859 := by
  unfold tailWord_1265330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537594126483246501104361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30766917670621990669611629 11537594126483246501104361)
  ·
    refine ⟨8653195594862434875828271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11537594126483246501104361 8653195594862434875828271)
    ·
      refine ⟨12979793392293652313742407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653195594862434875828271 12979793392293652313742407)
      ·
        refine ⟨19469690088440478470613611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979793392293652313742407 19469690088440478470613611)
        ·
          refine ⟨29204535132660717705920417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19469690088440478470613611 29204535132660717705920417)
          ·
            refine ⟨21903401349495538279440313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29204535132660717705920417 21903401349495538279440313)
            ·
              refine ⟨16427551012121653709580235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21903401349495538279440313 16427551012121653709580235)
              ·
                refine ⟨24641326518182480564370353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16427551012121653709580235 24641326518182480564370353)
                ·
                  refine ⟨18480994888636860423277765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24641326518182480564370353 18480994888636860423277765)
                  ·
                    refine ⟨3465186541619411329364581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18480994888636860423277765 3465186541619411329364581)
                    ·
                      refine ⟨649722476553639624255859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3465186541619411329364581 649722476553639624255859)
                      ·
                        rfl

theorem cell23_1265330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1265330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265330 prefixEnd_1265330 := by exact prefixLift 1265330
  have htrace : WordTrace (prefixWord ++ tailWord_1265330) baseStart_1265330 baseEnd_1265330 := by
    simpa [prefixWord, tailWord_1265330, baseEnd_1265330] using wordTrace_append hprefix tailTrace_1265330
  have hstable : (prefixWord ++ tailWord_1265330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265330).length < 2 ^ (prefixWord ++ tailWord_1265330).sum := by decide
  have hdescent : baseEnd_1265330 < baseStart_1265330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265337 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1265337 : Nat := 118140960795 + 1265337 * 2 ^ 59
def prefixEnd_1265337 : Nat := 4983230072969 + 3 ^ 40 * 1265337 * 2
def baseEnd_1265337 : Nat := 649726070918221096868327

theorem tailTrace_1265337 : CollatzResearch.WordTrace tailWord_1265337 prefixEnd_1265337 649726070918221096868327 := by
  unfold tailWord_1265337
  simp only [CollatzResearch.WordTrace]
  refine ⟨46150631816907626199922265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30767087877938417466614843 46150631816907626199922265)
  ·
    refine ⟨34612973862680719649941699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46150631816907626199922265 34612973862680719649941699)
    ·
      refine ⟨51919460794021079474912549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34612973862680719649941699 51919460794021079474912549)
      ·
        refine ⟨9734898898878952401546103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51919460794021079474912549 9734898898878952401546103)
        ·
          refine ⟨14602348348318428602319155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734898898878952401546103 14602348348318428602319155)
          ·
            refine ⟨21903522522477642903478733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14602348348318428602319155 21903522522477642903478733)
            ·
              refine ⟨8213820945929116088804525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21903522522477642903478733 8213820945929116088804525)
              ·
                refine ⟨3080182854723418533301697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8213820945929116088804525 3080182854723418533301697)
                ·
                  refine ⟨2310137141042563899976273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080182854723418533301697 2310137141042563899976273)
                  ·
                    refine ⟨1732602855781922924982205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310137141042563899976273 1732602855781922924982205)
                    ·
                      refine ⟨649726070918221096868327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732602855781922924982205 649726070918221096868327)
                      ·
                        rfl

theorem cell23_1265337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1265337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265337 prefixEnd_1265337 := by exact prefixLift 1265337
  have htrace : WordTrace (prefixWord ++ tailWord_1265337) baseStart_1265337 baseEnd_1265337 := by
    simpa [prefixWord, tailWord_1265337, baseEnd_1265337] using wordTrace_append hprefix tailTrace_1265337
  have hstable : (prefixWord ++ tailWord_1265337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265337).length < 2 ^ (prefixWord ++ tailWord_1265337).sum := by decide
  have hdescent : baseEnd_1265337 < baseStart_1265337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265344 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 1, 4]
def baseStart_1265344 : Nat := 118140960795 + 1265344 * 2 ^ 59
def prefixEnd_1265344 : Nat := 4983230072969 + 3 ^ 40 * 1265344 * 2
def baseEnd_1265344 : Nat := 216576555094267523160265

theorem tailTrace_1265344 : CollatzResearch.WordTrace tailWord_1265344 prefixEnd_1265344 216576555094267523160265 := by
  unfold tailWord_1265344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075443563941133197713543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30767258085254844263618057 23075443563941133197713543)
  ·
    refine ⟨34613165345911699796570315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23075443563941133197713543 34613165345911699796570315)
    ·
      refine ⟨51919748018867549694855473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34613165345911699796570315 51919748018867549694855473)
      ·
        refine ⟨38939811014150662271141605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51919748018867549694855473 38939811014150662271141605)
        ·
          refine ⟨7301214565153249175839051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38939811014150662271141605 7301214565153249175839051)
          ·
            refine ⟨10951821847729873763758577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7301214565153249175839051 10951821847729873763758577)
            ·
              refine ⟨8213866385797405322818933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10951821847729873763758577 8213866385797405322818933)
              ·
                refine ⟨770049973668506749014275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8213866385797405322818933 770049973668506749014275)
                ·
                  refine ⟨1155074960502760123521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770049973668506749014275 1155074960502760123521413)
                  ·
                    refine ⟨216576555094267523160265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155074960502760123521413 216576555094267523160265)
                    ·
                      rfl

theorem cell23_1265344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_1265344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265344 prefixEnd_1265344 := by exact prefixLift 1265344
  have htrace : WordTrace (prefixWord ++ tailWord_1265344) baseStart_1265344 baseEnd_1265344 := by
    simpa [prefixWord, tailWord_1265344, baseEnd_1265344] using wordTrace_append hprefix tailTrace_1265344
  have hstable : (prefixWord ++ tailWord_1265344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265344).length < 2 ^ (prefixWord ++ tailWord_1265344).sum := by decide
  have hdescent : baseEnd_1265344 < baseStart_1265344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265361 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 1, 4]
def baseStart_1265361 : Nat := 118140960795 + 1265361 * 2 ^ 59
def prefixEnd_1265361 : Nat := 4983230072969 + 3 ^ 40 * 1265361 * 2
def baseEnd_1265361 : Nat := 216579464817976334322739

theorem tailTrace_1265361 : CollatzResearch.WordTrace tailWord_1265361 prefixEnd_1265361 216579464817976334322739 := by
  unfold tailWord_1265361
  simp only [CollatzResearch.WordTrace]
  refine ⟨46151507168820678298795937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30767671445880452199197291 46151507168820678298795937)
  ·
    refine ⟨34613630376615508724096953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46151507168820678298795937 34613630376615508724096953)
    ·
      refine ⟨25960222782461631543072715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34613630376615508724096953 25960222782461631543072715)
      ·
        refine ⟨38940334173692447314609073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25960222782461631543072715 38940334173692447314609073)
        ·
          refine ⟨29205250630269335485956805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38940334173692447314609073 29205250630269335485956805)
          ·
            refine ⟨5475984493175500403616901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29205250630269335485956805 5475984493175500403616901)
            ·
              refine ⟨1026747092470406325678169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5475984493175500403616901 1026747092470406325678169)
              ·
                refine ⟨770060319352804744258627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026747092470406325678169 770060319352804744258627)
                ·
                  refine ⟨1155090479029207116387941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770060319352804744258627 1155090479029207116387941)
                  ·
                    refine ⟨216579464817976334322739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155090479029207116387941 216579464817976334322739)
                    ·
                      rfl

theorem cell23_1265361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_1265361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265361 prefixEnd_1265361 := by exact prefixLift 1265361
  have htrace : WordTrace (prefixWord ++ tailWord_1265361) baseStart_1265361 baseEnd_1265361 := by
    simpa [prefixWord, tailWord_1265361, baseEnd_1265361] using wordTrace_append hprefix tailTrace_1265361
  have hstable : (prefixWord ++ tailWord_1265361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265361).length < 2 ^ (prefixWord ++ tailWord_1265361).sum := by decide
  have hdescent : baseEnd_1265361 < baseStart_1265361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265380 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1265380 : Nat := 118140960795 + 1265380 * 2 ^ 59
def prefixEnd_1265380 : Nat := 4983230072969 + 3 ^ 40 * 1265380 * 2
def baseEnd_1265380 : Nat := 649748150586364428630629

theorem tailTrace_1265380 : CollatzResearch.WordTrace tailWord_1265380 prefixEnd_1265380 649748150586364428630629 := by
  unfold tailWord_1265380
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076100077875922271868797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30768133437167896362491729 23076100077875922271868797)
  ·
    refine ⟨8653537529203470851950799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23076100077875922271868797 8653537529203470851950799)
    ·
      refine ⟨12980306293805206277926199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653537529203470851950799 12980306293805206277926199)
      ·
        refine ⟨19470459440707809416889299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980306293805206277926199 19470459440707809416889299)
        ·
          refine ⟨29205689161061714125333949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19470459440707809416889299 29205689161061714125333949)
          ·
            refine ⟨10952133435398142797000231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29205689161061714125333949 10952133435398142797000231)
            ·
              refine ⟨16428200153097214195500347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10952133435398142797000231 16428200153097214195500347)
              ·
                refine ⟨24642300229645821293250521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16428200153097214195500347 24642300229645821293250521)
                ·
                  refine ⟨18481725172234365969937891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24642300229645821293250521 18481725172234365969937891)
                  ·
                    refine ⟨27722587758351548954906837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18481725172234365969937891 27722587758351548954906837)
                    ·
                      refine ⟨649748150586364428630629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27722587758351548954906837 649748150586364428630629)
                      ·
                        rfl

theorem cell23_1265380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1265380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265380 prefixEnd_1265380 := by exact prefixLift 1265380
  have htrace : WordTrace (prefixWord ++ tailWord_1265380) baseStart_1265380 baseEnd_1265380 := by
    simpa [prefixWord, tailWord_1265380, baseEnd_1265380] using wordTrace_append hprefix tailTrace_1265380
  have hstable : (prefixWord ++ tailWord_1265380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265380).length < 2 ^ (prefixWord ++ tailWord_1265380).sum := by decide
  have hdescent : baseEnd_1265380 < baseStart_1265380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265384 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1265384 : Nat := 118140960795 + 1265384 * 2 ^ 59
def prefixEnd_1265384 : Nat := 4983230072969 + 3 ^ 40 * 1265384 * 2
def baseEnd_1265384 : Nat := 649750204508982412980611

theorem tailTrace_1265384 : CollatzResearch.WordTrace tailWord_1265384 prefixEnd_1265384 649750204508982412980611 := by
  unfold tailWord_1265384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076173023868676613441603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30768230698491568817922137 23076173023868676613441603)
  ·
    refine ⟨34614259535803014920162405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23076173023868676613441603 34614259535803014920162405)
    ·
      refine ⟨6490173662963065297530451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34614259535803014920162405 6490173662963065297530451)
      ·
        refine ⟨9735260494444597946295677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6490173662963065297530451 9735260494444597946295677)
        ·
          refine ⟨3650722685416724229860879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9735260494444597946295677 3650722685416724229860879)
          ·
            refine ⟨5476084028125086344791319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650722685416724229860879 5476084028125086344791319)
            ·
              refine ⟨8214126042187629517186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476084028125086344791319 8214126042187629517186979)
              ·
                refine ⟨12321189063281444275780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214126042187629517186979 12321189063281444275780469)
                ·
                  refine ⟨1155111474682635400854419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12321189063281444275780469 1155111474682635400854419)
                  ·
                    refine ⟨1732667212023953101281629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155111474682635400854419 1732667212023953101281629)
                    ·
                      refine ⟨649750204508982412980611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732667212023953101281629 649750204508982412980611)
                      ·
                        rfl

theorem cell23_1265384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1265384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265384 prefixEnd_1265384 := by exact prefixLift 1265384
  have htrace : WordTrace (prefixWord ++ tailWord_1265384) baseStart_1265384 baseEnd_1265384 := by
    simpa [prefixWord, tailWord_1265384, baseEnd_1265384] using wordTrace_append hprefix tailTrace_1265384
  have hstable : (prefixWord ++ tailWord_1265384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265384).length < 2 ^ (prefixWord ++ tailWord_1265384).sum := by decide
  have hdescent : baseEnd_1265384 < baseStart_1265384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265394 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1265394 : Nat := 118140960795 + 1265394 * 2 ^ 59
def prefixEnd_1265394 : Nat := 4983230072969 + 3 ^ 40 * 1265394 * 2
def baseEnd_1265394 : Nat := 649755339315527373855565

theorem tailTrace_1265394 : CollatzResearch.WordTrace tailWord_1265394 prefixEnd_1265394 649755339315527373855565 := by
  unfold tailWord_1265394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11538177694425281233686809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30768473851800749956498157 11538177694425281233686809)
  ·
    refine ⟨8653633270818960925265107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11538177694425281233686809 8653633270818960925265107)
    ·
      refine ⟨12980449906228441387897661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653633270818960925265107 12980449906228441387897661)
      ·
        refine ⟨4867668714835665520461623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12980449906228441387897661 4867668714835665520461623)
        ·
          refine ⟨7301503072253498280692435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867668714835665520461623 7301503072253498280692435)
          ·
            refine ⟨10952254608380247421038653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7301503072253498280692435 10952254608380247421038653)
            ·
              refine ⟨4107095478142592782889495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10952254608380247421038653 4107095478142592782889495)
              ·
                refine ⟨6160643217213889174334243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107095478142592782889495 6160643217213889174334243)
                ·
                  refine ⟨9240964825820833761501365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160643217213889174334243 9240964825820833761501365)
                  ·
                    refine ⟨866340452420703165140753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9240964825820833761501365 866340452420703165140753)
                    ·
                      refine ⟨649755339315527373855565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866340452420703165140753 649755339315527373855565)
                      ·
                        rfl

theorem cell23_1265394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1265394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265394 prefixEnd_1265394 := by exact prefixLift 1265394
  have htrace : WordTrace (prefixWord ++ tailWord_1265394) baseStart_1265394 baseEnd_1265394 := by
    simpa [prefixWord, tailWord_1265394, baseEnd_1265394] using wordTrace_append hprefix tailTrace_1265394
  have hstable : (prefixWord ++ tailWord_1265394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265394).length < 2 ^ (prefixWord ++ tailWord_1265394).sum := by decide
  have hdescent : baseEnd_1265394 < baseStart_1265394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265400 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1265400 : Nat := 118140960795 + 1265400 * 2 ^ 59
def prefixEnd_1265400 : Nat := 4983230072969 + 3 ^ 40 * 1265400 * 2
def baseEnd_1265400 : Nat := 216586140066484783460179

theorem tailTrace_1265400 : CollatzResearch.WordTrace tailWord_1265400 prefixEnd_1265400 216586140066484783460179 := by
  unfold tailWord_1265400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076464807839693979732827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30768619743786258639643769 23076464807839693979732827)
  ·
    refine ⟨34614697211759540969599241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23076464807839693979732827 34614697211759540969599241)
    ·
      refine ⟨25961022908819655727199431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34614697211759540969599241 25961022908819655727199431)
      ·
        refine ⟨38941534363229483590799147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25961022908819655727199431 38941534363229483590799147)
        ·
          refine ⟨58412301544844225386198721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38941534363229483590799147 58412301544844225386198721)
          ·
            refine ⟨43809226158633169039649041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58412301544844225386198721 43809226158633169039649041)
            ·
              refine ⟨32856919618974876779736781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43809226158633169039649041 32856919618974876779736781)
              ·
                refine ⟨12321344857115578792401293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32856919618974876779736781 12321344857115578792401293)
                ·
                  refine ⟨4620504321418342047150485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12321344857115578792401293 4620504321418342047150485)
                  ·
                    refine ⟨216586140066484783460179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4620504321418342047150485 216586140066484783460179)
                    ·
                      rfl

theorem cell23_1265400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1265400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265400 prefixEnd_1265400 := by exact prefixLift 1265400
  have htrace : WordTrace (prefixWord ++ tailWord_1265400) baseStart_1265400 baseEnd_1265400 := by
    simpa [prefixWord, tailWord_1265400, baseEnd_1265400] using wordTrace_append hprefix tailTrace_1265400
  have hstable : (prefixWord ++ tailWord_1265400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265400).length < 2 ^ (prefixWord ++ tailWord_1265400).sum := by decide
  have hdescent : baseEnd_1265400 < baseStart_1265400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265427 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3]
def baseStart_1265427 : Nat := 118140960795 + 1265427 * 2 ^ 59
def prefixEnd_1265427 : Nat := 4983230072969 + 3 ^ 40 * 1265427 * 2
def baseEnd_1265427 : Nat := 649772284177125744742913

theorem tailTrace_1265427 : CollatzResearch.WordTrace tailWord_1265427 prefixEnd_1265427 649772284177125744742913 := by
  unfold tailWord_1265427
  simp only [CollatzResearch.WordTrace]
  refine ⟨46153914386581571570698535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30769276257721047713799023 46153914386581571570698535)
  ·
    refine ⟨69230871579872357356047803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46153914386581571570698535 69230871579872357356047803)
    ·
      refine ⟨103846307369808536034071705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69230871579872357356047803 103846307369808536034071705)
      ·
        refine ⟨77884730527356402025553779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103846307369808536034071705 77884730527356402025553779)
        ·
          refine ⟨116827095791034603038330669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77884730527356402025553779 116827095791034603038330669)
          ·
            refine ⟨43810160921637976139374001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116827095791034603038330669 43810160921637976139374001)
            ·
              refine ⟨32857620691228482104530501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43810160921637976139374001 32857620691228482104530501)
              ·
                refine ⟨6160803879605340394599469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32857620691228482104530501 6160803879605340394599469)
                ·
                  refine ⟨2310301454852002647974801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6160803879605340394599469 2310301454852002647974801)
                  ·
                    refine ⟨1732726091139001985981101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310301454852002647974801 1732726091139001985981101)
                    ·
                      refine ⟨649772284177125744742913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732726091139001985981101 649772284177125744742913)
                      ·
                        rfl

theorem cell23_1265427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_1265427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265427 prefixEnd_1265427 := by exact prefixLift 1265427
  have htrace : WordTrace (prefixWord ++ tailWord_1265427) baseStart_1265427 baseEnd_1265427 := by
    simpa [prefixWord, tailWord_1265427, baseEnd_1265427] using wordTrace_append hprefix tailTrace_1265427
  have hstable : (prefixWord ++ tailWord_1265427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265427).length < 2 ^ (prefixWord ++ tailWord_1265427).sum := by decide
  have hdescent : baseEnd_1265427 < baseStart_1265427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265434 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_1265434 : Nat := 118140960795 + 1265434 * 2 ^ 59
def prefixEnd_1265434 : Nat := 4983230072969 + 3 ^ 40 * 1265434 * 2
def baseEnd_1265434 : Nat := 216591959513902405785127

theorem tailTrace_1265434 : CollatzResearch.WordTrace tailWord_1265434 prefixEnd_1265434 216591959513902405785127 := by
  unfold tailWord_1265434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11538542424389052941550839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30769446465037474510802237 11538542424389052941550839)
  ·
    refine ⟨17307813636583579412326259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11538542424389052941550839 17307813636583579412326259)
    ·
      refine ⟨25961720454875369118489389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307813636583579412326259 25961720454875369118489389)
      ·
        refine ⟨9735645170578263419433521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25961720454875369118489389 9735645170578263419433521)
        ·
          refine ⟨7301733877933697564575141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9735645170578263419433521 7301733877933697564575141)
          ·
            refine ⟨1369075102112568293357839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7301733877933697564575141 1369075102112568293357839)
            ·
              refine ⟨2053612653168852440036759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369075102112568293357839 2053612653168852440036759)
              ·
                refine ⟨3080418979753278660055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053612653168852440036759 3080418979753278660055139)
                ·
                  refine ⟨4620628469629917990082709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080418979753278660055139 4620628469629917990082709)
                  ·
                    refine ⟨216591959513902405785127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4620628469629917990082709 216591959513902405785127)
                    ·
                      rfl

theorem cell23_1265434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_1265434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265434 prefixEnd_1265434 := by exact prefixLift 1265434
  have htrace : WordTrace (prefixWord ++ tailWord_1265434) baseStart_1265434 baseEnd_1265434 := by
    simpa [prefixWord, tailWord_1265434, baseEnd_1265434] using wordTrace_append hprefix tailTrace_1265434
  have hstable : (prefixWord ++ tailWord_1265434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265434).length < 2 ^ (prefixWord ++ tailWord_1265434).sum := by decide
  have hdescent : baseEnd_1265434 < baseStart_1265434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265441 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1265441 : Nat := 118140960795 + 1265441 * 2 ^ 59
def prefixEnd_1265441 : Nat := 4983230072969 + 3 ^ 40 * 1265441 * 2
def baseEnd_1265441 : Nat := 649779472906288689967849

theorem tailTrace_1265441 : CollatzResearch.WordTrace tailWord_1265441 prefixEnd_1265441 649779472906288689967849 := by
  unfold tailWord_1265441
  simp only [CollatzResearch.WordTrace]
  refine ⟨46154425008530851961708177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30769616672353901307805451 46154425008530851961708177)
  ·
    refine ⟨34615818756398138971281133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46154425008530851961708177 34615818756398138971281133)
    ·
      refine ⟨12980932033649302114230425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34615818756398138971281133 12980932033649302114230425)
      ·
        refine ⟨9735699025236976585672819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12980932033649302114230425 9735699025236976585672819)
        ·
          refine ⟨14603548537855464878509229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735699025236976585672819 14603548537855464878509229)
          ·
            refine ⟨5476330701695799329440961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14603548537855464878509229 5476330701695799329440961)
            ·
              refine ⟨4107248026271849497080721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5476330701695799329440961 4107248026271849497080721)
              ·
                refine ⟨3080436019703887122810541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107248026271849497080721 3080436019703887122810541)
                ·
                  refine ⟨1155163507388957671053953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3080436019703887122810541 1155163507388957671053953)
                  ·
                    refine ⟨866372630541718253290465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1155163507388957671053953 866372630541718253290465)
                    ·
                      refine ⟨649779472906288689967849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866372630541718253290465 649779472906288689967849)
                      ·
                        rfl

theorem cell23_1265441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1265441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265441 prefixEnd_1265441 := by exact prefixLift 1265441
  have htrace : WordTrace (prefixWord ++ tailWord_1265441) baseStart_1265441 baseEnd_1265441 := by
    simpa [prefixWord, tailWord_1265441, baseEnd_1265441] using wordTrace_append hprefix tailTrace_1265441
  have hstable : (prefixWord ++ tailWord_1265441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265441).length < 2 ^ (prefixWord ++ tailWord_1265441).sum := by decide
  have hdescent : baseEnd_1265441 < baseStart_1265441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265475 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 1, 2, 2]
def baseStart_1265475 : Nat := 118140960795 + 1265475 * 2 ^ 59
def prefixEnd_1265475 : Nat := 4983230072969 + 3 ^ 40 * 1265475 * 2
def baseEnd_1265475 : Nat := 649796931248541556942693

theorem tailTrace_1265475 : CollatzResearch.WordTrace tailWord_1265475 prefixEnd_1265475 649796931248541556942693 := by
  unfold tailWord_1265475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46155665090407675768445879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30770443393605117178963919 46155665090407675768445879)
  ·
    refine ⟨69233497635611513652668819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46155665090407675768445879 69233497635611513652668819)
    ·
      refine ⟨103850246453417270479003229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69233497635611513652668819 103850246453417270479003229)
      ·
        refine ⟨38943842420031476429626211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103850246453417270479003229 38943842420031476429626211)
        ·
          refine ⟨58415763630047214644439317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38943842420031476429626211 58415763630047214644439317)
          ·
            refine ⟨2738238920158463186458093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58415763630047214644439317 2738238920158463186458093)
            ·
              refine ⟨1026839595059423694921785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2738238920158463186458093 1026839595059423694921785)
              ·
                refine ⟨770129696294567771191339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026839595059423694921785 770129696294567771191339)
                ·
                  refine ⟨1155194544441851656787009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770129696294567771191339 1155194544441851656787009)
                  ·
                    refine ⟨866395908331388742590257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1155194544441851656787009 866395908331388742590257)
                    ·
                      refine ⟨649796931248541556942693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866395908331388742590257 649796931248541556942693)
                      ·
                        rfl

theorem cell23_1265475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_1265475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265475 prefixEnd_1265475 := by exact prefixLift 1265475
  have htrace : WordTrace (prefixWord ++ tailWord_1265475) baseStart_1265475 baseEnd_1265475 := by
    simpa [prefixWord, tailWord_1265475, baseEnd_1265475] using wordTrace_append hprefix tailTrace_1265475
  have hstable : (prefixWord ++ tailWord_1265475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265475).length < 2 ^ (prefixWord ++ tailWord_1265475).sum := by decide
  have hdescent : baseEnd_1265475 < baseStart_1265475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265485 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1265485 : Nat := 118140960795 + 1265485 * 2 ^ 59
def prefixEnd_1265485 : Nat := 4983230072969 + 3 ^ 40 * 1265485 * 2
def baseEnd_1265485 : Nat := 216600688685028839272549

theorem tailTrace_1265485 : CollatzResearch.WordTrace tailWord_1265485 prefixEnd_1265485 216600688685028839272549 := by
  unfold tailWord_1265485
  simp only [CollatzResearch.WordTrace]
  refine ⟨46156029820371447476309909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30770686546914298317539939 46156029820371447476309909)
  ·
    refine ⟨2163563897829911600452027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46156029820371447476309909 2163563897829911600452027)
    ·
      refine ⟨3245345846744867400678041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163563897829911600452027 3245345846744867400678041)
      ·
        refine ⟨2434009385058650550508531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3245345846744867400678041 2434009385058650550508531)
        ·
          refine ⟨3651014077587975825762797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434009385058650550508531 3651014077587975825762797)
          ·
            refine ⟨1369130279095490934661049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3651014077587975825762797 1369130279095490934661049)
            ·
              refine ⟨1026847709321618200995787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369130279095490934661049 1026847709321618200995787)
              ·
                refine ⟨1540271563982427301493681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026847709321618200995787 1540271563982427301493681)
                ·
                  refine ⟨1155203672986820476120261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1540271563982427301493681 1155203672986820476120261)
                  ·
                    refine ⟨216600688685028839272549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155203672986820476120261 216600688685028839272549)
                    ·
                      rfl

theorem cell23_1265485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1265485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265485 prefixEnd_1265485 := by exact prefixLift 1265485
  have htrace : WordTrace (prefixWord ++ tailWord_1265485) baseStart_1265485 baseEnd_1265485 := by
    simpa [prefixWord, tailWord_1265485, baseEnd_1265485] using wordTrace_append hprefix tailTrace_1265485
  have hstable : (prefixWord ++ tailWord_1265485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265485).length < 2 ^ (prefixWord ++ tailWord_1265485).sum := by decide
  have hdescent : baseEnd_1265485 < baseStart_1265485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265526 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1265526 : Nat := 118140960795 + 1265526 * 2 ^ 59
def prefixEnd_1265526 : Nat := 4983230072969 + 3 ^ 40 * 1265526 * 2
def baseEnd_1265526 : Nat := 649823118761920857404959

theorem tailTrace_1265526 : CollatzResearch.WordTrace tailWord_1265526 prefixEnd_1265526 649823118761920857404959 := by
  unfold tailWord_1265526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884845325826431967409527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30771683475481940985701621 2884845325826431967409527)
  ·
    refine ⟨4327267988739647951114291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884845325826431967409527 4327267988739647951114291)
    ·
      refine ⟨6490901983109471926671437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4327267988739647951114291 6490901983109471926671437)
      ·
        refine ⟨2434088243666051972501789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6490901983109471926671437 2434088243666051972501789)
        ·
          refine ⟨912783091374769489688171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434088243666051972501789 912783091374769489688171)
          ·
            refine ⟨1369174637062154234532257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912783091374769489688171 1369174637062154234532257)
            ·
              refine ⟨1026880977796615675899193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369174637062154234532257 1026880977796615675899193)
              ·
                refine ⟨770160733347461756924395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026880977796615675899193 770160733347461756924395)
                ·
                  refine ⟨1155241100021192635386593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770160733347461756924395 1155241100021192635386593)
                  ·
                    refine ⟨866430825015894476539945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1155241100021192635386593 866430825015894476539945)
                    ·
                      refine ⟨649823118761920857404959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866430825015894476539945 649823118761920857404959)
                      ·
                        rfl

theorem cell23_1265526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1265526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265526 prefixEnd_1265526 := by exact prefixLift 1265526
  have htrace : WordTrace (prefixWord ++ tailWord_1265526) baseStart_1265526 baseEnd_1265526 := by
    simpa [prefixWord, tailWord_1265526, baseEnd_1265526] using wordTrace_append hprefix tailTrace_1265526
  have hstable : (prefixWord ++ tailWord_1265526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265526).length < 2 ^ (prefixWord ++ tailWord_1265526).sum := by decide
  have hdescent : baseEnd_1265526 < baseStart_1265526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265554 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1265554 : Nat := 118140960795 + 1265554 * 2 ^ 59
def prefixEnd_1265554 : Nat := 4983230072969 + 3 ^ 40 * 1265554 * 2
def baseEnd_1265554 : Nat := 72204166246694083094981

theorem tailTrace_1265554 : CollatzResearch.WordTrace tailWord_1265554 prefixEnd_1265554 72204166246694083094981 := by
  unfold tailWord_1265554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539636614280368065142929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30772364304747648173714477 11539636614280368065142929)
  ·
    refine ⟨8654727460710276048857197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11539636614280368065142929 8654727460710276048857197)
    ·
      refine ⟨3245522797766353518321449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8654727460710276048857197 3245522797766353518321449)
      ·
        refine ⟨2434142098324765138741087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3245522797766353518321449 2434142098324765138741087)
        ·
          refine ⟨3651213147487147708111631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434142098324765138741087 3651213147487147708111631)
          ·
            refine ⟨5476819721230721562167447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651213147487147708111631 5476819721230721562167447)
            ·
              refine ⟨8215229581846082343251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476819721230721562167447 8215229581846082343251171)
              ·
                refine ⟨12322844372769123514876757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8215229581846082343251171 12322844372769123514876757)
                ·
                  refine ⟨72204166246694083094981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12322844372769123514876757 72204166246694083094981)
                  ·
                    rfl

theorem cell23_1265554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1265554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265554 prefixEnd_1265554 := by exact prefixLift 1265554
  have htrace : WordTrace (prefixWord ++ tailWord_1265554) baseStart_1265554 baseEnd_1265554 := by
    simpa [prefixWord, tailWord_1265554, baseEnd_1265554] using wordTrace_append hprefix tailTrace_1265554
  have hstable : (prefixWord ++ tailWord_1265554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265554).length < 2 ^ (prefixWord ++ tailWord_1265554).sum := by decide
  have hdescent : baseEnd_1265554 < baseStart_1265554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265577 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_1265577 : Nat := 118140960795 + 1265577 * 2 ^ 59
def prefixEnd_1265577 : Nat := 4983230072969 + 3 ^ 40 * 1265577 * 2
def baseEnd_1265577 : Nat := 649849306275300157867223

theorem tailTrace_1265577 : CollatzResearch.WordTrace tailWord_1265577 prefixEnd_1265577 649849306275300157867223 := by
  unfold tailWord_1265577
  simp only [CollatzResearch.WordTrace]
  refine ⟨46159385336038147188658985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30772923557358764792439323 46159385336038147188658985)
  ·
    refine ⟨34619539002028610391494239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46159385336038147188658985 34619539002028610391494239)
    ·
      refine ⟨51929308503042915587241359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34619539002028610391494239 51929308503042915587241359)
      ·
        refine ⟨77893962754564373380862039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51929308503042915587241359 77893962754564373380862039)
        ·
          refine ⟨116840944131846560071293059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77893962754564373380862039 116840944131846560071293059)
          ·
            refine ⟨175261416197769840106939589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116840944131846560071293059 175261416197769840106939589)
            ·
              refine ⟨32861515537081845020051173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175261416197769840106939589 32861515537081845020051173)
              ·
                refine ⟨6161534163202845941259595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32861515537081845020051173 6161534163202845941259595)
                ·
                  refine ⟨9242301244804268911889393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161534163202845941259595 9242301244804268911889393)
                  ·
                    refine ⟨6931725933603201683917045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9242301244804268911889393 6931725933603201683917045)
                    ·
                      refine ⟨649849306275300157867223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6931725933603201683917045 649849306275300157867223)
                      ·
                        rfl

theorem cell23_1265577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_1265577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265577 prefixEnd_1265577 := by exact prefixLift 1265577
  have htrace : WordTrace (prefixWord ++ tailWord_1265577) baseStart_1265577 baseEnd_1265577 := by
    simpa [prefixWord, tailWord_1265577, baseEnd_1265577] using wordTrace_append hprefix tailTrace_1265577
  have hstable : (prefixWord ++ tailWord_1265577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265577).length < 2 ^ (prefixWord ++ tailWord_1265577).sum := by decide
  have hdescent : baseEnd_1265577 < baseStart_1265577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265588 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1265588 : Nat := 118140960795 + 1265588 * 2 ^ 59
def prefixEnd_1265588 : Nat := 4983230072969 + 3 ^ 40 * 1265588 * 2
def baseEnd_1265588 : Nat := 72206106062499957203297

theorem tailTrace_1265588 : CollatzResearch.WordTrace tailWord_1265588 prefixEnd_1265588 72206106062499957203297 := by
  unfold tailWord_1265588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079893269499148033654709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30773191025998864044872945 23079893269499148033654709)
  ·
    refine ⟨2163739994015545128155129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23079893269499148033654709 2163739994015545128155129)
    ·
      refine ⟨1622804995511658846116347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163739994015545128155129 1622804995511658846116347)
      ·
        refine ⟨2434207493267488269174521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622804995511658846116347 2434207493267488269174521)
        ·
          refine ⟨1825655619950616201880891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434207493267488269174521 1825655619950616201880891)
          ·
            refine ⟨2738483429925924302821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825655619950616201880891 2738483429925924302821337)
            ·
              refine ⟨2053862572444443227116003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738483429925924302821337 2053862572444443227116003)
              ·
                refine ⟨3080793858666664840674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053862572444443227116003 3080793858666664840674005)
                ·
                  refine ⟨72206106062499957203297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3080793858666664840674005 72206106062499957203297)
                  ·
                    rfl

theorem cell23_1265588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1265588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265588 prefixEnd_1265588 := by exact prefixLift 1265588
  have htrace : WordTrace (prefixWord ++ tailWord_1265588) baseStart_1265588 baseEnd_1265588 := by
    simpa [prefixWord, tailWord_1265588, baseEnd_1265588] using wordTrace_append hprefix tailTrace_1265588
  have hstable : (prefixWord ++ tailWord_1265588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265588).length < 2 ^ (prefixWord ++ tailWord_1265588).sum := by decide
  have hdescent : baseEnd_1265588 < baseStart_1265588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265617 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_1265617 : Nat := 118140960795 + 1265617 * 2 ^ 59
def prefixEnd_1265617 : Nat := 4983230072969 + 3 ^ 40 * 1265617 * 2
def baseEnd_1265617 : Nat := 649869845501480001367039

theorem tailTrace_1265617 : CollatzResearch.WordTrace tailWord_1265617 prefixEnd_1265617 649869845501480001367039 := by
  unfold tailWord_1265617
  simp only [CollatzResearch.WordTrace]
  refine ⟨46160844255893234020115105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30773896170595489346743403 46160844255893234020115105)
  ·
    refine ⟨34620633191919925515086329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46160844255893234020115105 34620633191919925515086329)
    ·
      refine ⟨25965474893939944136314747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34620633191919925515086329 25965474893939944136314747)
      ·
        refine ⟨38948212340909916204472121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25965474893939944136314747 38948212340909916204472121)
        ·
          refine ⟨29211159255682437153354091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38948212340909916204472121 29211159255682437153354091)
          ·
            refine ⟨43816738883523655730031137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29211159255682437153354091 43816738883523655730031137)
            ·
              refine ⟨32862554162642741797523353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43816738883523655730031137 32862554162642741797523353)
              ·
                refine ⟨24646915621982056348142515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32862554162642741797523353 24646915621982056348142515)
                ·
                  refine ⟨36970373432973084522213773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24646915621982056348142515 36970373432973084522213773)
                  ·
                    refine ⟨13863890037364906695830165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36970373432973084522213773 13863890037364906695830165)
                    ·
                      refine ⟨649869845501480001367039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13863890037364906695830165 649869845501480001367039)
                      ·
                        rfl

theorem cell23_1265617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_1265617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265617 prefixEnd_1265617 := by exact prefixLift 1265617
  have htrace : WordTrace (prefixWord ++ tailWord_1265617) baseStart_1265617 baseEnd_1265617 := by
    simpa [prefixWord, tailWord_1265617, baseEnd_1265617] using wordTrace_append hprefix tailTrace_1265617
  have hstable : (prefixWord ++ tailWord_1265617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265617).length < 2 ^ (prefixWord ++ tailWord_1265617).sum := by decide
  have hdescent : baseEnd_1265617 < baseStart_1265617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265622 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1265622 : Nat := 118140960795 + 1265622 * 2 ^ 59
def prefixEnd_1265622 : Nat := 4983230072969 + 3 ^ 40 * 1265622 * 2
def baseEnd_1265622 : Nat := 72208045878305831311613

theorem tailTrace_1265622 : CollatzResearch.WordTrace tailWord_1265622 prefixEnd_1265622 72208045878305831311613 := by
  unfold tailWord_1265622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885064163804694992127945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30774017747250079916031413 2885064163804694992127945)
  ·
    refine ⟨2163798122853521244095959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885064163804694992127945 2163798122853521244095959)
    ·
      refine ⟨3245697184280281866143939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163798122853521244095959 3245697184280281866143939)
      ·
        refine ⟨4868545776420422799215909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245697184280281866143939 4868545776420422799215909)
        ·
          refine ⟨912852333078829274852983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4868545776420422799215909 912852333078829274852983)
          ·
            refine ⟨1369278499618243912279475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912852333078829274852983 1369278499618243912279475)
            ·
              refine ⟨2053917749427365868419213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369278499618243912279475 2053917749427365868419213)
              ·
                refine ⟨770219156035262200657205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053917749427365868419213 770219156035262200657205)
                ·
                  refine ⟨72208045878305831311613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770219156035262200657205 72208045878305831311613)
                  ·
                    rfl

theorem cell23_1265622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1265622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265622 prefixEnd_1265622 := by exact prefixLift 1265622
  have htrace : WordTrace (prefixWord ++ tailWord_1265622) baseStart_1265622 baseEnd_1265622 := by
    simpa [prefixWord, tailWord_1265622, baseEnd_1265622] using wordTrace_append hprefix tailTrace_1265622
  have hstable : (prefixWord ++ tailWord_1265622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265622).length < 2 ^ (prefixWord ++ tailWord_1265622).sum := by decide
  have hdescent : baseEnd_1265622 < baseStart_1265622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265624 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1265624 : Nat := 118140960795 + 1265624 * 2 ^ 59
def prefixEnd_1265624 : Nat := 4983230072969 + 3 ^ 40 * 1265624 * 2
def baseEnd_1265624 : Nat := 649873439866061473979507

theorem tailTrace_1265624 : CollatzResearch.WordTrace tailWord_1265624 prefixEnd_1265624 649873439866061473979507 := by
  unfold tailWord_1265624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23080549783433937107809963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30774066377911916143746617 23080549783433937107809963)
  ·
    refine ⟨34620824675150905661714945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23080549783433937107809963 34620824675150905661714945)
    ·
      refine ⟨25965618506363179246286209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34620824675150905661714945 25965618506363179246286209)
      ·
        refine ⟨19474213879772384434714657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25965618506363179246286209 19474213879772384434714657)
        ·
          refine ⟨14605660409829288326035993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19474213879772384434714657 14605660409829288326035993)
          ·
            refine ⟨10954245307371966244526995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14605660409829288326035993 10954245307371966244526995)
            ·
              refine ⟨16431367961057949366790493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10954245307371966244526995 16431367961057949366790493)
              ·
                refine ⟨6161762985396731012546435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16431367961057949366790493 6161762985396731012546435)
                ·
                  refine ⟨9242644478095096518819653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161762985396731012546435 9242644478095096518819653)
                  ·
                    refine ⟨1732995839642830597278685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9242644478095096518819653 1732995839642830597278685)
                    ·
                      refine ⟨649873439866061473979507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1732995839642830597278685 649873439866061473979507)
                      ·
                        rfl

theorem cell23_1265624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1265624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265624 prefixEnd_1265624 := by exact prefixLift 1265624
  have htrace : WordTrace (prefixWord ++ tailWord_1265624) baseStart_1265624 baseEnd_1265624 := by
    simpa [prefixWord, tailWord_1265624, baseEnd_1265624] using wordTrace_append hprefix tailTrace_1265624
  have hstable : (prefixWord ++ tailWord_1265624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265624).length < 2 ^ (prefixWord ++ tailWord_1265624).sum := by decide
  have hdescent : baseEnd_1265624 < baseStart_1265624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265661 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 6]
def baseStart_1265661 : Nat := 118140960795 + 1265661 * 2 ^ 59
def prefixEnd_1265661 : Nat := 4983230072969 + 3 ^ 40 * 1265661 * 2
def baseEnd_1265661 : Nat := 72210270961141981024093

theorem tailTrace_1265661 : CollatzResearch.WordTrace tailWord_1265661 prefixEnd_1265661 72210270961141981024093 := by
  unfold tailWord_1265661
  simp only [CollatzResearch.WordTrace]
  refine ⟨46162449067733829534716837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30774966045155886356477891 46162449067733829534716837)
  ·
    refine ⟨8655459200200093037759407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46162449067733829534716837 8655459200200093037759407)
    ·
      refine ⟨12983188800300139556639111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8655459200200093037759407 12983188800300139556639111)
      ·
        refine ⟨19474783200450209334958667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12983188800300139556639111 19474783200450209334958667)
        ·
          refine ⟨29212174800675314002438001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19474783200450209334958667 29212174800675314002438001)
          ·
            refine ⟨21909131100506485501828501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29212174800675314002438001 21909131100506485501828501)
            ·
              refine ⟨1026990520336241507898211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21909131100506485501828501 1026990520336241507898211)
              ·
                refine ⟨1540485780504362261847317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026990520336241507898211 1540485780504362261847317)
                ·
                  refine ⟨72210270961141981024093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1540485780504362261847317 72210270961141981024093)
                  ·
                    rfl

theorem cell23_1265661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_1265661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265661 prefixEnd_1265661 := by exact prefixLift 1265661
  have htrace : WordTrace (prefixWord ++ tailWord_1265661) baseStart_1265661 baseEnd_1265661 := by
    simpa [prefixWord, tailWord_1265661, baseEnd_1265661] using wordTrace_append hprefix tailTrace_1265661
  have hstable : (prefixWord ++ tailWord_1265661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265661).length < 2 ^ (prefixWord ++ tailWord_1265661).sum := by decide
  have hdescent : baseEnd_1265661 < baseStart_1265661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265698 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_1265698 : Nat := 118140960795 + 1265698 * 2 ^ 59
def prefixEnd_1265698 : Nat := 4983230072969 + 3 ^ 40 * 1265698 * 2
def baseEnd_1265698 : Nat := 649911437434494184454167

theorem tailTrace_1265698 : CollatzResearch.WordTrace tailWord_1265698 prefixEnd_1265698 649911437434494184454167 := by
  unfold tailWord_1265698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11540949642149946213453437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30775865712399856569209165 11540949642149946213453437)
  ·
    refine ⟨4327856115806229830045039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11540949642149946213453437 4327856115806229830045039)
    ·
      refine ⟨6491784173709344745067559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4327856115806229830045039 6491784173709344745067559)
      ·
        refine ⟨9737676260564017117601339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491784173709344745067559 9737676260564017117601339)
        ·
          refine ⟨14606514390846025676402009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9737676260564017117601339 14606514390846025676402009)
          ·
            refine ⟨10954885793134519257301507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14606514390846025676402009 10954885793134519257301507)
            ·
              refine ⟨16432328689701778885952261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10954885793134519257301507 16432328689701778885952261)
              ·
                refine ⟨3081061629319083541116049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16432328689701778885952261 3081061629319083541116049)
                ·
                  refine ⟨2310796221989312655837037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081061629319083541116049 2310796221989312655837037)
                  ·
                    refine ⟨866548583245992245938889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310796221989312655837037 866548583245992245938889)
                    ·
                      refine ⟨649911437434494184454167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866548583245992245938889 649911437434494184454167)
                      ·
                        rfl

theorem cell23_1265698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_1265698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265698 prefixEnd_1265698 := by exact prefixLift 1265698
  have htrace : WordTrace (prefixWord ++ tailWord_1265698) baseStart_1265698 baseEnd_1265698 := by
    simpa [prefixWord, tailWord_1265698, baseEnd_1265698] using wordTrace_append hprefix tailTrace_1265698
  have hstable : (prefixWord ++ tailWord_1265698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265698).length < 2 ^ (prefixWord ++ tailWord_1265698).sum := by decide
  have hdescent : baseEnd_1265698 < baseStart_1265698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265728 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2]
def baseStart_1265728 : Nat := 118140960795 + 1265728 * 2 ^ 59
def prefixEnd_1265728 : Nat := 4983230072969 + 3 ^ 40 * 1265728 * 2
def baseEnd_1265728 : Nat := 649926841854129067079029

theorem tailTrace_1265728 : CollatzResearch.WordTrace tailWord_1265728 prefixEnd_1265728 649926841854129067079029 := by
  unfold tailWord_1265728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23082446379245549988702919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30776595172327399984937225 23082446379245549988702919)
  ·
    refine ⟨34623669568868324983054379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23082446379245549988702919 34623669568868324983054379)
    ·
      refine ⟨51935504353302487474581569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34623669568868324983054379 51935504353302487474581569)
      ·
        refine ⟨38951628264976865605936177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51935504353302487474581569 38951628264976865605936177)
        ·
          refine ⟨29213721198732649204452133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38951628264976865605936177 29213721198732649204452133)
          ·
            refine ⟨5477572724762371725834775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29213721198732649204452133 5477572724762371725834775)
            ·
              refine ⟨8216359087143557588752163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477572724762371725834775 8216359087143557588752163)
              ·
                refine ⟨12324538630715336383128245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216359087143557588752163 12324538630715336383128245)
                ·
                  refine ⟨1155425496629562785918273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12324538630715336383128245 1155425496629562785918273)
                  ·
                    refine ⟨866569122472172089438705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1155425496629562785918273 866569122472172089438705)
                    ·
                      refine ⟨649926841854129067079029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866569122472172089438705 649926841854129067079029)
                      ·
                        rfl

theorem cell23_1265728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_1265728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265728 prefixEnd_1265728 := by exact prefixLift 1265728
  have htrace : WordTrace (prefixWord ++ tailWord_1265728) baseStart_1265728 baseEnd_1265728 := by
    simpa [prefixWord, tailWord_1265728, baseEnd_1265728] using wordTrace_append hprefix tailTrace_1265728
  have hstable : (prefixWord ++ tailWord_1265728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265728).length < 2 ^ (prefixWord ++ tailWord_1265728).sum := by decide
  have hdescent : baseEnd_1265728 < baseStart_1265728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265764 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1265764 : Nat := 118140960795 + 1265764 * 2 ^ 59
def prefixEnd_1265764 : Nat := 4983230072969 + 3 ^ 40 * 1265764 * 2
def baseEnd_1265764 : Nat := 216648442385896975409621

theorem tailTrace_1265764 : CollatzResearch.WordTrace tailWord_1265764 prefixEnd_1265764 216648442385896975409621 := by
  unfold tailWord_1265764
  simp only [CollatzResearch.WordTrace]
  refine ⟨23083102893180339062858173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30777470524240452083810897 23083102893180339062858173)
  ·
    refine ⟨8656163584942627148571815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23083102893180339062858173 8656163584942627148571815)
    ·
      refine ⟨12984245377413940722857723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656163584942627148571815 12984245377413940722857723)
      ·
        refine ⟨19476368066120911084286585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12984245377413940722857723 19476368066120911084286585)
        ·
          refine ⟨14607276049590683313214939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19476368066120911084286585 14607276049590683313214939)
          ·
            refine ⟨21910914074386024969822409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14607276049590683313214939 21910914074386024969822409)
            ·
              refine ⟨16433185555789518727366807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21910914074386024969822409 16433185555789518727366807)
              ·
                refine ⟨24649778333684278091050211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16433185555789518727366807 24649778333684278091050211)
                ·
                  refine ⟨36974667500526417136575317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24649778333684278091050211 36974667500526417136575317)
                  ·
                    refine ⟨216648442385896975409621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 36974667500526417136575317 216648442385896975409621)
                    ·
                      rfl

theorem cell23_1265764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1265764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265764 prefixEnd_1265764 := by exact prefixLift 1265764
  have htrace : WordTrace (prefixWord ++ tailWord_1265764) baseStart_1265764 baseEnd_1265764 := by
    simpa [prefixWord, tailWord_1265764, baseEnd_1265764] using wordTrace_append hprefix tailTrace_1265764
  have hstable : (prefixWord ++ tailWord_1265764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265764).length < 2 ^ (prefixWord ++ tailWord_1265764).sum := by decide
  have hdescent : baseEnd_1265764 < baseStart_1265764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265778 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1265778 : Nat := 118140960795 + 1265778 * 2 ^ 59
def prefixEnd_1265778 : Nat := 4983230072969 + 3 ^ 40 * 1265778 * 2
def baseEnd_1265778 : Nat := 649952515886853871453799

theorem tailTrace_1265778 : CollatzResearch.WordTrace tailWord_1265778 prefixEnd_1265778 649952515886853871453799 := by
  unfold tailWord_1265778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541679102077489629181497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30777810938873305677817325 11541679102077489629181497)
  ·
    refine ⟨8656259326558117221886123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11541679102077489629181497 8656259326558117221886123)
    ·
      refine ⟨12984388989837175832829185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656259326558117221886123 12984388989837175832829185)
      ·
        refine ⟨9738291742377881874621889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12984388989837175832829185 9738291742377881874621889)
        ·
          refine ⟨7303718806783411405966417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9738291742377881874621889 7303718806783411405966417)
          ·
            refine ⟨5477789105087558554474813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303718806783411405966417 5477789105087558554474813)
            ·
              refine ⟨2054170914407834457928055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5477789105087558554474813 2054170914407834457928055)
              ·
                refine ⟨3081256371611751686892083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054170914407834457928055 3081256371611751686892083)
                ·
                  refine ⟨4621884557417627530338125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081256371611751686892083 4621884557417627530338125)
                  ·
                    refine ⟨1733206709031610323876797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4621884557417627530338125 1733206709031610323876797)
                    ·
                      refine ⟨649952515886853871453799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733206709031610323876797 649952515886853871453799)
                      ·
                        rfl

theorem cell23_1265778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1265778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265778 prefixEnd_1265778 := by exact prefixLift 1265778
  have htrace : WordTrace (prefixWord ++ tailWord_1265778) baseStart_1265778 baseEnd_1265778 := by
    simpa [prefixWord, tailWord_1265778, baseEnd_1265778] using wordTrace_append hprefix tailTrace_1265778
  have hstable : (prefixWord ++ tailWord_1265778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265778).length < 2 ^ (prefixWord ++ tailWord_1265778).sum := by decide
  have hdescent : baseEnd_1265778 < baseStart_1265778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265871 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 2, 5]
def baseStart_1265871 : Nat := 118140960795 + 1265871 * 2 ^ 59
def prefixEnd_1265871 : Nat := 4983230072969 + 3 ^ 40 * 1265871 * 2
def baseEnd_1265871 : Nat := 216666756529240669196957

theorem tailTrace_1265871 : CollatzResearch.WordTrace tailWord_1265871 prefixEnd_1265871 216666756529240669196957 := by
  unfold tailWord_1265871
  simp only [CollatzResearch.WordTrace]
  refine ⟨46170108396973035399861467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30780072264648690266574311 46170108396973035399861467)
  ·
    refine ⟨69255162595459553099792201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46170108396973035399861467 69255162595459553099792201)
    ·
      refine ⟨51941371946594664824844151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69255162595459553099792201 51941371946594664824844151)
      ·
        refine ⟨77912057919891997237266227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51941371946594664824844151 77912057919891997237266227)
        ·
          refine ⟨116868086879837995855899341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77912057919891997237266227 116868086879837995855899341)
          ·
            refine ⟨43825532579939248445962253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116868086879837995855899341 43825532579939248445962253)
            ·
              refine ⟨16434574717477218167235845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43825532579939248445962253 16434574717477218167235845)
              ·
                refine ⟨3081482759526978406356721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16434574717477218167235845 3081482759526978406356721)
                ·
                  refine ⟨2311112069645233804767541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081482759526978406356721 2311112069645233804767541)
                  ·
                    refine ⟨216666756529240669196957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2311112069645233804767541 216666756529240669196957)
                    ·
                      rfl

theorem cell23_1265871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_1265871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265871 prefixEnd_1265871 := by exact prefixLift 1265871
  have htrace : WordTrace (prefixWord ++ tailWord_1265871) baseStart_1265871 baseEnd_1265871 := by
    simpa [prefixWord, tailWord_1265871, baseEnd_1265871] using wordTrace_append hprefix tailTrace_1265871
  have hstable : (prefixWord ++ tailWord_1265871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265871).length < 2 ^ (prefixWord ++ tailWord_1265871).sum := by decide
  have hdescent : baseEnd_1265871 < baseStart_1265871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265881 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1265881 : Nat := 118140960795 + 1265881 * 2 ^ 59
def prefixEnd_1265881 : Nat := 4983230072969 + 3 ^ 40 * 1265881 * 2
def baseEnd_1265881 : Nat := 650005404394266968465825

theorem tailTrace_1265881 : CollatzResearch.WordTrace tailWord_1265881 prefixEnd_1265881 650005404394266968465825 := by
  unfold tailWord_1265881
  simp only [CollatzResearch.WordTrace]
  refine ⟨46170473126936807107725497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30780315417957871405150331 46170473126936807107725497)
  ·
    refine ⟨34627854845202605330794123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46170473126936807107725497 34627854845202605330794123)
    ·
      refine ⟨51941782267803907996191185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34627854845202605330794123 51941782267803907996191185)
      ·
        refine ⟨38956336700852930997143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51941782267803907996191185 38956336700852930997143389)
        ·
          refine ⟨14608626262819849123928771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38956336700852930997143389 14608626262819849123928771)
          ·
            refine ⟨21912939394229773685893157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608626262819849123928771 21912939394229773685893157)
            ·
              refine ⟨4108676136418082566104967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21912939394229773685893157 4108676136418082566104967)
              ·
                refine ⟨6163014204627123849157451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108676136418082566104967 6163014204627123849157451)
                ·
                  refine ⟨9244521306940685773736177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163014204627123849157451 9244521306940685773736177)
                  ·
                    refine ⟨6933390980205514330302133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9244521306940685773736177 6933390980205514330302133)
                    ·
                      refine ⟨650005404394266968465825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6933390980205514330302133 650005404394266968465825)
                      ·
                        rfl

theorem cell23_1265881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1265881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265881 prefixEnd_1265881 := by exact prefixLift 1265881
  have htrace : WordTrace (prefixWord ++ tailWord_1265881) baseStart_1265881 baseEnd_1265881 := by
    simpa [prefixWord, tailWord_1265881, baseEnd_1265881] using wordTrace_append hprefix tailTrace_1265881
  have hstable : (prefixWord ++ tailWord_1265881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265881).length < 2 ^ (prefixWord ++ tailWord_1265881).sum := by decide
  have hdescent : baseEnd_1265881 < baseStart_1265881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265885 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1265885 : Nat := 118140960795 + 1265885 * 2 ^ 59
def prefixEnd_1265885 : Nat := 4983230072969 + 3 ^ 40 * 1265885 * 2
def baseEnd_1265885 : Nat := 650007458316884952815807

theorem tailTrace_1265885 : CollatzResearch.WordTrace tailWord_1265885 prefixEnd_1265885 650007458316884952815807 := by
  unfold tailWord_1265885
  simp only [CollatzResearch.WordTrace]
  refine ⟨46170619018922315790871109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30780412679281543860580739 46170619018922315790871109)
  ·
    refine ⟨8656991066047934210788333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46170619018922315790871109 8656991066047934210788333)
    ·
      refine ⟨3246371649767975329045625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8656991066047934210788333 3246371649767975329045625)
      ·
        refine ⟨2434778737325981496784219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246371649767975329045625 2434778737325981496784219)
        ·
          refine ⟨3652168105988972245176329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434778737325981496784219 3652168105988972245176329)
          ·
            refine ⟨2739126079491729183882247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3652168105988972245176329 2739126079491729183882247)
            ·
              refine ⟨4108689119237593775823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739126079491729183882247 4108689119237593775823371)
              ·
                refine ⟨6163033678856390663735057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108689119237593775823371 6163033678856390663735057)
                ·
                  refine ⟨4622275259142292997801293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6163033678856390663735057 4622275259142292997801293)
                  ·
                    refine ⟨1733353222178359874175485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4622275259142292997801293 1733353222178359874175485)
                    ·
                      refine ⟨650007458316884952815807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733353222178359874175485 650007458316884952815807)
                      ·
                        rfl

theorem cell23_1265885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1265885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265885 prefixEnd_1265885 := by exact prefixLift 1265885
  have htrace : WordTrace (prefixWord ++ tailWord_1265885) baseStart_1265885 baseEnd_1265885 := by
    simpa [prefixWord, tailWord_1265885, baseEnd_1265885] using wordTrace_append hprefix tailTrace_1265885
  have hstable : (prefixWord ++ tailWord_1265885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265885).length < 2 ^ (prefixWord ++ tailWord_1265885).sum := by decide
  have hdescent : baseEnd_1265885 < baseStart_1265885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265921 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1265921 : Nat := 118140960795 + 1265921 * 2 ^ 59
def prefixEnd_1265921 : Nat := 4983230072969 + 3 ^ 40 * 1265921 * 2
def baseEnd_1265921 : Nat := 650025943620446811965641

theorem tailTrace_1265921 : CollatzResearch.WordTrace tailWord_1265921 prefixEnd_1265921 650025943620446811965641 := by
  unfold tailWord_1265921
  simp only [CollatzResearch.WordTrace]
  refine ⟨46171932046791893939181617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30781288031194595959454411 46171932046791893939181617)
  ·
    refine ⟨34628949035093920454386213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46171932046791893939181617 34628949035093920454386213)
    ·
      refine ⟨6492927944080110085197415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34628949035093920454386213 6492927944080110085197415)
      ·
        refine ⟨9739391916120165127796123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6492927944080110085197415 9739391916120165127796123)
        ·
          refine ⟨14609087874180247691694185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739391916120165127796123 14609087874180247691694185)
          ·
            refine ⟨10956815905635185768770639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14609087874180247691694185 10956815905635185768770639)
            ·
              refine ⟨16435223858452778653155959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10956815905635185768770639 16435223858452778653155959)
              ·
                refine ⟨24652835787679167979733939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16435223858452778653155959 24652835787679167979733939)
                ·
                  refine ⟨36979253681518751969600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24652835787679167979733939 36979253681518751969600909)
                  ·
                    refine ⟨13867220130569531988600341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36979253681518751969600909 13867220130569531988600341)
                    ·
                      refine ⟨650025943620446811965641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13867220130569531988600341 650025943620446811965641)
                      ·
                        rfl

theorem cell23_1265921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1265921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265921 prefixEnd_1265921 := by exact prefixLift 1265921
  have htrace : WordTrace (prefixWord ++ tailWord_1265921) baseStart_1265921 baseEnd_1265921 := by
    simpa [prefixWord, tailWord_1265921, baseEnd_1265921] using wordTrace_append hprefix tailTrace_1265921
  have hstable : (prefixWord ++ tailWord_1265921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265921).length < 2 ^ (prefixWord ++ tailWord_1265921).sum := by decide
  have hdescent : baseEnd_1265921 < baseStart_1265921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265931 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 8]
def baseStart_1265931 : Nat := 118140960795 + 1265931 * 2 ^ 59
def prefixEnd_1265931 : Nat := 4983230072969 + 3 ^ 40 * 1265931 * 2
def baseEnd_1265931 : Nat := 72225675380776863648955

theorem tailTrace_1265931 : CollatzResearch.WordTrace tailWord_1265931 prefixEnd_1265931 72225675380776863648955 := by
  unfold tailWord_1265931
  simp only [CollatzResearch.WordTrace]
  refine ⟨46172296776755665647045647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30781531184503777098030431 46172296776755665647045647)
  ·
    refine ⟨69258445165133498470568471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46172296776755665647045647 69258445165133498470568471)
    ·
      refine ⟨103887667747700247705852707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69258445165133498470568471 103887667747700247705852707)
      ·
        refine ⟨155831501621550371558779061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103887667747700247705852707 155831501621550371558779061)
        ·
          refine ⟨14609203277020347333635537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155831501621550371558779061 14609203277020347333635537)
          ·
            refine ⟨10956902457765260500226653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14609203277020347333635537 10956902457765260500226653)
            ·
              refine ⟨4108838421661972687584995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10956902457765260500226653 4108838421661972687584995)
              ·
                refine ⟨6163257632492959031377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108838421661972687584995 6163257632492959031377493)
                ·
                  refine ⟨72225675380776863648955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6163257632492959031377493 72225675380776863648955)
                  ·
                    rfl

theorem cell23_1265931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 8].length) (baseStart_1265931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265931 prefixEnd_1265931 := by exact prefixLift 1265931
  have htrace : WordTrace (prefixWord ++ tailWord_1265931) baseStart_1265931 baseEnd_1265931 := by
    simpa [prefixWord, tailWord_1265931, baseEnd_1265931] using wordTrace_append hprefix tailTrace_1265931
  have hstable : (prefixWord ++ tailWord_1265931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265931).length < 2 ^ (prefixWord ++ tailWord_1265931).sum := by decide
  have hdescent : baseEnd_1265931 < baseStart_1265931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265969 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 1, 4]
def baseStart_1265969 : Nat := 118140960795 + 1265969 * 2 ^ 59
def prefixEnd_1265969 : Nat := 4983230072969 + 3 ^ 40 * 1265969 * 2
def baseEnd_1265969 : Nat := 216683530230620874721807

theorem tailTrace_1265969 : CollatzResearch.WordTrace tailWord_1265969 prefixEnd_1265969 216683530230620874721807 := by
  unfold tailWord_1265969
  simp only [CollatzResearch.WordTrace]
  refine ⟨46173682750617998136928961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30782455167078665424619307 46173682750617998136928961)
  ·
    refine ⟨34630262062963498602696721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46173682750617998136928961 34630262062963498602696721)
    ·
      refine ⟨25972696547222623952022541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34630262062963498602696721 25972696547222623952022541)
      ·
        refine ⟨9739761205208483982008453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25972696547222623952022541 9739761205208483982008453)
        ·
          refine ⟨1826205225976590746626585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9739761205208483982008453 1826205225976590746626585)
          ·
            refine ⟨1369653919482443059969939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826205225976590746626585 1369653919482443059969939)
            ·
              refine ⟨2054480879223664589954909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369653919482443059969939 2054480879223664589954909)
              ·
                refine ⟨770430329708874221233091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2054480879223664589954909 770430329708874221233091)
                ·
                  refine ⟨1155645494563311331849637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770430329708874221233091 1155645494563311331849637)
                  ·
                    refine ⟨216683530230620874721807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155645494563311331849637 216683530230620874721807)
                    ·
                      rfl

theorem cell23_1265969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_1265969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265969 prefixEnd_1265969 := by exact prefixLift 1265969
  have htrace : WordTrace (prefixWord ++ tailWord_1265969) baseStart_1265969 baseEnd_1265969 := by
    simpa [prefixWord, tailWord_1265969, baseEnd_1265969] using wordTrace_append hprefix tailTrace_1265969
  have hstable : (prefixWord ++ tailWord_1265969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265969).length < 2 ^ (prefixWord ++ tailWord_1265969).sum := by decide
  have hdescent : baseEnd_1265969 < baseStart_1265969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1265992 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_1265992 : Nat := 118140960795 + 1265992 * 2 ^ 59
def prefixEnd_1265992 : Nat := 4983230072969 + 3 ^ 40 * 1265992 * 2
def baseEnd_1265992 : Nat := 650062400746916034177815

theorem tailTrace_1265992 : CollatzResearch.WordTrace tailWord_1265992 prefixEnd_1265992 650062400746916034177815 := by
  unfold tailWord_1265992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087260814767336532508115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30783014419689782043344153 23087260814767336532508115)
  ·
    refine ⟨34630891222151004798762173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087260814767336532508115 34630891222151004798762173)
    ·
      refine ⟨12986584208306626799535815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34630891222151004798762173 12986584208306626799535815)
      ·
        refine ⟨19479876312459940199303723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12986584208306626799535815 19479876312459940199303723)
        ·
          refine ⟨29219814468689910298955585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19479876312459940199303723 29219814468689910298955585)
          ·
            refine ⟨21914860851517432724216689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29219814468689910298955585 21914860851517432724216689)
            ·
              refine ⟨16436145638638074543162517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21914860851517432724216689 16436145638638074543162517)
              ·
                refine ⟨770444326811159744210743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16436145638638074543162517 770444326811159744210743)
                ·
                  refine ⟨1155666490216739616316115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770444326811159744210743 1155666490216739616316115)
                  ·
                    refine ⟨1733499735325109424474173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155666490216739616316115 1733499735325109424474173)
                    ·
                      refine ⟨650062400746916034177815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733499735325109424474173 650062400746916034177815)
                      ·
                        rfl

theorem cell23_1265992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_1265992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1265992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1265992 prefixEnd_1265992 := by exact prefixLift 1265992
  have htrace : WordTrace (prefixWord ++ tailWord_1265992) baseStart_1265992 baseEnd_1265992 := by
    simpa [prefixWord, tailWord_1265992, baseEnd_1265992] using wordTrace_append hprefix tailTrace_1265992
  have hstable : (prefixWord ++ tailWord_1265992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1265992).length < 2 ^ (prefixWord ++ tailWord_1265992).sum := by decide
  have hdescent : baseEnd_1265992 < baseStart_1265992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1265992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266008 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_1266008 : Nat := 118140960795 + 1266008 * 2 ^ 59
def prefixEnd_1266008 : Nat := 4983230072969 + 3 ^ 40 * 1266008 * 2
def baseEnd_1266008 : Nat := 216690205479129323859247

theorem tailTrace_1266008 : CollatzResearch.WordTrace tailWord_1266008 prefixEnd_1266008 216690205479129323859247 := by
  unfold tailWord_1266008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087552598738353898799339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30783403464984471865065785 23087552598738353898799339)
  ·
    refine ⟨34631328898107530848199009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087552598738353898799339 34631328898107530848199009)
    ·
      refine ⟨25973496673580648136149257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34631328898107530848199009 25973496673580648136149257)
      ·
        refine ⟨19480122505185486102111943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25973496673580648136149257 19480122505185486102111943)
        ·
          refine ⟨29220183757778229153167915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19480122505185486102111943 29220183757778229153167915)
          ·
            refine ⟨43830275636667343729751873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29220183757778229153167915 43830275636667343729751873)
            ·
              refine ⟨32872706727500507797313905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43830275636667343729751873 32872706727500507797313905)
              ·
                refine ⟨24654530045625380847985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32872706727500507797313905 24654530045625380847985429)
                ·
                  refine ⟨1155681095888689727249317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24654530045625380847985429 1155681095888689727249317)
                  ·
                    refine ⟨216690205479129323859247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1155681095888689727249317 216690205479129323859247)
                    ·
                      rfl

theorem cell23_1266008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_1266008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266008 prefixEnd_1266008 := by exact prefixLift 1266008
  have htrace : WordTrace (prefixWord ++ tailWord_1266008) baseStart_1266008 baseEnd_1266008 := by
    simpa [prefixWord, tailWord_1266008, baseEnd_1266008] using wordTrace_append hprefix tailTrace_1266008
  have hstable : (prefixWord ++ tailWord_1266008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266008).length < 2 ^ (prefixWord ++ tailWord_1266008).sum := by decide
  have hdescent : baseEnd_1266008 < baseStart_1266008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266012 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1266012 : Nat := 118140960795 + 1266012 * 2 ^ 59
def prefixEnd_1266012 : Nat := 4983230072969 + 3 ^ 40 * 1266012 * 2
def baseEnd_1266012 : Nat := 216690890120001985309241

theorem tailTrace_1266012 : CollatzResearch.WordTrace tailWord_1266012 prefixEnd_1266012 216690890120001985309241 := by
  unfold tailWord_1266012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087625544731108240372145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30783500726308144320496193 23087625544731108240372145)
  ·
    refine ⟨17315719158548331180279109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23087625544731108240372145 17315719158548331180279109)
    ·
      refine ⟨3246697342227812096302333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17315719158548331180279109 3246697342227812096302333)
      ·
        refine ⟨1217511503335429536113375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3246697342227812096302333 1217511503335429536113375)
        ·
          refine ⟨1826267255003144304170063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217511503335429536113375 1826267255003144304170063)
          ·
            refine ⟨2739400882504716456255095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826267255003144304170063 2739400882504716456255095)
            ·
              refine ⟨4109101323757074684382643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739400882504716456255095 4109101323757074684382643)
              ·
                refine ⟨6163651985635612026573965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109101323757074684382643 6163651985635612026573965)
                ·
                  refine ⟨2311369494613354509965237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6163651985635612026573965 2311369494613354509965237)
                  ·
                    refine ⟨216690890120001985309241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2311369494613354509965237 216690890120001985309241)
                    ·
                      rfl

theorem cell23_1266012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1266012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266012 prefixEnd_1266012 := by exact prefixLift 1266012
  have htrace : WordTrace (prefixWord ++ tailWord_1266012) baseStart_1266012 baseEnd_1266012 := by
    simpa [prefixWord, tailWord_1266012, baseEnd_1266012] using wordTrace_append hprefix tailTrace_1266012
  have hstable : (prefixWord ++ tailWord_1266012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266012).length < 2 ^ (prefixWord ++ tailWord_1266012).sum := by decide
  have hdescent : baseEnd_1266012 < baseStart_1266012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266015 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1266015 : Nat := 118140960795 + 1266015 * 2 ^ 59
def prefixEnd_1266015 : Nat := 4983230072969 + 3 ^ 40 * 1266015 * 2
def baseEnd_1266015 : Nat := 650074210801969444190209

theorem tailTrace_1266015 : CollatzResearch.WordTrace tailWord_1266015 prefixEnd_1266015 650074210801969444190209 := by
  unfold tailWord_1266015
  simp only [CollatzResearch.WordTrace]
  refine ⟨46175360508451347993103499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30783573672300898662068999 46175360508451347993103499)
  ·
    refine ⟨69263040762677021989655249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46175360508451347993103499 69263040762677021989655249)
    ·
      refine ⟨51947280572007766492241437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69263040762677021989655249 51947280572007766492241437)
      ·
        refine ⟨19480230214502912434590539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51947280572007766492241437 19480230214502912434590539)
        ·
          refine ⟨29220345321754368651885809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19480230214502912434590539 29220345321754368651885809)
          ·
            refine ⟨21915258991315776488914357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29220345321754368651885809 21915258991315776488914357)
            ·
              refine ⟨2054555530435854045835721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21915258991315776488914357 2054555530435854045835721)
              ·
                refine ⟨1540916647826890534376791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054555530435854045835721 1540916647826890534376791)
                ·
                  refine ⟨2311374971740335801565187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540916647826890534376791 2311374971740335801565187)
                  ·
                    refine ⟨3467062457610503702347781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311374971740335801565187 3467062457610503702347781)
                    ·
                      refine ⟨650074210801969444190209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467062457610503702347781 650074210801969444190209)
                      ·
                        rfl

theorem cell23_1266015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1266015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266015 prefixEnd_1266015 := by exact prefixLift 1266015
  have htrace : WordTrace (prefixWord ++ tailWord_1266015) baseStart_1266015 baseEnd_1266015 := by
    simpa [prefixWord, tailWord_1266015, baseEnd_1266015] using wordTrace_append hprefix tailTrace_1266015
  have hstable : (prefixWord ++ tailWord_1266015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266015).length < 2 ^ (prefixWord ++ tailWord_1266015).sum := by decide
  have hdescent : baseEnd_1266015 < baseStart_1266015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266032 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4]
def baseStart_1266032 : Nat := 118140960795 + 1266032 * 2 ^ 59
def prefixEnd_1266032 : Nat := 4983230072969 + 3 ^ 40 * 1266032 * 2
def baseEnd_1266032 : Nat := 650082939973095877677631

theorem tailTrace_1266032 : CollatzResearch.WordTrace tailWord_1266032 prefixEnd_1266032 650082939973095877677631 := by
  unfold tailWord_1266032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087990274694879948236175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30783987032926506597648233 23087990274694879948236175)
  ·
    refine ⟨34631985412042319922354263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087990274694879948236175 34631985412042319922354263)
    ·
      refine ⟨51947978118063479883531395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34631985412042319922354263 51947978118063479883531395)
      ·
        refine ⟨77921967177095219825297093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51947978118063479883531395 77921967177095219825297093)
        ·
          refine ⟨14610368845705353717243205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77921967177095219825297093 14610368845705353717243205)
          ·
            refine ⟨2739444158569753821983101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14610368845705353717243205 2739444158569753821983101)
            ·
              refine ⟨1027291559463657683243663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2739444158569753821983101 1027291559463657683243663)
              ·
                refine ⟨1540937339195486524865495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027291559463657683243663 1540937339195486524865495)
                ·
                  refine ⟨2311406008793229787298243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540937339195486524865495 2311406008793229787298243)
                  ·
                    refine ⟨3467109013189844680947365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311406008793229787298243 3467109013189844680947365)
                    ·
                      refine ⟨650082939973095877677631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467109013189844680947365 650082939973095877677631)
                      ·
                        rfl

theorem cell23_1266032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 1, 4].length) (baseStart_1266032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266032 prefixEnd_1266032 := by exact prefixLift 1266032
  have htrace : WordTrace (prefixWord ++ tailWord_1266032) baseStart_1266032 baseEnd_1266032 := by
    simpa [prefixWord, tailWord_1266032, baseEnd_1266032] using wordTrace_append hprefix tailTrace_1266032
  have hstable : (prefixWord ++ tailWord_1266032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266032).length < 2 ^ (prefixWord ++ tailWord_1266032).sum := by decide
  have hdescent : baseEnd_1266032 < baseStart_1266032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266062 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1266062 : Nat := 118140960795 + 1266062 * 2 ^ 59
def prefixEnd_1266062 : Nat := 4983230072969 + 3 ^ 40 * 1266062 * 2
def baseEnd_1266062 : Nat := 650098344392730760302493

theorem tailTrace_1266062 : CollatzResearch.WordTrace tailWord_1266062 prefixEnd_1266062 650098344392730760302493 := by
  unfold tailWord_1266062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772134342410134377508055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30784716492854050013376293 5772134342410134377508055)
  ·
    refine ⟨8658201513615201566262083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5772134342410134377508055 8658201513615201566262083)
    ·
      refine ⟨12987302270422802349393125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658201513615201566262083 12987302270422802349393125)
      ·
        refine ⟨2435119175704275440511211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12987302270422802349393125 2435119175704275440511211)
        ·
          refine ⟨3652678763556413160766817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435119175704275440511211 3652678763556413160766817)
          ·
            refine ⟨2739509072667309870575113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3652678763556413160766817 2739509072667309870575113)
            ·
              refine ⟨2054631804500482402931335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739509072667309870575113 2054631804500482402931335)
              ·
                refine ⟨3081947706750723604397003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054631804500482402931335 3081947706750723604397003)
                ·
                  refine ⟨4622921560126085406595505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081947706750723604397003 4622921560126085406595505)
                  ·
                    refine ⟨3467191170094564054946629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622921560126085406595505 3467191170094564054946629)
                    ·
                      refine ⟨650098344392730760302493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467191170094564054946629 650098344392730760302493)
                      ·
                        rfl

theorem cell23_1266062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1266062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266062 prefixEnd_1266062 := by exact prefixLift 1266062
  have htrace : WordTrace (prefixWord ++ tailWord_1266062) baseStart_1266062 baseEnd_1266062 := by
    simpa [prefixWord, tailWord_1266062, baseEnd_1266062] using wordTrace_append hprefix tailTrace_1266062
  have hstable : (prefixWord ++ tailWord_1266062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266062).length < 2 ^ (prefixWord ++ tailWord_1266062).sum := by decide
  have hdescent : baseEnd_1266062 < baseStart_1266062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266070 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1266070 : Nat := 118140960795 + 1266070 * 2 ^ 59
def prefixEnd_1266070 : Nat := 4983230072969 + 3 ^ 40 * 1266070 * 2
def baseEnd_1266070 : Nat := 650102452237966729002457

theorem tailTrace_1266070 : CollatzResearch.WordTrace tailWord_1266070 prefixEnd_1266070 650102452237966729002457 := by
  unfold tailWord_1266070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886085407703255774147229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30784911015501394924237109 2886085407703255774147229)
  ·
    refine ⟨1082282027888720915305211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2886085407703255774147229 1082282027888720915305211)
    ·
      refine ⟨1623423041833081372957817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082282027888720915305211 1623423041833081372957817)
      ·
        refine ⟨1217567281374811029718363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623423041833081372957817 1217567281374811029718363)
        ·
          refine ⟨1826350922062216544577545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217567281374811029718363 1826350922062216544577545)
          ·
            refine ⟨1369763191546662408433159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826350922062216544577545 1369763191546662408433159)
            ·
              refine ⟨2054644787319993612649739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369763191546662408433159 2054644787319993612649739)
              ·
                refine ⟨3081967180979990418974609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054644787319993612649739 3081967180979990418974609)
                ·
                  refine ⟨2311475385734992814230957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081967180979990418974609 2311475385734992814230957)
                  ·
                    refine ⟨866803269650622305336609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311475385734992814230957 866803269650622305336609)
                    ·
                      refine ⟨650102452237966729002457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 866803269650622305336609 650102452237966729002457)
                      ·
                        rfl

theorem cell23_1266070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1266070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266070 prefixEnd_1266070 := by exact prefixLift 1266070
  have htrace : WordTrace (prefixWord ++ tailWord_1266070) baseStart_1266070 baseEnd_1266070 := by
    simpa [prefixWord, tailWord_1266070, baseEnd_1266070] using wordTrace_append hprefix tailTrace_1266070
  have hstable : (prefixWord ++ tailWord_1266070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266070).length < 2 ^ (prefixWord ++ tailWord_1266070).sum := by decide
  have hdescent : baseEnd_1266070 < baseStart_1266070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266082 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1266082 : Nat := 118140960795 + 1266082 * 2 ^ 59
def prefixEnd_1266082 : Nat := 4983230072969 + 3 ^ 40 * 1266082 * 2
def baseEnd_1266082 : Nat := 650108614005820682052401

theorem tailTrace_1266082 : CollatzResearch.WordTrace tailWord_1266082 prefixEnd_1266082 650108614005820682052401 := by
  unfold tailWord_1266082
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544451049802154608948125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30785202799472412290528333 11544451049802154608948125)
  ·
    refine ⟨4329169143675807978355547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11544451049802154608948125 4329169143675807978355547)
    ·
      refine ⟨6493753715513711967533321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4329169143675807978355547 6493753715513711967533321)
      ·
        refine ⟨4870315286635283975649991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6493753715513711967533321 4870315286635283975649991)
        ·
          refine ⟨7305472929952925963474987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870315286635283975649991 7305472929952925963474987)
          ·
            refine ⟨10958209394929388945212481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305472929952925963474987 10958209394929388945212481)
            ·
              refine ⟨8218657046197041708909361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958209394929388945212481 8218657046197041708909361)
              ·
                refine ⟨6163992784647781281682021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8218657046197041708909361 6163992784647781281682021)
                ·
                  refine ⟨1155748647121458990315379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6163992784647781281682021 1155748647121458990315379)
                  ·
                    refine ⟨1733622970682188485473069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155748647121458990315379 1733622970682188485473069)
                    ·
                      refine ⟨650108614005820682052401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733622970682188485473069 650108614005820682052401)
                      ·
                        rfl

theorem cell23_1266082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1266082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266082 prefixEnd_1266082 := by exact prefixLift 1266082
  have htrace : WordTrace (prefixWord ++ tailWord_1266082) baseStart_1266082 baseEnd_1266082 := by
    simpa [prefixWord, tailWord_1266082, baseEnd_1266082] using wordTrace_append hprefix tailTrace_1266082
  have hstable : (prefixWord ++ tailWord_1266082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266082).length < 2 ^ (prefixWord ++ tailWord_1266082).sum := by decide
  have hdescent : baseEnd_1266082 < baseStart_1266082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266098 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1266098 : Nat := 118140960795 + 1266098 * 2 ^ 59
def prefixEnd_1266098 : Nat := 4983230072969 + 3 ^ 40 * 1266098 * 2
def baseEnd_1266098 : Nat := 216705609898764206484109

theorem tailTrace_1266098 : CollatzResearch.WordTrace tailWord_1266098 prefixEnd_1266098 216705609898764206484109 := by
  unfold tailWord_1266098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544596941787663292093737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30785591844767102112249965 11544596941787663292093737)
  ·
    refine ⟨8658447706340747469070303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11544596941787663292093737 8658447706340747469070303)
    ·
      refine ⟨12987671559511121203605455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658447706340747469070303 12987671559511121203605455)
      ·
        refine ⟨19481507339266681805408183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987671559511121203605455 19481507339266681805408183)
        ·
          refine ⟨29222261008900022708112275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19481507339266681805408183 29222261008900022708112275)
          ·
            refine ⟨43833391513350034062168413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29222261008900022708112275 43833391513350034062168413)
            ·
              refine ⟨16437521817506262773313155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43833391513350034062168413 16437521817506262773313155)
              ·
                refine ⟨24656282726259394159969733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16437521817506262773313155 24656282726259394159969733)
                ·
                  refine ⟨4623053011173636404994325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24656282726259394159969733 4623053011173636404994325)
                  ·
                    refine ⟨216705609898764206484109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4623053011173636404994325 216705609898764206484109)
                    ·
                      rfl

theorem cell23_1266098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1266098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266098 prefixEnd_1266098 := by exact prefixLift 1266098
  have htrace : WordTrace (prefixWord ++ tailWord_1266098) baseStart_1266098 baseEnd_1266098 := by
    simpa [prefixWord, tailWord_1266098, baseEnd_1266098] using wordTrace_append hprefix tailTrace_1266098
  have hstable : (prefixWord ++ tailWord_1266098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266098).length < 2 ^ (prefixWord ++ tailWord_1266098).sum := by decide
  have hdescent : baseEnd_1266098 < baseStart_1266098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266113 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1266113 : Nat := 118140960795 + 1266113 * 2 ^ 59
def prefixEnd_1266113 : Nat := 4983230072969 + 3 ^ 40 * 1266113 * 2
def baseEnd_1266113 : Nat := 650124531906110060764759

theorem tailTrace_1266113 : CollatzResearch.WordTrace tailWord_1266113 prefixEnd_1266113 650124531906110060764759 := by
  unfold tailWord_1266113
  simp only [CollatzResearch.WordTrace]
  refine ⟨46178934862096310730170993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30785956574730873820113995 46178934862096310730170993)
  ·
    refine ⟨34634201146572233047628245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46178934862096310730170993 34634201146572233047628245)
    ·
      refine ⟨811739089372786712053787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34634201146572233047628245 811739089372786712053787)
      ·
        refine ⟨1217608634059180068080681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811739089372786712053787 1217608634059180068080681)
        ·
          refine ⟨913206475544385051060511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217608634059180068080681 913206475544385051060511)
          ·
            refine ⟨1369809713316577576590767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913206475544385051060511 1369809713316577576590767)
            ·
              refine ⟨2054714569974866364886151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369809713316577576590767 2054714569974866364886151)
              ·
                refine ⟨3082071854962299547329227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054714569974866364886151 3082071854962299547329227)
                ·
                  refine ⟨4623107782443449320993841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082071854962299547329227 4623107782443449320993841)
                  ·
                    refine ⟨3467330836832586990745381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4623107782443449320993841 3467330836832586990745381)
                    ·
                      refine ⟨650124531906110060764759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467330836832586990745381 650124531906110060764759)
                      ·
                        rfl

theorem cell23_1266113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1266113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266113 prefixEnd_1266113 := by exact prefixLift 1266113
  have htrace : WordTrace (prefixWord ++ tailWord_1266113) baseStart_1266113 baseEnd_1266113 := by
    simpa [prefixWord, tailWord_1266113, baseEnd_1266113] using wordTrace_append hprefix tailTrace_1266113
  have hstable : (prefixWord ++ tailWord_1266113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266113).length < 2 ^ (prefixWord ++ tailWord_1266113).sum := by decide
  have hdescent : baseEnd_1266113 < baseStart_1266113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266116 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1266116 : Nat := 118140960795 + 1266116 * 2 ^ 59
def prefixEnd_1266116 : Nat := 4983230072969 + 3 ^ 40 * 1266116 * 2
def baseEnd_1266116 : Nat := 650126072348073549027245

theorem tailTrace_1266116 : CollatzResearch.WordTrace tailWord_1266116 prefixEnd_1266116 650126072348073549027245 := by
  unfold tailWord_1266116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089522140542721121265101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30786029520723628161686801 23089522140542721121265101)
  ·
    refine ⟨8658570802703520420474413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23089522140542721121265101 8658570802703520420474413)
    ·
      refine ⟨3246964051013820157677905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8658570802703520420474413 3246964051013820157677905)
      ·
        refine ⟨2435223038260365118258429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246964051013820157677905 2435223038260365118258429)
        ·
          refine ⟨913208639347636919346911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2435223038260365118258429 913208639347636919346911)
          ·
            refine ⟨1369812959021455379020367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913208639347636919346911 1369812959021455379020367)
            ·
              refine ⟨2054719438532183068530551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369812959021455379020367 2054719438532183068530551)
              ·
                refine ⟨3082079157798274602795827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054719438532183068530551 3082079157798274602795827)
                ·
                  refine ⟨4623118736697411904193741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082079157798274602795827 4623118736697411904193741)
                  ·
                    refine ⟨1733669526261529464072653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4623118736697411904193741 1733669526261529464072653)
                    ·
                      refine ⟨650126072348073549027245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733669526261529464072653 650126072348073549027245)
                      ·
                        rfl

theorem cell23_1266116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1266116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266116 prefixEnd_1266116 := by exact prefixLift 1266116
  have htrace : WordTrace (prefixWord ++ tailWord_1266116) baseStart_1266116 baseEnd_1266116 := by
    simpa [prefixWord, tailWord_1266116, baseEnd_1266116] using wordTrace_append hprefix tailTrace_1266116
  have hstable : (prefixWord ++ tailWord_1266116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266116).length < 2 ^ (prefixWord ++ tailWord_1266116).sum := by decide
  have hdescent : baseEnd_1266116 < baseStart_1266116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266148 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1266148 : Nat := 118140960795 + 1266148 * 2 ^ 59
def prefixEnd_1266148 : Nat := 4983230072969 + 3 ^ 40 * 1266148 * 2
def baseEnd_1266148 : Nat := 650142503729017423827097

theorem tailTrace_1266148 : CollatzResearch.WordTrace tailWord_1266148 prefixEnd_1266148 650142503729017423827097 := by
  unfold tailWord_1266148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23090105708484755853847549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30786807611313007805130065 23090105708484755853847549)
  ·
    refine ⟨8658789640681783445192831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23090105708484755853847549 8658789640681783445192831)
    ·
      refine ⟨12988184461022675167789247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658789640681783445192831 12988184461022675167789247)
      ·
        refine ⟨19482276691534012751683871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12988184461022675167789247 19482276691534012751683871)
        ·
          refine ⟨29223415037301019127525807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19482276691534012751683871 29223415037301019127525807)
          ·
            refine ⟨43835122555951528691288711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29223415037301019127525807 43835122555951528691288711)
            ·
              refine ⟨65752683833927293036933067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43835122555951528691288711 65752683833927293036933067)
              ·
                refine ⟨98629025750890939555399601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65752683833927293036933067 98629025750890939555399601)
                ·
                  refine ⟨73971769313168204666549701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98629025750890939555399601 73971769313168204666549701)
                  ·
                    refine ⟨13869706746219038374978069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73971769313168204666549701 13869706746219038374978069)
                    ·
                      refine ⟨650142503729017423827097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13869706746219038374978069 650142503729017423827097)
                      ·
                        rfl

theorem cell23_1266148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1266148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266148 prefixEnd_1266148 := by exact prefixLift 1266148
  have htrace : WordTrace (prefixWord ++ tailWord_1266148) baseStart_1266148 baseEnd_1266148 := by
    simpa [prefixWord, tailWord_1266148, baseEnd_1266148] using wordTrace_append hprefix tailTrace_1266148
  have hstable : (prefixWord ++ tailWord_1266148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266148).length < 2 ^ (prefixWord ++ tailWord_1266148).sum := by decide
  have hdescent : baseEnd_1266148 < baseStart_1266148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266246 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1266246 : Nat := 118140960795 + 1266246 * 2 ^ 59
def prefixEnd_1266246 : Nat := 4983230072969 + 3 ^ 40 * 1266246 * 2
def baseEnd_1266246 : Nat := 650192824833158040401647

theorem tailTrace_1266246 : CollatzResearch.WordTrace tailWord_1266246 prefixEnd_1266246 650192824833158040401647 := by
  unfold tailWord_1266246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443243305331702326398831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30789190513742982963175061 1443243305331702326398831)
  ·
    refine ⟨2164864957997553489598247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443243305331702326398831 2164864957997553489598247)
    ·
      refine ⟨3247297436996330234397371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164864957997553489598247 3247297436996330234397371)
      ·
        refine ⟨4870946155494495351596057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247297436996330234397371 4870946155494495351596057)
        ·
          refine ⟨3653209616620871513697043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870946155494495351596057 3653209616620871513697043)
          ·
            refine ⟨5479814424931307270545565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653209616620871513697043 5479814424931307270545565)
            ·
              refine ⟨2054930409349240226454587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5479814424931307270545565 2054930409349240226454587)
              ·
                refine ⟨3082395614023860339681881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054930409349240226454587 3082395614023860339681881)
                ·
                  refine ⟨2311796710517895254761411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3082395614023860339681881 2311796710517895254761411)
                  ·
                    refine ⟨3467695065776842882142117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311796710517895254761411 3467695065776842882142117)
                    ·
                      refine ⟨650192824833158040401647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467695065776842882142117 650192824833158040401647)
                      ·
                        rfl

theorem cell23_1266246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1266246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266246 prefixEnd_1266246 := by exact prefixLift 1266246
  have htrace : WordTrace (prefixWord ++ tailWord_1266246) baseStart_1266246 baseEnd_1266246 := by
    simpa [prefixWord, tailWord_1266246, baseEnd_1266246] using wordTrace_append hprefix tailTrace_1266246
  have hstable : (prefixWord ++ tailWord_1266246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266246).length < 2 ^ (prefixWord ++ tailWord_1266246).sum := by decide
  have hdescent : baseEnd_1266246 < baseStart_1266246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266330 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1266330 : Nat := 118140960795 + 1266330 * 2 ^ 59
def prefixEnd_1266330 : Nat := 4983230072969 + 3 ^ 40 * 1266330 * 2
def baseEnd_1266330 : Nat := 650235957208135711751261

theorem tailTrace_1266330 : CollatzResearch.WordTrace tailWord_1266330 prefixEnd_1266330 650235957208135711751261 := by
  unfold tailWord_1266330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546712375577539197705111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30791233001540104527213629 11546712375577539197705111)
  ·
    refine ⟨17320068563366308796557667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11546712375577539197705111 17320068563366308796557667)
    ·
      refine ⟨25980102845049463194836501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17320068563366308796557667 25980102845049463194836501)
      ·
        refine ⟨1217817320861693587257961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25980102845049463194836501 1217817320861693587257961)
        ·
          refine ⟨913362990646270190443471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217817320861693587257961 913362990646270190443471)
          ·
            refine ⟨1370044485969405285665207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913362990646270190443471 1370044485969405285665207)
            ·
              refine ⟨2055066728954107928497811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370044485969405285665207 2055066728954107928497811)
              ·
                refine ⟨3082600093431161892746717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055066728954107928497811 3082600093431161892746717)
                ·
                  refine ⟨1155975035036685709780019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3082600093431161892746717 1155975035036685709780019)
                  ·
                    refine ⟨1733962552555028564670029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155975035036685709780019 1733962552555028564670029)
                    ·
                      refine ⟨650235957208135711751261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733962552555028564670029 650235957208135711751261)
                      ·
                        rfl

theorem cell23_1266330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1266330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266330 prefixEnd_1266330 := by exact prefixLift 1266330
  have htrace : WordTrace (prefixWord ++ tailWord_1266330) baseStart_1266330 baseEnd_1266330 := by
    simpa [prefixWord, tailWord_1266330, baseEnd_1266330] using wordTrace_append hprefix tailTrace_1266330
  have hstable : (prefixWord ++ tailWord_1266330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266330).length < 2 ^ (prefixWord ++ tailWord_1266330).sum := by decide
  have hdescent : baseEnd_1266330 < baseStart_1266330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266332 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1266332 : Nat := 118140960795 + 1266332 * 2 ^ 59
def prefixEnd_1266332 : Nat := 4983230072969 + 3 ^ 40 * 1266332 * 2
def baseEnd_1266332 : Nat := 650236984169444703926251

theorem tailTrace_1266332 : CollatzResearch.WordTrace tailWord_1266332 prefixEnd_1266332 650236984169444703926251 := by
  unfold tailWord_1266332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093461224151455566196625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30791281632201940754928833 23093461224151455566196625)
  ·
    refine ⟨17320095918113591674647469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23093461224151455566196625 17320095918113591674647469)
    ·
      refine ⟨6495035969292596877992801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17320095918113591674647469 6495035969292596877992801)
      ·
        refine ⟨4871276976969447658494601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495035969292596877992801 4871276976969447658494601)
        ·
          refine ⟨3653457732727085743870951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871276976969447658494601 3653457732727085743870951)
          ·
            refine ⟨5480186599090628615806427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653457732727085743870951 5480186599090628615806427)
            ·
              refine ⟨8220279898635942923709641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480186599090628615806427 8220279898635942923709641)
              ·
                refine ⟨6165209923976957192782231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220279898635942923709641 6165209923976957192782231)
                ·
                  refine ⟨9247814885965435789173347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165209923976957192782231 9247814885965435789173347)
                  ·
                    refine ⟨13871722328948153683760021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247814885965435789173347 13871722328948153683760021)
                    ·
                      refine ⟨650236984169444703926251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13871722328948153683760021 650236984169444703926251)
                      ·
                        rfl

theorem cell23_1266332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1266332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266332 prefixEnd_1266332 := by exact prefixLift 1266332
  have htrace : WordTrace (prefixWord ++ tailWord_1266332) baseStart_1266332 baseEnd_1266332 := by
    simpa [prefixWord, tailWord_1266332, baseEnd_1266332] using wordTrace_append hprefix tailTrace_1266332
  have hstable : (prefixWord ++ tailWord_1266332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266332).length < 2 ^ (prefixWord ++ tailWord_1266332).sum := by decide
  have hdescent : baseEnd_1266332 < baseStart_1266332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
