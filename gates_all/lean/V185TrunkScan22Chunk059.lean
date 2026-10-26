import V185TrunkScan22Chunk058

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_529329 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_529329 : Nat := 118140960795 + 529329 * 2 ^ 59
def prefixEnd_529329 : Nat := 4983230072969 + 3 ^ 40 * 529329 * 2
def baseEnd_529329 : Nat := 181200134242576487702111

theorem tailTrace_529329 : CollatzResearch.WordTrace tailWord_529329 prefixEnd_529329 181200134242576487702111 := by
  unfold tailWord_529329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306214699338910041023041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12870809799559273360682027 19306214699338910041023041)
  ·
    refine ⟨14479661024504182530767281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19306214699338910041023041 14479661024504182530767281)
    ·
      refine ⟨10859745768378136898075461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14479661024504182530767281 10859745768378136898075461)
      ·
        refine ⟨2036202331570900668389149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10859745768378136898075461 2036202331570900668389149)
        ·
          refine ⟨763575874339087750645931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2036202331570900668389149 763575874339087750645931)
          ·
            refine ⟨1145363811508631625968897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763575874339087750645931 1145363811508631625968897)
            ·
              refine ⟨859022858631473719476673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145363811508631625968897 859022858631473719476673)
              ·
                refine ⟨644267143973605289607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859022858631473719476673 644267143973605289607505)
                ·
                  refine ⟨483200357980203967205629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644267143973605289607505 483200357980203967205629)
                  ·
                    refine ⟨181200134242576487702111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483200357980203967205629 181200134242576487702111)
                    ·
                      rfl

theorem cell22_529329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_529329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529329 prefixEnd_529329 := by exact prefixLift 529329
  have htrace : WordTrace (prefixWord ++ tailWord_529329) baseStart_529329 baseEnd_529329 := by
    simpa [prefixWord, tailWord_529329, baseEnd_529329] using wordTrace_append hprefix tailTrace_529329
  have hstable : (prefixWord ++ tailWord_529329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529329).length < 2 ^ (prefixWord ++ tailWord_529329).sum := by decide
  have hdescent : baseEnd_529329 < baseStart_529329 := by decide
  rcases family_descends (prefixWord ++ tailWord_529329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529338 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_529338 : Nat := 118140960795 + 529338 * 2 ^ 59
def prefixEnd_529338 : Nat := 4983230072969 + 3 ^ 40 * 529338 * 2
def baseEnd_529338 : Nat := 181203215126503464227083

theorem tailTrace_529338 : CollatzResearch.WordTrace tailWord_529338 prefixEnd_529338 181203215126503464227083 := by
  unfold tailWord_529338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826635739076576144525167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12871028637537536385400445 4826635739076576144525167)
  ·
    refine ⟨7239953608614864216787751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826635739076576144525167 7239953608614864216787751)
    ·
      refine ⟨10859930412922296325181627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7239953608614864216787751 10859930412922296325181627)
      ·
        refine ⟨16289895619383444487772441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10859930412922296325181627 16289895619383444487772441)
        ·
          refine ⟨12217421714537583365829331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16289895619383444487772441 12217421714537583365829331)
          ·
            refine ⟨18326132571806375048743997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217421714537583365829331 18326132571806375048743997)
            ·
              refine ⟨6872299714427390643278999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18326132571806375048743997 6872299714427390643278999)
              ·
                refine ⟨10308449571641085964918499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872299714427390643278999 10308449571641085964918499)
                ·
                  refine ⟨15462674357461628947377749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10308449571641085964918499 15462674357461628947377749)
                  ·
                    refine ⟨181203215126503464227083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15462674357461628947377749 181203215126503464227083)
                    ·
                      rfl

theorem cell22_529338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_529338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529338 prefixEnd_529338 := by exact prefixLift 529338
  have htrace : WordTrace (prefixWord ++ tailWord_529338) baseStart_529338 baseEnd_529338 := by
    simpa [prefixWord, tailWord_529338, baseEnd_529338] using wordTrace_append hprefix tailTrace_529338
  have hstable : (prefixWord ++ tailWord_529338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529338).length < 2 ^ (prefixWord ++ tailWord_529338).sum := by decide
  have hdescent : baseEnd_529338 < baseStart_529338 := by decide
  rcases family_descends (prefixWord ++ tailWord_529338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529415 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 6]
def baseStart_529415 : Nat := 118140960795 + 529415 * 2 ^ 59
def prefixEnd_529415 : Nat := 4983230072969 + 3 ^ 40 * 529415 * 2
def baseEnd_529415 : Nat := 60409857933366976683949

theorem tailTrace_529415 : CollatzResearch.WordTrace tailWord_529415 prefixEnd_529415 60409857933366976683949 := by
  unfold tailWord_529415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309351377027346728653699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12872900918018231152435799 19309351377027346728653699)
  ·
    refine ⟨28964027065541020092980549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19309351377027346728653699 28964027065541020092980549)
    ·
      refine ⟨5430755074788941267433853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28964027065541020092980549 5430755074788941267433853)
      ·
        refine ⟨2036533153045852975287695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5430755074788941267433853 2036533153045852975287695)
        ·
          refine ⟨3054799729568779462931543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036533153045852975287695 3054799729568779462931543)
          ·
            refine ⟨4582199594353169194397315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054799729568779462931543 4582199594353169194397315)
            ·
              refine ⟨6873299391529753791595973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582199594353169194397315 6873299391529753791595973)
              ·
                refine ⟨1288743635911828835924245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6873299391529753791595973 1288743635911828835924245)
                ·
                  refine ⟨60409857933366976683949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1288743635911828835924245 60409857933366976683949)
                  ·
                    rfl

theorem cell22_529415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_529415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529415 prefixEnd_529415 := by exact prefixLift 529415
  have htrace : WordTrace (prefixWord ++ tailWord_529415) baseStart_529415 baseEnd_529415 := by
    simpa [prefixWord, tailWord_529415, baseEnd_529415] using wordTrace_append hprefix tailTrace_529415
  have hstable : (prefixWord ++ tailWord_529415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529415).length < 2 ^ (prefixWord ++ tailWord_529415).sum := by decide
  have hdescent : baseEnd_529415 < baseStart_529415 := by decide
  rcases family_descends (prefixWord ++ tailWord_529415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529464 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_529464 : Nat := 118140960795 + 529464 * 2 ^ 59
def prefixEnd_529464 : Nat := 4983230072969 + 3 ^ 40 * 529464 * 2
def baseEnd_529464 : Nat := 181246347501481135576697

theorem tailTrace_529464 : CollatzResearch.WordTrace tailWord_529464 prefixEnd_529464 181246347501481135576697 := by
  unfold tailWord_529464
  simp only [CollatzResearch.WordTrace]
  refine ⟨9655569276924914048593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12874092369233218731458297 9655569276924914048593723)
  ·
    refine ⟨14483353915387371072890585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9655569276924914048593723 14483353915387371072890585)
    ·
      refine ⟨10862515436540528304667939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14483353915387371072890585 10862515436540528304667939)
      ·
        refine ⟨16293773154810792457001909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10862515436540528304667939 16293773154810792457001909)
        ·
          refine ⟨1527541233263511792843929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16293773154810792457001909 1527541233263511792843929)
          ·
            refine ⟨1145655924947633844632947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527541233263511792843929 1145655924947633844632947)
            ·
              refine ⟨1718483887421450766949421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145655924947633844632947 1718483887421450766949421)
              ·
                refine ⟨644431457783044037606033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718483887421450766949421 644431457783044037606033)
                ·
                  refine ⟨483323593337283028204525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644431457783044037606033 483323593337283028204525)
                  ·
                    refine ⟨181246347501481135576697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483323593337283028204525 181246347501481135576697)
                    ·
                      rfl

theorem cell22_529464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_529464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529464 prefixEnd_529464 := by exact prefixLift 529464
  have htrace : WordTrace (prefixWord ++ tailWord_529464) baseStart_529464 baseEnd_529464 := by
    simpa [prefixWord, tailWord_529464, baseEnd_529464] using wordTrace_append hprefix tailTrace_529464
  have hstable : (prefixWord ++ tailWord_529464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529464).length < 2 ^ (prefixWord ++ tailWord_529464).sum := by decide
  have hdescent : baseEnd_529464 < baseStart_529464 := by decide
  rcases family_descends (prefixWord ++ tailWord_529464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529494 : List Nat := [5, 2, 2, 1, 2, 10]
def baseStart_529494 : Nat := 118140960795 + 529494 * 2 ^ 59
def prefixEnd_529494 : Nat := 4983230072969 + 3 ^ 40 * 529494 * 2
def baseEnd_529494 : Nat := 2237736013760136510205

theorem tailTrace_529494 : CollatzResearch.WordTrace tailWord_529494 prefixEnd_529494 2237736013760136510205 := by
  unfold tailWord_529494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207014546483821451298721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12874821829160762147186357 1207014546483821451298721)
  ·
    refine ⟨905260909862866088474041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1207014546483821451298721 905260909862866088474041)
    ·
      refine ⟨678945682397149566355531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905260909862866088474041 678945682397149566355531)
      ·
        refine ⟨1018418523595724349533297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678945682397149566355531 1018418523595724349533297)
        ·
          refine ⟨763813892696793262149973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018418523595724349533297 763813892696793262149973)
          ·
            refine ⟨2237736013760136510205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 763813892696793262149973 2237736013760136510205)
            ·
              rfl

theorem cell22_529494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 10].length) (baseStart_529494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529494 prefixEnd_529494 := by exact prefixLift 529494
  have htrace : WordTrace (prefixWord ++ tailWord_529494) baseStart_529494 baseEnd_529494 := by
    simpa [prefixWord, tailWord_529494, baseEnd_529494] using wordTrace_append hprefix tailTrace_529494
  have hstable : (prefixWord ++ tailWord_529494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529494).length < 2 ^ (prefixWord ++ tailWord_529494).sum := by decide
  have hdescent : baseEnd_529494 < baseStart_529494 := by decide
  rcases family_descends (prefixWord ++ tailWord_529494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529505 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 7]
def baseStart_529505 : Nat := 118140960795 + 529505 * 2 ^ 59
def prefixEnd_529505 : Nat := 4983230072969 + 3 ^ 40 * 529505 * 2
def baseEnd_529505 : Nat := 60420127546456898433857

theorem tailTrace_529505 : CollatzResearch.WordTrace tailWord_529505 prefixEnd_529505 60420127546456898433857 := by
  unfold tailWord_529505
  simp only [CollatzResearch.WordTrace]
  refine ⟨19312633946701292099429969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12875089297800861399619979 19312633946701292099429969)
  ·
    refine ⟨14484475460025969074572477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19312633946701292099429969 14484475460025969074572477)
    ·
      refine ⟨5431678297509738402964679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14484475460025969074572477 5431678297509738402964679)
      ·
        refine ⟨8147517446264607604447019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431678297509738402964679 8147517446264607604447019)
        ·
          refine ⟨12221276169396911406670529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8147517446264607604447019 12221276169396911406670529)
          ·
            refine ⟨9165957127047683555002897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12221276169396911406670529 9165957127047683555002897)
            ·
              refine ⟨6874467845285762666252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9165957127047683555002897 6874467845285762666252173)
              ·
                refine ⟨2577925441982160999844565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6874467845285762666252173 2577925441982160999844565)
                ·
                  refine ⟨60420127546456898433857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2577925441982160999844565 60420127546456898433857)
                  ·
                    rfl

theorem cell22_529505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_529505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529505 prefixEnd_529505 := by exact prefixLift 529505
  have htrace : WordTrace (prefixWord ++ tailWord_529505) baseStart_529505 baseEnd_529505 := by
    simpa [prefixWord, tailWord_529505, baseEnd_529505] using wordTrace_append hprefix tailTrace_529505
  have hstable : (prefixWord ++ tailWord_529505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529505).length < 2 ^ (prefixWord ++ tailWord_529505).sum := by decide
  have hdescent : baseEnd_529505 < baseStart_529505 := by decide
  rcases family_descends (prefixWord ++ tailWord_529505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529522 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_529522 : Nat := 118140960795 + 529522 * 2 ^ 59
def prefixEnd_529522 : Nat := 4983230072969 + 3 ^ 40 * 529522 * 2
def baseEnd_529522 : Nat := 60422067362262772542173

theorem tailTrace_529522 : CollatzResearch.WordTrace tailWord_529522 prefixEnd_529522 60422067362262772542173 := by
  unfold tailWord_529522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828313496909926000699705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12875502658426469335199213 4828313496909926000699705)
  ·
    refine ⟨3621235122682444500524779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4828313496909926000699705 3621235122682444500524779)
    ·
      refine ⟨5431852684023666750787169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621235122682444500524779 5431852684023666750787169)
      ·
        refine ⟨4073889513017750063090377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5431852684023666750787169 4073889513017750063090377)
        ·
          refine ⟨3055417134763312547317783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073889513017750063090377 3055417134763312547317783)
          ·
            refine ⟨4583125702144968820976675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055417134763312547317783 4583125702144968820976675)
            ·
              refine ⟨6874688553217453231465013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583125702144968820976675 6874688553217453231465013)
              ·
                refine ⟨644502051864136240449845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6874688553217453231465013 644502051864136240449845)
                ·
                  refine ⟨60422067362262772542173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644502051864136240449845 60422067362262772542173)
                  ·
                    rfl

theorem cell22_529522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_529522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529522 prefixEnd_529522 := by exact prefixLift 529522
  have htrace : WordTrace (prefixWord ++ tailWord_529522) baseStart_529522 baseEnd_529522 := by
    simpa [prefixWord, tailWord_529522, baseEnd_529522] using wordTrace_append hprefix tailTrace_529522
  have hstable : (prefixWord ++ tailWord_529522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529522).length < 2 ^ (prefixWord ++ tailWord_529522).sum := by decide
  have hdescent : baseEnd_529522 < baseStart_529522 := by decide
  rcases family_descends (prefixWord ++ tailWord_529522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529597 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_529597 : Nat := 118140960795 + 529597 * 2 ^ 59
def prefixEnd_529597 : Nat := 4983230072969 + 3 ^ 40 * 529597 * 2
def baseEnd_529597 : Nat := 181291876119513122001289

theorem tailTrace_529597 : CollatzResearch.WordTrace tailWord_529597 prefixEnd_529597 181291876119513122001289 := by
  unfold tailWord_529597
  simp only [CollatzResearch.WordTrace]
  refine ⟨19315989462367991811779045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12877326308245327874519363 19315989462367991811779045)
  ·
    refine ⟨3621748024193998464708571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19315989462367991811779045 3621748024193998464708571)
    ·
      refine ⟨5432622036290997697062857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621748024193998464708571 5432622036290997697062857)
      ·
        refine ⟨4074466527218248272797143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5432622036290997697062857 4074466527218248272797143)
        ·
          refine ⟨6111699790827372409195715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074466527218248272797143 6111699790827372409195715)
          ·
            refine ⟨9167549686241058613793573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111699790827372409195715 9167549686241058613793573)
            ·
              refine ⟨1718915566170198490086295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9167549686241058613793573 1718915566170198490086295)
              ·
                refine ⟨2578373349255297735129443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1718915566170198490086295 2578373349255297735129443)
                ·
                  refine ⟨3867560023882946602694165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578373349255297735129443 3867560023882946602694165)
                  ·
                    refine ⟨181291876119513122001289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3867560023882946602694165 181291876119513122001289)
                    ·
                      rfl

theorem cell22_529597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_529597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529597 prefixEnd_529597 := by exact prefixLift 529597
  have htrace : WordTrace (prefixWord ++ tailWord_529597) baseStart_529597 baseEnd_529597 := by
    simpa [prefixWord, tailWord_529597, baseEnd_529597] using wordTrace_append hprefix tailTrace_529597
  have hstable : (prefixWord ++ tailWord_529597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529597).length < 2 ^ (prefixWord ++ tailWord_529597).sum := by decide
  have hdescent : baseEnd_529597 < baseStart_529597 := by decide
  rcases family_descends (prefixWord ++ tailWord_529597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529633 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_529633 : Nat := 118140960795 + 529633 * 2 ^ 59
def prefixEnd_529633 : Nat := 4983230072969 + 3 ^ 40 * 529633 * 2
def baseEnd_529633 : Nat := 181304199655221028101179

theorem tailTrace_529633 : CollatzResearch.WordTrace tailWord_529633 prefixEnd_529633 181304199655221028101179 := by
  unfold tailWord_529633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19317302490237569960089553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12878201660158379973393035 19317302490237569960089553)
  ·
    refine ⟨14487976867678177470067165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19317302490237569960089553 14487976867678177470067165)
    ·
      refine ⟨5432991325379316551275187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14487976867678177470067165 5432991325379316551275187)
      ·
        refine ⟨8149486988068974826912781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432991325379316551275187 8149486988068974826912781)
        ·
          refine ⟨3056057620525865560092293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8149486988068974826912781 3056057620525865560092293)
          ·
            refine ⟨573010803848599792517305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3056057620525865560092293 573010803848599792517305)
            ·
              refine ⟨429758102886449844387979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573010803848599792517305 429758102886449844387979)
              ·
                refine ⟨644637154329674766581969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429758102886449844387979 644637154329674766581969)
                ·
                  refine ⟨483477865747256074936477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644637154329674766581969 483477865747256074936477)
                  ·
                    refine ⟨181304199655221028101179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483477865747256074936477 181304199655221028101179)
                    ·
                      rfl

theorem cell22_529633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_529633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529633 prefixEnd_529633 := by exact prefixLift 529633
  have htrace : WordTrace (prefixWord ++ tailWord_529633) baseStart_529633 baseEnd_529633 := by
    simpa [prefixWord, tailWord_529633, baseEnd_529633] using wordTrace_append hprefix tailTrace_529633
  have hstable : (prefixWord ++ tailWord_529633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529633).length < 2 ^ (prefixWord ++ tailWord_529633).sum := by decide
  have hdescent : baseEnd_529633 < baseStart_529633 := by decide
  rcases family_descends (prefixWord ++ tailWord_529633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529678 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_529678 : Nat := 118140960795 + 529678 * 2 ^ 59
def prefixEnd_529678 : Nat := 4983230072969 + 3 ^ 40 * 529678 * 2
def baseEnd_529678 : Nat := 181319604074855910726041

theorem tailTrace_529678 : CollatzResearch.WordTrace tailWord_529678 prefixEnd_529678 181319604074855910726041 := by
  unfold tailWord_529678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414867971884317830684711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12879295850049695096985125 2414867971884317830684711)
  ·
    refine ⟨3622301957826476746027067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2414867971884317830684711 3622301957826476746027067)
    ·
      refine ⟨5433452936739715119040601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622301957826476746027067 5433452936739715119040601)
      ·
        refine ⟨4075089702554786339280451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5433452936739715119040601 4075089702554786339280451)
        ·
          refine ⟨6112634553832179508920677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075089702554786339280451 6112634553832179508920677)
          ·
            refine ⟨1146118978843533657922627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6112634553832179508920677 1146118978843533657922627)
            ·
              refine ⟨1719178468265300486883941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146118978843533657922627 1719178468265300486883941)
              ·
                refine ⟨322345962799743841290739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1719178468265300486883941 322345962799743841290739)
                ·
                  refine ⟨483518944199615761936109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322345962799743841290739 483518944199615761936109)
                  ·
                    refine ⟨181319604074855910726041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483518944199615761936109 181319604074855910726041)
                    ·
                      rfl

theorem cell22_529678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_529678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529678 prefixEnd_529678 := by exact prefixLift 529678
  have htrace : WordTrace (prefixWord ++ tailWord_529678) baseStart_529678 baseEnd_529678 := by
    simpa [prefixWord, tailWord_529678, baseEnd_529678] using wordTrace_append hprefix tailTrace_529678
  have hstable : (prefixWord ++ tailWord_529678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529678).length < 2 ^ (prefixWord ++ tailWord_529678).sum := by decide
  have hdescent : baseEnd_529678 < baseStart_529678 := by decide
  rcases family_descends (prefixWord ++ tailWord_529678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529725 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 5]
def baseStart_529725 : Nat := 118140960795 + 529725 * 2 ^ 59
def prefixEnd_529725 : Nat := 4983230072969 + 3 ^ 40 * 529725 * 2
def baseEnd_529725 : Nat := 60445231045121151600299

theorem tailTrace_529725 : CollatzResearch.WordTrace tailWord_529725 prefixEnd_529725 60445231045121151600299 := by
  unfold tailWord_529725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320658005904269672438629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12880438670602846448292419 19320658005904269672438629)
  ·
    refine ⟨3622623376107050563582243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19320658005904269672438629 3622623376107050563582243)
    ·
      refine ⟨5433935064160575845373365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622623376107050563582243 5433935064160575845373365)
      ·
        refine ⟨509431412265053985503753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5433935064160575845373365 509431412265053985503753)
        ·
          refine ⟨382073559198790489127815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509431412265053985503753 382073559198790489127815)
          ·
            refine ⟨573110338798185733691723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382073559198790489127815 573110338798185733691723)
            ·
              refine ⟨859665508197278600537585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573110338798185733691723 859665508197278600537585)
              ·
                refine ⟨644749131147958950403189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859665508197278600537585 644749131147958950403189)
                ·
                  refine ⟨60445231045121151600299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644749131147958950403189 60445231045121151600299)
                  ·
                    rfl

theorem cell22_529725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_529725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529725 prefixEnd_529725 := by exact prefixLift 529725
  have htrace : WordTrace (prefixWord ++ tailWord_529725) baseStart_529725 baseEnd_529725 := by
    simpa [prefixWord, tailWord_529725, baseEnd_529725] using wordTrace_append hprefix tailTrace_529725
  have hstable : (prefixWord ++ tailWord_529725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529725).length < 2 ^ (prefixWord ++ tailWord_529725).sum := by decide
  have hdescent : baseEnd_529725 < baseStart_529725 := by decide
  rcases family_descends (prefixWord ++ tailWord_529725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529747 : List Nat := [1, 1, 1, 2, 1, 1, 6, 9]
def baseStart_529747 : Nat := 118140960795 + 529747 * 2 ^ 59
def prefixEnd_529747 : Nat := 4983230072969 + 3 ^ 40 * 529747 * 2
def baseEnd_529747 : Nat := 20149247131662525638981

theorem tailTrace_529747 : CollatzResearch.WordTrace tailWord_529747 prefixEnd_529747 20149247131662525638981 := by
  unfold tailWord_529747
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321460411824567429739495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12880973607883044953159663 19321460411824567429739495)
  ·
    refine ⟨28982190617736851144609243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19321460411824567429739495 28982190617736851144609243)
    ·
      refine ⟨43473285926605276716913865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28982190617736851144609243 43473285926605276716913865)
      ·
        refine ⟨32604964444953957537685399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43473285926605276716913865 32604964444953957537685399)
        ·
          refine ⟨48907446667430936306528099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32604964444953957537685399 48907446667430936306528099)
          ·
            refine ⟨73361170001146404459792149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48907446667430936306528099 73361170001146404459792149)
            ·
              refine ⟨3438804843803737709052757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73361170001146404459792149 3438804843803737709052757)
              ·
                refine ⟨20149247131662525638981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3438804843803737709052757 20149247131662525638981)
                ·
                  rfl

theorem cell22_529747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 9].length) (baseStart_529747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529747 prefixEnd_529747 := by exact prefixLift 529747
  have htrace : WordTrace (prefixWord ++ tailWord_529747) baseStart_529747 baseEnd_529747 := by
    simpa [prefixWord, tailWord_529747, baseEnd_529747] using wordTrace_append hprefix tailTrace_529747
  have hstable : (prefixWord ++ tailWord_529747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529747).length < 2 ^ (prefixWord ++ tailWord_529747).sum := by decide
  have hdescent : baseEnd_529747 < baseStart_529747 := by decide
  rcases family_descends (prefixWord ++ tailWord_529747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529749 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_529749 : Nat := 118140960795 + 529749 * 2 ^ 59
def prefixEnd_529749 : Nat := 4983230072969 + 3 ^ 40 * 529749 * 2
def baseEnd_529749 : Nat := 181343908825835392200823

theorem tailTrace_529749 : CollatzResearch.WordTrace tailWord_529749 prefixEnd_529749 181343908825835392200823 := by
  unfold tailWord_529749
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321533357817321771312301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12881022238544881180874867 19321533357817321771312301)
  ·
    refine ⟨7245575009181495664242113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19321533357817321771312301 7245575009181495664242113)
    ·
      refine ⟨5434181256886121748181585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7245575009181495664242113 5434181256886121748181585)
      ·
        refine ⟨4075635942664591311136189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5434181256886121748181585 4075635942664591311136189)
        ·
          refine ⟨1528363478499221741676071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4075635942664591311136189 1528363478499221741676071)
          ·
            refine ⟨2292545217748832612514107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528363478499221741676071 2292545217748832612514107)
            ·
              refine ⟨3438817826623248918771161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292545217748832612514107 3438817826623248918771161)
              ·
                refine ⟨2579113369967436689078371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3438817826623248918771161 2579113369967436689078371)
                ·
                  refine ⟨3868670054951155033617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579113369967436689078371 3868670054951155033617557)
                  ·
                    refine ⟨181343908825835392200823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3868670054951155033617557 181343908825835392200823)
                    ·
                      rfl

theorem cell22_529749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_529749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529749 prefixEnd_529749 := by exact prefixLift 529749
  have htrace : WordTrace (prefixWord ++ tailWord_529749) baseStart_529749 baseEnd_529749 := by
    simpa [prefixWord, tailWord_529749, baseEnd_529749] using wordTrace_append hprefix tailTrace_529749
  have hstable : (prefixWord ++ tailWord_529749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529749).length < 2 ^ (prefixWord ++ tailWord_529749).sum := by decide
  have hdescent : baseEnd_529749 < baseStart_529749 := by decide
  rcases family_descends (prefixWord ++ tailWord_529749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529751 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 5]
def baseStart_529751 : Nat := 118140960795 + 529751 * 2 ^ 59
def prefixEnd_529751 : Nat := 4983230072969 + 3 ^ 40 * 529751 * 2
def baseEnd_529751 : Nat := 181344593466708053650817

theorem tailTrace_529751 : CollatzResearch.WordTrace tailWord_529751 prefixEnd_529751 181344593466708053650817 := by
  unfold tailWord_529751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19321606303810076112885107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12881070869206717408590071 19321606303810076112885107)
  ·
    refine ⟨28982409455715114169327661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19321606303810076112885107 28982409455715114169327661)
    ·
      refine ⟨10868403545893167813497873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28982409455715114169327661 10868403545893167813497873)
      ·
        refine ⟨8151302659419875860123405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10868403545893167813497873 8151302659419875860123405)
        ·
          refine ⟨3056738497282453447546277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8151302659419875860123405 3056738497282453447546277)
          ·
            refine ⟨573138468240460021414927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3056738497282453447546277 573138468240460021414927)
            ·
              refine ⟨859707702360690032122391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573138468240460021414927 859707702360690032122391)
              ·
                refine ⟨1289561553541035048183587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859707702360690032122391 1289561553541035048183587)
                ·
                  refine ⟨1934342330311552572275381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289561553541035048183587 1934342330311552572275381)
                  ·
                    refine ⟨181344593466708053650817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1934342330311552572275381 181344593466708053650817)
                    ·
                      rfl

theorem cell22_529751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_529751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529751 prefixEnd_529751 := by exact prefixLift 529751
  have htrace : WordTrace (prefixWord ++ tailWord_529751) baseStart_529751 baseEnd_529751 := by
    simpa [prefixWord, tailWord_529751, baseEnd_529751] using wordTrace_append hprefix tailTrace_529751
  have hstable : (prefixWord ++ tailWord_529751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529751).length < 2 ^ (prefixWord ++ tailWord_529751).sum := by decide
  have hdescent : baseEnd_529751 < baseStart_529751 := by decide
  rcases family_descends (prefixWord ++ tailWord_529751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529764 : List Nat := [2, 3, 1, 1, 3, 3, 1, 8]
def baseStart_529764 : Nat := 118140960795 + 529764 * 2 ^ 59
def prefixEnd_529764 : Nat := 4983230072969 + 3 ^ 40 * 529764 * 2
def baseEnd_529764 : Nat := 20149893736931150341753

theorem tailTrace_529764 : CollatzResearch.WordTrace tailWord_529764 prefixEnd_529764 20149893736931150341753 := by
  unfold tailWord_529764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661040226381489666554173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12881386968508652888738897 9661040226381489666554173)
  ·
    refine ⟨3622890084893058624957815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9661040226381489666554173 3622890084893058624957815)
    ·
      refine ⟨5434335127339587937436723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622890084893058624957815 5434335127339587937436723)
      ·
        refine ⟨8151502691009381906155085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5434335127339587937436723 8151502691009381906155085)
        ·
          refine ⟨3056813509128518214808157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8151502691009381906155085 3056813509128518214808157)
          ·
            refine ⟨1146305065923194330553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3056813509128518214808157 1146305065923194330553059)
            ·
              refine ⟨1719457598884791495829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146305065923194330553059 1719457598884791495829589)
              ·
                refine ⟨20149893736931150341753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1719457598884791495829589 20149893736931150341753)
                ·
                  rfl

theorem cell22_529764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_529764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529764 prefixEnd_529764 := by exact prefixLift 529764
  have htrace : WordTrace (prefixWord ++ tailWord_529764) baseStart_529764 baseEnd_529764 := by
    simpa [prefixWord, tailWord_529764, baseEnd_529764] using wordTrace_append hprefix tailTrace_529764
  have hstable : (prefixWord ++ tailWord_529764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529764).length < 2 ^ (prefixWord ++ tailWord_529764).sum := by decide
  have hdescent : baseEnd_529764 < baseStart_529764 := by decide
  rcases family_descends (prefixWord ++ tailWord_529764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529770 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_529770 : Nat := 118140960795 + 529770 * 2 ^ 59
def prefixEnd_529770 : Nat := 4983230072969 + 3 ^ 40 * 529770 * 2
def baseEnd_529770 : Nat := 60450365851666112475253

theorem tailTrace_529770 : CollatzResearch.WordTrace tailWord_529770 prefixEnd_529770 60450365851666112475253 := by
  unfold tailWord_529770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830574822685310589456691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12881532860494161571884509 4830574822685310589456691)
  ·
    refine ⟨7245862234027965884185037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830574822685310589456691 7245862234027965884185037)
    ·
      refine ⟨2717198337760487206569389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7245862234027965884185037 2717198337760487206569389)
      ·
        refine ⟨1018949376660182702463521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2717198337760487206569389 1018949376660182702463521)
        ·
          refine ⟨764212032495137026847641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018949376660182702463521 764212032495137026847641)
          ·
            refine ⟨573159024371352770135731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764212032495137026847641 573159024371352770135731)
            ·
              refine ⟨859738536557029155203597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573159024371352770135731 859738536557029155203597)
              ·
                refine ⟨322401951208885933201349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859738536557029155203597 322401951208885933201349)
                ·
                  refine ⟨60450365851666112475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322401951208885933201349 60450365851666112475253)
                  ·
                    rfl

theorem cell22_529770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_529770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529770 prefixEnd_529770 := by exact prefixLift 529770
  have htrace : WordTrace (prefixWord ++ tailWord_529770) baseStart_529770 baseEnd_529770 := by
    simpa [prefixWord, tailWord_529770, baseEnd_529770] using wordTrace_append hprefix tailTrace_529770
  have hstable : (prefixWord ++ tailWord_529770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529770).length < 2 ^ (prefixWord ++ tailWord_529770).sum := by decide
  have hdescent : baseEnd_529770 < baseStart_529770 := by decide
  rcases family_descends (prefixWord ++ tailWord_529770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529781 : List Nat := [1, 3, 4, 1, 3, 2, 8]
def baseStart_529781 : Nat := 118140960795 + 529781 * 2 ^ 59
def prefixEnd_529781 : Nat := 4983230072969 + 3 ^ 40 * 529781 * 2
def baseEnd_529781 : Nat := 6716846780733258348175

theorem tailTrace_529781 : CollatzResearch.WordTrace tailWord_529781 prefixEnd_529781 6716846780733258348175 := by
  unfold tailWord_529781
  simp only [CollatzResearch.WordTrace]
  refine ⟨19322700493701391236477197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12881800329134260824318131 19322700493701391236477197)
  ·
    refine ⟨7246012685138021713678949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19322700493701391236477197 7246012685138021713678949)
    ·
      refine ⟨1358627378463379071314803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7246012685138021713678949 1358627378463379071314803)
      ·
        refine ⟨2037941067695068606972205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358627378463379071314803 2037941067695068606972205)
        ·
          refine ⟨764227900385650727614577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2037941067695068606972205 764227900385650727614577)
          ·
            refine ⟨573170925289238045710933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764227900385650727614577 573170925289238045710933)
            ·
              refine ⟨6716846780733258348175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 573170925289238045710933 6716846780733258348175)
              ·
                rfl

theorem cell22_529781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 8].length) (baseStart_529781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529781 prefixEnd_529781 := by exact prefixLift 529781
  have htrace : WordTrace (prefixWord ++ tailWord_529781) baseStart_529781 baseEnd_529781 := by
    simpa [prefixWord, tailWord_529781, baseEnd_529781] using wordTrace_append hprefix tailTrace_529781
  have hstable : (prefixWord ++ tailWord_529781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529781).length < 2 ^ (prefixWord ++ tailWord_529781).sum := by decide
  have hdescent : baseEnd_529781 < baseStart_529781 := by decide
  rcases family_descends (prefixWord ++ tailWord_529781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529809 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 5]
def baseStart_529809 : Nat := 118140960795 + 529809 * 2 ^ 59
def prefixEnd_529809 : Nat := 4983230072969 + 3 ^ 40 * 529809 * 2
def baseEnd_529809 : Nat := 60454816017338411900213

theorem tailTrace_529809 : CollatzResearch.WordTrace tailWord_529809 prefixEnd_529809 60454816017338411900213 := by
  unfold tailWord_529809
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323721737599952018496481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12882481158399968012330987 19323721737599952018496481)
  ·
    refine ⟨14492791303199964013872361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19323721737599952018496481 14492791303199964013872361)
    ·
      refine ⟨10869593477399973010404271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14492791303199964013872361 10869593477399973010404271)
      ·
        refine ⟨16304390216099959515606407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10869593477399973010404271 16304390216099959515606407)
        ·
          refine ⟨24456585324149939273409611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16304390216099959515606407 24456585324149939273409611)
          ·
            refine ⟨36684877986224908910114417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24456585324149939273409611 36684877986224908910114417)
            ·
              refine ⟨27513658489668681682585813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36684877986224908910114417 27513658489668681682585813)
              ·
                refine ⟨644851370851609726935605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27513658489668681682585813 644851370851609726935605)
                ·
                  refine ⟨60454816017338411900213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644851370851609726935605 60454816017338411900213)
                  ·
                    rfl

theorem cell22_529809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_529809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529809 prefixEnd_529809 := by exact prefixLift 529809
  have htrace : WordTrace (prefixWord ++ tailWord_529809) baseStart_529809 baseEnd_529809 := by
    simpa [prefixWord, tailWord_529809, baseEnd_529809] using wordTrace_append hprefix tailTrace_529809
  have hstable : (prefixWord ++ tailWord_529809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529809).length < 2 ^ (prefixWord ++ tailWord_529809).sum := by decide
  have hdescent : baseEnd_529809 < baseStart_529809 := by decide
  rcases family_descends (prefixWord ++ tailWord_529809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529903 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 2, 3]
def baseStart_529903 : Nat := 118140960795 + 529903 * 2 ^ 59
def prefixEnd_529903 : Nat := 4983230072969 + 3 ^ 40 * 529903 * 2
def baseEnd_529903 : Nat := 181396626173030323850351

theorem tailTrace_529903 : CollatzResearch.WordTrace tailWord_529903 prefixEnd_529903 181396626173030323850351 := by
  unfold tailWord_529903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19327150199259406072418363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12884766799506270714945575 19327150199259406072418363)
  ·
    refine ⟨28990725298889109108627545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19327150199259406072418363 28990725298889109108627545)
    ·
      refine ⟨21743043974166831831470659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28990725298889109108627545 21743043974166831831470659)
      ·
        refine ⟨32614565961250247747205989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21743043974166831831470659 32614565961250247747205989)
        ·
          refine ⟨6115231117734421452601123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32614565961250247747205989 6115231117734421452601123)
          ·
            refine ⟨9172846676601632178901685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115231117734421452601123 9172846676601632178901685)
            ·
              refine ⟨859954375931403016772033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9172846676601632178901685 859954375931403016772033)
              ·
                refine ⟨644965781948552262579025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859954375931403016772033 644965781948552262579025)
                ·
                  refine ⟨483724336461414196934269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644965781948552262579025 483724336461414196934269)
                  ·
                    refine ⟨181396626173030323850351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483724336461414196934269 181396626173030323850351)
                    ·
                      rfl

theorem cell22_529903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_529903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_529903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_529903 prefixEnd_529903 := by exact prefixLift 529903
  have htrace : WordTrace (prefixWord ++ tailWord_529903) baseStart_529903 baseEnd_529903 := by
    simpa [prefixWord, tailWord_529903, baseEnd_529903] using wordTrace_append hprefix tailTrace_529903
  have hstable : (prefixWord ++ tailWord_529903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529903).length < 2 ^ (prefixWord ++ tailWord_529903).sum := by decide
  have hdescent : baseEnd_529903 < baseStart_529903 := by decide
  rcases family_descends (prefixWord ++ tailWord_529903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530072 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_530072 : Nat := 118140960795 + 530072 * 2 ^ 59
def prefixEnd_530072 : Nat := 4983230072969 + 3 ^ 40 * 530072 * 2
def baseEnd_530072 : Nat := 181454478326770216374833

theorem tailTrace_530072 : CollatzResearch.WordTrace tailWord_530072 prefixEnd_530072 181454478326770216374833 := by
  unfold tailWord_530072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666657067823573967660235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12888876090431431956880313 9666657067823573967660235)
  ·
    refine ⟨14499985601735360951490353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666657067823573967660235 14499985601735360951490353)
    ·
      refine ⟨10874989201301520713617765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14499985601735360951490353 10874989201301520713617765)
      ·
        refine ⟨2039060475244035133803331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10874989201301520713617765 2039060475244035133803331)
        ·
          refine ⟨3058590712866052700704997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039060475244035133803331 3058590712866052700704997)
          ·
            refine ⟨573485758662384881382187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3058590712866052700704997 573485758662384881382187)
            ·
              refine ⟨860228637993577322073281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573485758662384881382187 860228637993577322073281)
              ·
                refine ⟨645171478495182991554961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860228637993577322073281 645171478495182991554961)
                ·
                  refine ⟨483878608871387243666221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645171478495182991554961 483878608871387243666221)
                  ·
                    refine ⟨181454478326770216374833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483878608871387243666221 181454478326770216374833)
                    ·
                      rfl

theorem cell22_530072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_530072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530072 prefixEnd_530072 := by exact prefixLift 530072
  have htrace : WordTrace (prefixWord ++ tailWord_530072) baseStart_530072 baseEnd_530072 := by
    simpa [prefixWord, tailWord_530072, baseEnd_530072] using wordTrace_append hprefix tailTrace_530072
  have hstable : (prefixWord ++ tailWord_530072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530072).length < 2 ^ (prefixWord ++ tailWord_530072).sum := by decide
  have hdescent : baseEnd_530072 < baseStart_530072 := by decide
  rcases family_descends (prefixWord ++ tailWord_530072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530102 : List Nat := [5, 1, 3, 1, 1, 1, 4, 6]
def baseStart_530102 : Nat := 118140960795 + 530102 * 2 ^ 59
def prefixEnd_530102 : Nat := 4983230072969 + 3 ^ 40 * 530102 * 2
def baseEnd_530102 : Nat := 20162749771095570902749

theorem tailTrace_530102 : CollatzResearch.WordTrace tailWord_530102 prefixEnd_530102 20162749771095570902749 := by
  unfold tailWord_530102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208400520346153941182035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12889605550358975372608373 1208400520346153941182035)
  ·
    refine ⟨1812600780519230911773053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208400520346153941182035 1812600780519230911773053)
    ·
      refine ⟨679725292694711591914895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1812600780519230911773053 679725292694711591914895)
      ·
        refine ⟨1019587939042067387872343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679725292694711591914895 1019587939042067387872343)
        ·
          refine ⟨1529381908563101081808515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019587939042067387872343 1529381908563101081808515)
          ·
            refine ⟨2294072862844651622712773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529381908563101081808515 2294072862844651622712773)
            ·
              refine ⟨430138661783372179258645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2294072862844651622712773 430138661783372179258645)
              ·
                refine ⟨20162749771095570902749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430138661783372179258645 20162749771095570902749)
                ·
                  rfl

theorem cell22_530102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_530102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530102 prefixEnd_530102 := by exact prefixLift 530102
  have htrace : WordTrace (prefixWord ++ tailWord_530102) baseStart_530102 baseEnd_530102 := by
    simpa [prefixWord, tailWord_530102, baseEnd_530102] using wordTrace_append hprefix tailTrace_530102
  have hstable : (prefixWord ++ tailWord_530102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530102).length < 2 ^ (prefixWord ++ tailWord_530102).sum := by decide
  have hdescent : baseEnd_530102 < baseStart_530102 := by decide
  rcases family_descends (prefixWord ++ tailWord_530102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530143 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 3, 4]
def baseStart_530143 : Nat := 118140960795 + 530143 * 2 ^ 59
def prefixEnd_530143 : Nat := 4983230072969 + 3 ^ 40 * 530143 * 2
def baseEnd_530143 : Nat := 181478783077749697849615

theorem tailTrace_530143 : CollatzResearch.WordTrace tailWord_530143 prefixEnd_530143 181478783077749697849615 := by
  unfold tailWord_530143
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335903718389927061155083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890602478926618040770055 19335903718389927061155083)
  ·
    refine ⟨29003855577584890591732625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19335903718389927061155083 29003855577584890591732625)
    ·
      refine ⟨21752891683188667943799469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29003855577584890591732625 21752891683188667943799469)
      ·
        refine ⟨8157334381195750478924801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21752891683188667943799469 8157334381195750478924801)
        ·
          refine ⟨6118000785896812859193601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8157334381195750478924801 6118000785896812859193601)
          ·
            refine ⟨4588500589422609644395201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6118000785896812859193601 4588500589422609644395201)
            ·
              refine ⟨3441375442066957233296401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588500589422609644395201 3441375442066957233296401)
              ·
                refine ⟨2581031581550217924972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3441375442066957233296401 2581031581550217924972301)
                ·
                  refine ⟨967886843081331721864613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2581031581550217924972301 967886843081331721864613)
                  ·
                    refine ⟨181478783077749697849615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 967886843081331721864613 181478783077749697849615)
                    ·
                      rfl

theorem cell22_530143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_530143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530143 prefixEnd_530143 := by exact prefixLift 530143
  have htrace : WordTrace (prefixWord ++ tailWord_530143) baseStart_530143 baseEnd_530143 := by
    simpa [prefixWord, tailWord_530143, baseEnd_530143] using wordTrace_append hprefix tailTrace_530143
  have hstable : (prefixWord ++ tailWord_530143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530143).length < 2 ^ (prefixWord ++ tailWord_530143).sum := by decide
  have hdescent : baseEnd_530143 < baseStart_530143 := by decide
  rcases family_descends (prefixWord ++ tailWord_530143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530158 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_530158 : Nat := 118140960795 + 530158 * 2 ^ 59
def prefixEnd_530158 : Nat := 4983230072969 + 3 ^ 40 * 530158 * 2
def baseEnd_530158 : Nat := 60494639294764886241523

theorem tailTrace_530158 : CollatzResearch.WordTrace tailWord_530158 prefixEnd_530158 60494639294764886241523 := by
  unfold tailWord_530158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417056351666948077868891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12890967208890389748634085 2417056351666948077868891)
  ·
    refine ⟨3625584527500422116803337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417056351666948077868891 3625584527500422116803337)
    ·
      refine ⟨2719188395625316587602503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3625584527500422116803337 2719188395625316587602503)
      ·
        refine ⟨4078782593437974881403755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719188395625316587602503 4078782593437974881403755)
        ·
          refine ⟨6118173890156962322105633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078782593437974881403755 6118173890156962322105633)
          ·
            refine ⟨4588630417617721741579225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6118173890156962322105633 4588630417617721741579225)
            ·
              refine ⟨3441472813213291306184419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588630417617721741579225 3441472813213291306184419)
              ·
                refine ⟨5162209219819936959276629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441472813213291306184419 5162209219819936959276629)
                ·
                  refine ⟨60494639294764886241523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5162209219819936959276629 60494639294764886241523)
                  ·
                    rfl

theorem cell22_530158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_530158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530158 prefixEnd_530158 := by exact prefixLift 530158
  have htrace : WordTrace (prefixWord ++ tailWord_530158) baseStart_530158 baseEnd_530158 := by
    simpa [prefixWord, tailWord_530158, baseEnd_530158] using wordTrace_append hprefix tailTrace_530158
  have hstable : (prefixWord ++ tailWord_530158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530158).length < 2 ^ (prefixWord ++ tailWord_530158).sum := by decide
  have hdescent : baseEnd_530158 < baseStart_530158 := by decide
  rcases family_descends (prefixWord ++ tailWord_530158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530190 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_530190 : Nat := 118140960795 + 530190 * 2 ^ 59
def prefixEnd_530190 : Nat := 4983230072969 + 3 ^ 40 * 530190 * 2
def baseEnd_530190 : Nat := 181494872138257241924471

theorem tailTrace_530190 : CollatzResearch.WordTrace tailWord_530190 prefixEnd_530190 181494872138257241924471 := by
  unfold tailWord_530190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417202243652456761014503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12891745299479769392077349 2417202243652456761014503)
  ·
    refine ⟨3625803365478685141521755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417202243652456761014503 3625803365478685141521755)
    ·
      refine ⟨5438705048218027712282633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625803365478685141521755 5438705048218027712282633)
      ·
        refine ⟨4079028786163520784211975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438705048218027712282633 4079028786163520784211975)
        ·
          refine ⟨6118543179245281176317963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079028786163520784211975 6118543179245281176317963)
          ·
            refine ⟨9177814768867921764476945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118543179245281176317963 9177814768867921764476945)
            ·
              refine ⟨6883361076650941323357709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9177814768867921764476945 6883361076650941323357709)
              ·
                refine ⟨2581260403744102996259141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883361076650941323357709 2581260403744102996259141)
                ·
                  refine ⟨483986325702019311798589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2581260403744102996259141 483986325702019311798589)
                  ·
                    refine ⟨181494872138257241924471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483986325702019311798589 181494872138257241924471)
                    ·
                      rfl

theorem cell22_530190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_530190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530190 prefixEnd_530190 := by exact prefixLift 530190
  have htrace : WordTrace (prefixWord ++ tailWord_530190) baseStart_530190 baseEnd_530190 := by
    simpa [prefixWord, tailWord_530190, baseEnd_530190] using wordTrace_append hprefix tailTrace_530190
  have hstable : (prefixWord ++ tailWord_530190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530190).length < 2 ^ (prefixWord ++ tailWord_530190).sum := by decide
  have hdescent : baseEnd_530190 < baseStart_530190 := by decide
  rcases family_descends (prefixWord ++ tailWord_530190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530220 : List Nat := [2, 2, 1, 1, 1, 6, 3, 6]
def baseStart_530220 : Nat := 118140960795 + 530220 * 2 ^ 59
def prefixEnd_530220 : Nat := 4983230072969 + 3 ^ 40 * 530220 * 2
def baseEnd_530220 : Nat := 20167237972371907074931

theorem tailTrace_530220 : CollatzResearch.WordTrace tailWord_530220 prefixEnd_530220 20167237972371907074931 := by
  unfold tailWord_530220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669356069555484605854057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12892474759407312807805409 9669356069555484605854057)
  ·
    refine ⟨7252017052166613454390543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9669356069555484605854057 7252017052166613454390543)
    ·
      refine ⟨10878025578249920181585815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7252017052166613454390543 10878025578249920181585815)
      ·
        refine ⟨16317038367374880272378723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10878025578249920181585815 16317038367374880272378723)
        ·
          refine ⟨24475557551062320408568085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16317038367374880272378723 24475557551062320408568085)
          ·
            refine ⟨1147291760206046269151629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24475557551062320408568085 1147291760206046269151629)
            ·
              refine ⟨430234410077267350931861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147291760206046269151629 430234410077267350931861)
              ·
                refine ⟨20167237972371907074931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430234410077267350931861 20167237972371907074931)
                ·
                  rfl

theorem cell22_530220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_530220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530220 prefixEnd_530220 := by exact prefixLift 530220
  have htrace : WordTrace (prefixWord ++ tailWord_530220) baseStart_530220 baseEnd_530220 := by
    simpa [prefixWord, tailWord_530220, baseEnd_530220] using wordTrace_append hprefix tailTrace_530220
  have hstable : (prefixWord ++ tailWord_530220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530220).length < 2 ^ (prefixWord ++ tailWord_530220).sum := by decide
  have hdescent : baseEnd_530220 < baseStart_530220 := by decide
  rcases family_descends (prefixWord ++ tailWord_530220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530222 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_530222 : Nat := 118140960795 + 530222 * 2 ^ 59
def prefixEnd_530222 : Nat := 4983230072969 + 3 ^ 40 * 530222 * 2
def baseEnd_530222 : Nat := 181505826392219825124373

theorem tailTrace_530222 : CollatzResearch.WordTrace tailWord_530222 prefixEnd_530222 181505826392219825124373 := by
  unfold tailWord_530222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417348135637965444160115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12892523390069149035520613 2417348135637965444160115)
  ·
    refine ⟨3626022203456948166240173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417348135637965444160115 3626022203456948166240173)
    ·
      refine ⟨1359758326296355562340065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3626022203456948166240173 1359758326296355562340065)
      ·
        refine ⟨1019818744722266671755049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359758326296355562340065 1019818744722266671755049)
        ·
          refine ⟨764864058541700003816287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019818744722266671755049 764864058541700003816287)
          ·
            refine ⟨1147296087812550005724431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764864058541700003816287 1147296087812550005724431)
            ·
              refine ⟨1720944131718825008586647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147296087812550005724431 1720944131718825008586647)
              ·
                refine ⟨2581416197578237512879971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720944131718825008586647 2581416197578237512879971)
                ·
                  refine ⟨3872124296367356269319957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581416197578237512879971 3872124296367356269319957)
                  ·
                    refine ⟨181505826392219825124373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3872124296367356269319957 181505826392219825124373)
                    ·
                      rfl

theorem cell22_530222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_530222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530222 prefixEnd_530222 := by exact prefixLift 530222
  have htrace : WordTrace (prefixWord ++ tailWord_530222) baseStart_530222 baseEnd_530222 := by
    simpa [prefixWord, tailWord_530222, baseEnd_530222] using wordTrace_append hprefix tailTrace_530222
  have hstable : (prefixWord ++ tailWord_530222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530222).length < 2 ^ (prefixWord ++ tailWord_530222).sum := by decide
  have hdescent : baseEnd_530222 < baseStart_530222 := by decide
  rcases family_descends (prefixWord ++ tailWord_530222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530286 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_530286 : Nat := 118140960795 + 530286 * 2 ^ 59
def prefixEnd_530286 : Nat := 4983230072969 + 3 ^ 40 * 530286 * 2
def baseEnd_530286 : Nat := 181527734900144991524177

theorem tailTrace_530286 : CollatzResearch.WordTrace tailWord_530286 prefixEnd_530286 181527734900144991524177 := by
  unfold tailWord_530286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417639919608982810451339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12894079571247908322407141 2417639919608982810451339)
  ·
    refine ⟨3626459879413474215677009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417639919608982810451339 3626459879413474215677009)
    ·
      refine ⟨2719844909560105661757757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3626459879413474215677009 2719844909560105661757757)
      ·
        refine ⟨1019941841085039623159159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2719844909560105661757757 1019941841085039623159159)
        ·
          refine ⟨1529912761627559434738739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019941841085039623159159 1529912761627559434738739)
          ·
            refine ⟨2294869142441339152108109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529912761627559434738739 2294869142441339152108109)
            ·
              refine ⟨860575928415502182040541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2294869142441339152108109 860575928415502182040541)
              ·
                refine ⟨322715973155813318265203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860575928415502182040541 322715973155813318265203)
                ·
                  refine ⟨484073959733719977397805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322715973155813318265203 484073959733719977397805)
                  ·
                    refine ⟨181527734900144991524177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484073959733719977397805 181527734900144991524177)
                    ·
                      rfl

theorem cell22_530286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_530286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530286 prefixEnd_530286 := by exact prefixLift 530286
  have htrace : WordTrace (prefixWord ++ tailWord_530286) baseStart_530286 baseEnd_530286 := by
    simpa [prefixWord, tailWord_530286, baseEnd_530286] using wordTrace_append hprefix tailTrace_530286
  have hstable : (prefixWord ++ tailWord_530286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530286).length < 2 ^ (prefixWord ++ tailWord_530286).sum := by decide
  have hdescent : baseEnd_530286 < baseStart_530286 := by decide
  rcases family_descends (prefixWord ++ tailWord_530286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530325 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_530325 : Nat := 118140960795 + 530325 * 2 ^ 59
def prefixEnd_530325 : Nat := 4983230072969 + 3 ^ 40 * 530325 * 2
def baseEnd_530325 : Nat := 181541085397161889799057

theorem tailTrace_530325 : CollatzResearch.WordTrace tailWord_530325 prefixEnd_530325 181541085397161889799057 := by
  unfold tailWord_530325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342541803730572144280429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12895027869153714762853619 19342541803730572144280429)
  ·
    refine ⟨7253453176398964554105161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19342541803730572144280429 7253453176398964554105161)
    ·
      refine ⟨5440089882299223415578871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7253453176398964554105161 5440089882299223415578871)
      ·
        refine ⟨8160134823448835123368307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440089882299223415578871 8160134823448835123368307)
        ·
          refine ⟨12240202235173252685052461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8160134823448835123368307 12240202235173252685052461)
          ·
            refine ⟨4590075838189969756894673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12240202235173252685052461 4590075838189969756894673)
            ·
              refine ⟨3442556878642477317671005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4590075838189969756894673 3442556878642477317671005)
              ·
                refine ⟨1290958829490928994126627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3442556878642477317671005 1290958829490928994126627)
                ·
                  refine ⟨1936438244236393491189941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290958829490928994126627 1936438244236393491189941)
                  ·
                    refine ⟨181541085397161889799057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1936438244236393491189941 181541085397161889799057)
                    ·
                      rfl

theorem cell22_530325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_530325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530325 prefixEnd_530325 := by exact prefixLift 530325
  have htrace : WordTrace (prefixWord ++ tailWord_530325) baseStart_530325 baseEnd_530325 := by
    simpa [prefixWord, tailWord_530325, baseEnd_530325] using wordTrace_append hprefix tailTrace_530325
  have hstable : (prefixWord ++ tailWord_530325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530325).length < 2 ^ (prefixWord ++ tailWord_530325).sum := by decide
  have hdescent : baseEnd_530325 < baseStart_530325 := by decide
  rcases family_descends (prefixWord ++ tailWord_530325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530357 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_530357 : Nat := 118140960795 + 530357 * 2 ^ 59
def prefixEnd_530357 : Nat := 4983230072969 + 3 ^ 40 * 530357 * 2
def baseEnd_530357 : Nat := 181552039651124472998959

theorem tailTrace_530357 : CollatzResearch.WordTrace tailWord_530357 prefixEnd_530357 181552039651124472998959 := by
  unfold tailWord_530357
  simp only [CollatzResearch.WordTrace]
  refine ⟨19343708939614641609445325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12895805959743094406296883 19343708939614641609445325)
  ·
    refine ⟨7253890852355490603541997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19343708939614641609445325 7253890852355490603541997)
    ·
      refine ⟨2720209069633308976328249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7253890852355490603541997 2720209069633308976328249)
      ·
        refine ⟨2040156802224981732246187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2720209069633308976328249 2040156802224981732246187)
        ·
          refine ⟨3060235203337472598369281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040156802224981732246187 3060235203337472598369281)
          ·
            refine ⟨2295176402503104448776961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060235203337472598369281 2295176402503104448776961)
            ·
              refine ⟨1721382301877328336582721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295176402503104448776961 1721382301877328336582721)
              ·
                refine ⟨1291036726407996252437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721382301877328336582721 1291036726407996252437041)
                ·
                  refine ⟨968277544805997189327781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291036726407996252437041 968277544805997189327781)
                  ·
                    refine ⟨181552039651124472998959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 968277544805997189327781 181552039651124472998959)
                    ·
                      rfl

theorem cell22_530357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_530357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530357 prefixEnd_530357 := by exact prefixLift 530357
  have htrace : WordTrace (prefixWord ++ tailWord_530357) baseStart_530357 baseEnd_530357 := by
    simpa [prefixWord, tailWord_530357, baseEnd_530357] using wordTrace_append hprefix tailTrace_530357
  have hstable : (prefixWord ++ tailWord_530357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530357).length < 2 ^ (prefixWord ++ tailWord_530357).sum := by decide
  have hdescent : baseEnd_530357 < baseStart_530357 := by decide
  rcases family_descends (prefixWord ++ tailWord_530357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530415 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_530415 : Nat := 118140960795 + 530415 * 2 ^ 59
def prefixEnd_530415 : Nat := 4983230072969 + 3 ^ 40 * 530415 * 2
def baseEnd_530415 : Nat := 181571894236431655048781

theorem tailTrace_530415 : CollatzResearch.WordTrace tailWord_530415 prefixEnd_530415 181571894236431655048781 := by
  unfold tailWord_530415
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345824373404517515056699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12897216248936345010037799 19345824373404517515056699)
  ·
    refine ⟨29018736560106776272585049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19345824373404517515056699 29018736560106776272585049)
    ·
      refine ⟨21764052420080082204438787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29018736560106776272585049 21764052420080082204438787)
      ·
        refine ⟨32646078630120123306658181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21764052420080082204438787 32646078630120123306658181)
        ·
          refine ⟨6121139743147523119998409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32646078630120123306658181 6121139743147523119998409)
          ·
            refine ⟨4590854807360642339998807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6121139743147523119998409 4590854807360642339998807)
            ·
              refine ⟨6886282211040963509998211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590854807360642339998807 6886282211040963509998211)
              ·
                refine ⟨10329423316561445264997317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6886282211040963509998211 10329423316561445264997317)
                ·
                  refine ⟨1936766871855270987186997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10329423316561445264997317 1936766871855270987186997)
                  ·
                    refine ⟨181571894236431655048781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1936766871855270987186997 181571894236431655048781)
                    ·
                      rfl

theorem cell22_530415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_530415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530415 prefixEnd_530415 := by exact prefixLift 530415
  have htrace : WordTrace (prefixWord ++ tailWord_530415) baseStart_530415 baseEnd_530415 := by
    simpa [prefixWord, tailWord_530415, baseEnd_530415] using wordTrace_append hprefix tailTrace_530415
  have hstable : (prefixWord ++ tailWord_530415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530415).length < 2 ^ (prefixWord ++ tailWord_530415).sum := by decide
  have hdescent : baseEnd_530415 < baseStart_530415 := by decide
  rcases family_descends (prefixWord ++ tailWord_530415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530417 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 7]
def baseStart_530417 : Nat := 118140960795 + 530417 * 2 ^ 59
def prefixEnd_530417 : Nat := 4983230072969 + 3 ^ 40 * 530417 * 2
def baseEnd_530417 : Nat := 60524192959101438832925

theorem tailTrace_530417 : CollatzResearch.WordTrace tailWord_530417 prefixEnd_530417 60524192959101438832925 := by
  unfold tailWord_530417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345897319397271856629505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12897264879598181237753003 19345897319397271856629505)
  ·
    refine ⟨14509422989547953892472129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19345897319397271856629505 14509422989547953892472129)
    ·
      refine ⟨10882067242160965419354097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14509422989547953892472129 10882067242160965419354097)
      ·
        refine ⟨8161550431620724064515573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10882067242160965419354097 8161550431620724064515573)
        ·
          refine ⟨765145352964442881048335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8161550431620724064515573 765145352964442881048335)
          ·
            refine ⟨1147718029446664321572503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765145352964442881048335 1147718029446664321572503)
            ·
              refine ⟨1721577044169996482358755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147718029446664321572503 1721577044169996482358755)
              ·
                refine ⟨2582365566254994723538133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721577044169996482358755 2582365566254994723538133)
                ·
                  refine ⟨60524192959101438832925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2582365566254994723538133 60524192959101438832925)
                  ·
                    rfl

theorem cell22_530417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_530417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530417 prefixEnd_530417 := by exact prefixLift 530417
  have htrace : WordTrace (prefixWord ++ tailWord_530417) baseStart_530417 baseEnd_530417 := by
    simpa [prefixWord, tailWord_530417, baseEnd_530417] using wordTrace_append hprefix tailTrace_530417
  have hstable : (prefixWord ++ tailWord_530417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530417).length < 2 ^ (prefixWord ++ tailWord_530417).sum := by decide
  have hdescent : baseEnd_530417 < baseStart_530417 := by decide
  rcases family_descends (prefixWord ++ tailWord_530417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530455 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 1, 3]
def baseStart_530455 : Nat := 118140960795 + 530455 * 2 ^ 59
def prefixEnd_530455 : Nat := 4983230072969 + 3 ^ 40 * 530455 * 2
def baseEnd_530455 : Nat := 181585587053884884048659

theorem tailTrace_530455 : CollatzResearch.WordTrace tailWord_530455 prefixEnd_530455 181585587053884884048659 := by
  unfold tailWord_530455
  simp only [CollatzResearch.WordTrace]
  refine ⟨19347283293259604346512819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12898188862173069564341879 19347283293259604346512819)
  ·
    refine ⟨29020924939889406519769229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19347283293259604346512819 29020924939889406519769229)
    ·
      refine ⟨10882846852458527444913461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29020924939889406519769229 10882846852458527444913461)
      ·
        refine ⟨1020266892417986947960637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10882846852458527444913461 1020266892417986947960637)
        ·
          refine ⟨382600084656745105485239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020266892417986947960637 382600084656745105485239)
          ·
            refine ⟨573900126985117658227859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382600084656745105485239 573900126985117658227859)
            ·
              refine ⟨860850190477676487341789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573900126985117658227859 860850190477676487341789)
              ·
                refine ⟨322818821429128682753171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860850190477676487341789 322818821429128682753171)
                ·
                  refine ⟨484228232143693024129757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322818821429128682753171 484228232143693024129757)
                  ·
                    refine ⟨181585587053884884048659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484228232143693024129757 181585587053884884048659)
                    ·
                      rfl

theorem cell22_530455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_530455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530455 prefixEnd_530455 := by exact prefixLift 530455
  have htrace : WordTrace (prefixWord ++ tailWord_530455) baseStart_530455 baseEnd_530455 := by
    simpa [prefixWord, tailWord_530455, baseEnd_530455] using wordTrace_append hprefix tailTrace_530455
  have hstable : (prefixWord ++ tailWord_530455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530455).length < 2 ^ (prefixWord ++ tailWord_530455).sum := by decide
  have hdescent : baseEnd_530455 < baseStart_530455 := by decide
  rcases family_descends (prefixWord ++ tailWord_530455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530475 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_530475 : Nat := 118140960795 + 530475 * 2 ^ 59
def prefixEnd_530475 : Nat := 4983230072969 + 3 ^ 40 * 530475 * 2
def baseEnd_530475 : Nat := 181592433462611498548597

theorem tailTrace_530475 : CollatzResearch.WordTrace tailWord_530475 prefixEnd_530475 181592433462611498548597 := by
  unfold tailWord_530475
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348012753187147762240879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12898675168791431841493919 19348012753187147762240879)
  ·
    refine ⟨29022019129780721643361319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19348012753187147762240879 29022019129780721643361319)
    ·
      refine ⟨43533028694671082465041979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29022019129780721643361319 43533028694671082465041979)
      ·
        refine ⟨65299543042006623697562969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43533028694671082465041979 65299543042006623697562969)
        ·
          refine ⟨48974657281504967773172227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65299543042006623697562969 48974657281504967773172227)
          ·
            refine ⟨73461985922257451659758341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48974657281504967773172227 73461985922257451659758341)
            ·
              refine ⟨13774122360423272186204689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73461985922257451659758341 13774122360423272186204689)
              ·
                refine ⟨10330591770317454139653517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13774122360423272186204689 10330591770317454139653517)
                ·
                  refine ⟨3873971913869045302370069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10330591770317454139653517 3873971913869045302370069)
                  ·
                    refine ⟨181592433462611498548597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3873971913869045302370069 181592433462611498548597)
                    ·
                      rfl

theorem cell22_530475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_530475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530475 prefixEnd_530475 := by exact prefixLift 530475
  have htrace : WordTrace (prefixWord ++ tailWord_530475) baseStart_530475 baseEnd_530475 := by
    simpa [prefixWord, tailWord_530475, baseEnd_530475] using wordTrace_append hprefix tailTrace_530475
  have hstable : (prefixWord ++ tailWord_530475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530475).length < 2 ^ (prefixWord ++ tailWord_530475).sum := by decide
  have hdescent : baseEnd_530475 < baseStart_530475 := by decide
  rcases family_descends (prefixWord ++ tailWord_530475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530492 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_530492 : Nat := 118140960795 + 530492 * 2 ^ 59
def prefixEnd_530492 : Nat := 4983230072969 + 3 ^ 40 * 530492 * 2
def baseEnd_530492 : Nat := 181598252910029120873545

theorem tailTrace_530492 : CollatzResearch.WordTrace tailWord_530492 prefixEnd_530492 181598252910029120873545 := by
  unfold tailWord_530492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674316397062779832804865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12899088529417039777073153 9674316397062779832804865)
  ·
    refine ⟨7255737297797084874603649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9674316397062779832804865 7255737297797084874603649)
    ·
      refine ⟨5441802973347813655952737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7255737297797084874603649 5441802973347813655952737)
      ·
        refine ⟨4081352230010860241964553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5441802973347813655952737 4081352230010860241964553)
        ·
          refine ⟨3061014172508145181473415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4081352230010860241964553 3061014172508145181473415)
          ·
            refine ⟨4591521258762217772210123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061014172508145181473415 4591521258762217772210123)
            ·
              refine ⟨6887281888143326658315185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591521258762217772210123 6887281888143326658315185)
              ·
                refine ⟨5165461416107494993736389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6887281888143326658315185 5165461416107494993736389)
                ·
                  refine ⟨968524015520155311325573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5165461416107494993736389 968524015520155311325573)
                  ·
                    refine ⟨181598252910029120873545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 968524015520155311325573 181598252910029120873545)
                    ·
                      rfl

theorem cell22_530492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_530492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530492 prefixEnd_530492 := by exact prefixLift 530492
  have htrace : WordTrace (prefixWord ++ tailWord_530492) baseStart_530492 baseEnd_530492 := by
    simpa [prefixWord, tailWord_530492, baseEnd_530492] using wordTrace_append hprefix tailTrace_530492
  have hstable : (prefixWord ++ tailWord_530492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530492).length < 2 ^ (prefixWord ++ tailWord_530492).sum := by decide
  have hdescent : baseEnd_530492 < baseStart_530492 := by decide
  rcases family_descends (prefixWord ++ tailWord_530492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530530 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_530530 : Nat := 118140960795 + 530530 * 2 ^ 59
def prefixEnd_530530 : Nat := 4983230072969 + 3 ^ 40 * 530530 * 2
def baseEnd_530530 : Nat := 60537087028869896141143

theorem tailTrace_530530 : CollatzResearch.WordTrace tailWord_530530 prefixEnd_530530 60537087028869896141143 := by
  unfold tailWord_530530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837504691996973038873261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12900012511991928103662029 4837504691996973038873261)
  ·
    refine ⟨1814064259498864889577473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4837504691996973038873261 1814064259498864889577473)
    ·
      refine ⟨1360548194624148667183105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1814064259498864889577473 1360548194624148667183105)
      ·
        refine ⟨1020411145968111500387329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360548194624148667183105 1020411145968111500387329)
        ·
          refine ⟨765308359476083625290497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020411145968111500387329 765308359476083625290497)
          ·
            refine ⟨573981269607062718967873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765308359476083625290497 573981269607062718967873)
            ·
              refine ⟨430485952205297039225905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573981269607062718967873 430485952205297039225905)
              ·
                refine ⟨322864464153972779419429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430485952205297039225905 322864464153972779419429)
                ·
                  refine ⟨60537087028869896141143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322864464153972779419429 60537087028869896141143)
                  ·
                    rfl

theorem cell22_530530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_530530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530530 prefixEnd_530530 := by exact prefixLift 530530
  have htrace : WordTrace (prefixWord ++ tailWord_530530) baseStart_530530 baseEnd_530530 := by
    simpa [prefixWord, tailWord_530530, baseEnd_530530] using wordTrace_append hprefix tailTrace_530530
  have hstable : (prefixWord ++ tailWord_530530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530530).length < 2 ^ (prefixWord ++ tailWord_530530).sum := by decide
  have hdescent : baseEnd_530530 < baseStart_530530 := by decide
  rcases family_descends (prefixWord ++ tailWord_530530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530629 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_530629 : Nat := 118140960795 + 530629 * 2 ^ 59
def prefixEnd_530629 : Nat := 4983230072969 + 3 ^ 40 * 530629 * 2
def baseEnd_530629 : Nat := 181645150809806430198125

theorem tailTrace_530629 : CollatzResearch.WordTrace tailWord_530629 prefixEnd_530629 181645150809806430198125 := by
  unfold tailWord_530629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19353629594629232063346941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12902419729752821375564627 19353629594629232063346941)
  ·
    refine ⟨7257611097985962023755103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19353629594629232063346941 7257611097985962023755103)
    ·
      refine ⟨10886416646978943035632655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257611097985962023755103 10886416646978943035632655)
      ·
        refine ⟨16329624970468414553448983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10886416646978943035632655 16329624970468414553448983)
        ·
          refine ⟨24494437455702621830173475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16329624970468414553448983 24494437455702621830173475)
          ·
            refine ⟨36741656183553932745260213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24494437455702621830173475 36741656183553932745260213)
            ·
              refine ⟨3444530267208181194868145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36741656183553932745260213 3444530267208181194868145)
              ·
                refine ⟨2583397700406135896151109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444530267208181194868145 2583397700406135896151109)
                ·
                  refine ⟨484387068826150480528333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2583397700406135896151109 484387068826150480528333)
                  ·
                    refine ⟨181645150809806430198125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484387068826150480528333 181645150809806430198125)
                    ·
                      rfl

theorem cell22_530629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_530629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530629 prefixEnd_530629 := by exact prefixLift 530629
  have htrace : WordTrace (prefixWord ++ tailWord_530629) baseStart_530629 baseEnd_530629 := by
    simpa [prefixWord, tailWord_530629, baseEnd_530629] using wordTrace_append hprefix tailTrace_530629
  have hstable : (prefixWord ++ tailWord_530629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530629).length < 2 ^ (prefixWord ++ tailWord_530629).sum := by decide
  have hdescent : baseEnd_530629 < baseStart_530629 := by decide
  rcases family_descends (prefixWord ++ tailWord_530629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530648 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_530648 : Nat := 118140960795 + 530648 * 2 ^ 59
def prefixEnd_530648 : Nat := 4983230072969 + 3 ^ 40 * 530648 * 2
def baseEnd_530648 : Nat := 60550551632698904657689

theorem tailTrace_530648 : CollatzResearch.WordTrace tailWord_530648 prefixEnd_530648 60550551632698904657689 := by
  unfold tailWord_530648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677161290780199154144299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12902881721040265538859065 9677161290780199154144299)
  ·
    refine ⟨14515741936170298731216449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9677161290780199154144299 14515741936170298731216449)
    ·
      refine ⟨10886806452127724048412337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14515741936170298731216449 10886806452127724048412337)
      ·
        refine ⟨8165104839095793036309253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10886806452127724048412337 8165104839095793036309253)
        ·
          refine ⟨1530957157330461194307985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8165104839095793036309253 1530957157330461194307985)
          ·
            refine ⟨1148217867997845895730989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530957157330461194307985 1148217867997845895730989)
            ·
              refine ⟨430581700499192210899121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148217867997845895730989 430581700499192210899121)
              ·
                refine ⟨322936275374394158174341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430581700499192210899121 322936275374394158174341)
                ·
                  refine ⟨60550551632698904657689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322936275374394158174341 60550551632698904657689)
                  ·
                    rfl

theorem cell22_530648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_530648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530648 prefixEnd_530648 := by exact prefixLift 530648
  have htrace : WordTrace (prefixWord ++ tailWord_530648) baseStart_530648 baseEnd_530648 := by
    simpa [prefixWord, tailWord_530648, baseEnd_530648] using wordTrace_append hprefix tailTrace_530648
  have hstable : (prefixWord ++ tailWord_530648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530648).length < 2 ^ (prefixWord ++ tailWord_530648).sum := by decide
  have hdescent : baseEnd_530648 < baseStart_530648 := by decide
  rcases family_descends (prefixWord ++ tailWord_530648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530663 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 2, 3]
def baseStart_530663 : Nat := 118140960795 + 530663 * 2 ^ 59
def prefixEnd_530663 : Nat := 4983230072969 + 3 ^ 40 * 530663 * 2
def baseEnd_530663 : Nat := 181656789704641674848021

theorem tailTrace_530663 : CollatzResearch.WordTrace tailWord_530663 prefixEnd_530663 181656789704641674848021 := by
  unfold tailWord_530663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19354869676506055870084643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12903246451004037246723095 19354869676506055870084643)
  ·
    refine ⟨29032304514759083805126965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19354869676506055870084643 29032304514759083805126965)
    ·
      refine ⟨2721778548258664106730653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29032304514759083805126965 2721778548258664106730653)
      ·
        refine ⟨1020666955596999040023995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2721778548258664106730653 1020666955596999040023995)
        ·
          refine ⟨1531000433395498560035993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020666955596999040023995 1531000433395498560035993)
          ·
            refine ⟨1148250325046623920026995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531000433395498560035993 1148250325046623920026995)
            ·
              refine ⟨1722375487569935880040493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148250325046623920026995 1722375487569935880040493)
              ·
                refine ⟨645890807838725955015185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722375487569935880040493 645890807838725955015185)
                ·
                  refine ⟨484418105879044466261389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645890807838725955015185 484418105879044466261389)
                  ·
                    refine ⟨181656789704641674848021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484418105879044466261389 181656789704641674848021)
                    ·
                      rfl

theorem cell22_530663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_530663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530663 prefixEnd_530663 := by exact prefixLift 530663
  have htrace : WordTrace (prefixWord ++ tailWord_530663) baseStart_530663 baseEnd_530663 := by
    simpa [prefixWord, tailWord_530663, baseEnd_530663] using wordTrace_append hprefix tailTrace_530663
  have hstable : (prefixWord ++ tailWord_530663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530663).length < 2 ^ (prefixWord ++ tailWord_530663).sum := by decide
  have hdescent : baseEnd_530663 < baseStart_530663 := by decide
  rcases family_descends (prefixWord ++ tailWord_530663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530719 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_530719 : Nat := 118140960795 + 530719 * 2 ^ 59
def prefixEnd_530719 : Nat := 4983230072969 + 3 ^ 40 * 530719 * 2
def baseEnd_530719 : Nat := 181675959649076195447849

theorem tailTrace_530719 : CollatzResearch.WordTrace tailWord_530719 prefixEnd_530719 181675959649076195447849 := by
  unfold tailWord_530719
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356912164303177434123211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12904608109535451622748807 19356912164303177434123211)
  ·
    refine ⟨29035368246454766151184817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19356912164303177434123211 29035368246454766151184817)
    ·
      refine ⟨21776526184841074613388613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29035368246454766151184817 21776526184841074613388613)
      ·
        refine ⟨4083098659657701490010365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21776526184841074613388613 4083098659657701490010365)
        ·
          refine ⟨1531161997371638058753887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4083098659657701490010365 1531161997371638058753887)
          ·
            refine ⟨2296742996057457088130831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531161997371638058753887 2296742996057457088130831)
            ·
              refine ⟨3445114494086185632196247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296742996057457088130831 3445114494086185632196247)
              ·
                refine ⟨5167671741129278448294371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445114494086185632196247 5167671741129278448294371)
                ·
                  refine ⟨7751507611693917672441557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5167671741129278448294371 7751507611693917672441557)
                  ·
                    refine ⟨181675959649076195447849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7751507611693917672441557 181675959649076195447849)
                    ·
                      rfl

theorem cell22_530719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_530719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530719 prefixEnd_530719 := by exact prefixLift 530719
  have htrace : WordTrace (prefixWord ++ tailWord_530719) baseStart_530719 baseEnd_530719 := by
    simpa [prefixWord, tailWord_530719, baseEnd_530719] using wordTrace_append hprefix tailTrace_530719
  have hstable : (prefixWord ++ tailWord_530719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530719).length < 2 ^ (prefixWord ++ tailWord_530719).sum := by decide
  have hdescent : baseEnd_530719 < baseStart_530719 := by decide
  rcases family_descends (prefixWord ++ tailWord_530719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530751 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 1, 4]
def baseStart_530751 : Nat := 118140960795 + 530751 * 2 ^ 59
def prefixEnd_530751 : Nat := 4983230072969 + 3 ^ 40 * 530751 * 2
def baseEnd_530751 : Nat := 181686913903038778647751

theorem tailTrace_530751 : CollatzResearch.WordTrace tailWord_530751 prefixEnd_530751 181686913903038778647751 := by
  unfold tailWord_530751
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358079300187246899288107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12905386200124831266192071 19358079300187246899288107)
  ·
    refine ⟨29037118950280870348932161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19358079300187246899288107 29037118950280870348932161)
    ·
      refine ⟨21777839212710652761699121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29037118950280870348932161 21777839212710652761699121)
      ·
        refine ⟨16333379409532989571274341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21777839212710652761699121 16333379409532989571274341)
        ·
          refine ⟨3062508639287435544613939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16333379409532989571274341 3062508639287435544613939)
          ·
            refine ⟨4593762958931153316920909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062508639287435544613939 4593762958931153316920909)
            ·
              refine ⟨1722661109599182493845341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4593762958931153316920909 1722661109599182493845341)
              ·
                refine ⟨645997916099693435192003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722661109599182493845341 645997916099693435192003)
                ·
                  refine ⟨968996874149540152788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645997916099693435192003 968996874149540152788005)
                  ·
                    refine ⟨181686913903038778647751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 968996874149540152788005 181686913903038778647751)
                    ·
                      rfl

theorem cell22_530751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_530751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530751 prefixEnd_530751 := by exact prefixLift 530751
  have htrace : WordTrace (prefixWord ++ tailWord_530751) baseStart_530751 baseEnd_530751 := by
    simpa [prefixWord, tailWord_530751, baseEnd_530751] using wordTrace_append hprefix tailTrace_530751
  have hstable : (prefixWord ++ tailWord_530751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530751).length < 2 ^ (prefixWord ++ tailWord_530751).sum := by decide
  have hdescent : baseEnd_530751 < baseStart_530751 := by decide
  rcases family_descends (prefixWord ++ tailWord_530751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530873 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 5]
def baseStart_530873 : Nat := 118140960795 + 530873 * 2 ^ 59
def prefixEnd_530873 : Nat := 4983230072969 + 3 ^ 40 * 530873 * 2
def baseEnd_530873 : Nat := 60576225665423709032459

theorem tailTrace_530873 : CollatzResearch.WordTrace tailWord_530873 prefixEnd_530873 60576225665423709032459 := by
  unfold tailWord_530873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362529005745261735229273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12908352670496841156819515 19362529005745261735229273)
  ·
    refine ⟨14521896754308946301421955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19362529005745261735229273 14521896754308946301421955)
    ·
      refine ⟨21782845131463419452132933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14521896754308946301421955 21782845131463419452132933)
      ·
        refine ⟨4084283462149391147274925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21782845131463419452132933 4084283462149391147274925)
        ·
          refine ⟨1531606298306021680228097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4084283462149391147274925 1531606298306021680228097)
          ·
            refine ⟨1148704723729516260171073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531606298306021680228097 1148704723729516260171073)
            ·
              refine ⟨861528542797137195128305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148704723729516260171073 861528542797137195128305)
              ·
                refine ⟨646146407097852896346229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861528542797137195128305 646146407097852896346229)
                ·
                  refine ⟨60576225665423709032459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646146407097852896346229 60576225665423709032459)
                  ·
                    rfl

theorem cell22_530873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_530873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530873 prefixEnd_530873 := by exact prefixLift 530873
  have htrace : WordTrace (prefixWord ++ tailWord_530873) baseStart_530873 baseEnd_530873 := by
    simpa [prefixWord, tailWord_530873, baseEnd_530873] using wordTrace_append hprefix tailTrace_530873
  have hstable : (prefixWord ++ tailWord_530873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530873).length < 2 ^ (prefixWord ++ tailWord_530873).sum := by decide
  have hdescent : baseEnd_530873 < baseStart_530873 := by decide
  rcases family_descends (prefixWord ++ tailWord_530873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530877 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_530877 : Nat := 118140960795 + 530877 * 2 ^ 59
def prefixEnd_530877 : Nat := 4983230072969 + 3 ^ 40 * 530877 * 2
def baseEnd_530877 : Nat := 181730046278016449997365

theorem tailTrace_530877 : CollatzResearch.WordTrace tailWord_530877 prefixEnd_530877 181730046278016449997365 := by
  unfold tailWord_530877
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362674897730770418374885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12908449931820513612249923 19362674897730770418374885)
  ·
    refine ⟨3630501543324519453445291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19362674897730770418374885 3630501543324519453445291)
    ·
      refine ⟨5445752314986779180167937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630501543324519453445291 5445752314986779180167937)
      ·
        refine ⟨4084314236240084385125953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5445752314986779180167937 4084314236240084385125953)
        ·
          refine ⟨3063235677180063288844465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084314236240084385125953 3063235677180063288844465)
          ·
            refine ⟨2297426757885047466633349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063235677180063288844465 2297426757885047466633349)
            ·
              refine ⟨430767517103446399993753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2297426757885047466633349 430767517103446399993753)
              ·
                refine ⟨323075637827584799995315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430767517103446399993753 323075637827584799995315)
                ·
                  refine ⟨484613456741377199992973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323075637827584799995315 484613456741377199992973)
                  ·
                    refine ⟨181730046278016449997365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484613456741377199992973 181730046278016449997365)
                    ·
                      rfl

theorem cell22_530877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_530877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530877 prefixEnd_530877 := by exact prefixLift 530877
  have htrace : WordTrace (prefixWord ++ tailWord_530877) baseStart_530877 baseEnd_530877 := by
    simpa [prefixWord, tailWord_530877, baseEnd_530877] using wordTrace_append hprefix tailTrace_530877
  have hstable : (prefixWord ++ tailWord_530877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530877).length < 2 ^ (prefixWord ++ tailWord_530877).sum := by decide
  have hdescent : baseEnd_530877 < baseStart_530877 := by decide
  rcases family_descends (prefixWord ++ tailWord_530877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530901 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 8]
def baseStart_530901 : Nat := 118140960795 + 530901 * 2 ^ 59
def prefixEnd_530901 : Nat := 4983230072969 + 3 ^ 40 * 530901 * 2
def baseEnd_530901 : Nat := 60579420656162795799097

theorem tailTrace_530901 : CollatzResearch.WordTrace tailWord_530901 prefixEnd_530901 60579420656162795799097 := by
  unfold tailWord_530901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19363550249643822517248557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12909033499762548344832371 19363550249643822517248557)
  ·
    refine ⟨7261331343616433443968209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19363550249643822517248557 7261331343616433443968209)
    ·
      refine ⟨5445998507712325082976157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7261331343616433443968209 5445998507712325082976157)
      ·
        refine ⟨2042249440392121906116059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5445998507712325082976157 2042249440392121906116059)
        ·
          refine ⟨3063374160588182859174089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042249440392121906116059 3063374160588182859174089)
          ·
            refine ⟨2297530620441137144380567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063374160588182859174089 2297530620441137144380567)
            ·
              refine ⟨3446295930661705716570851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297530620441137144380567 3446295930661705716570851)
              ·
                refine ⟨5169443895992558574856277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446295930661705716570851 5169443895992558574856277)
                ·
                  refine ⟨60579420656162795799097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5169443895992558574856277 60579420656162795799097)
                  ·
                    rfl

theorem cell22_530901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_530901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530901 prefixEnd_530901 := by exact prefixLift 530901
  have htrace : WordTrace (prefixWord ++ tailWord_530901) baseStart_530901 baseEnd_530901 := by
    simpa [prefixWord, tailWord_530901, baseEnd_530901] using wordTrace_append hprefix tailTrace_530901
  have hstable : (prefixWord ++ tailWord_530901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530901).length < 2 ^ (prefixWord ++ tailWord_530901).sum := by decide
  have hdescent : baseEnd_530901 < baseStart_530901 := by decide
  rcases family_descends (prefixWord ++ tailWord_530901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530920 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_530920 : Nat := 118140960795 + 530920 * 2 ^ 59
def prefixEnd_530920 : Nat := 4983230072969 + 3 ^ 40 * 530920 * 2
def baseEnd_530920 : Nat := 181744766056778671172233

theorem tailTrace_530920 : CollatzResearch.WordTrace tailWord_530920 prefixEnd_530920 181744766056778671172233 := by
  unfold tailWord_530920
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682121618287494381095107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12909495491049992508126809 9682121618287494381095107)
  ·
    refine ⟨14523182427431241571642661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9682121618287494381095107 14523182427431241571642661)
    ·
      refine ⟨2723096705143357794682999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14523182427431241571642661 2723096705143357794682999)
      ·
        refine ⟨4084645057715036692024499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723096705143357794682999 4084645057715036692024499)
        ·
          refine ⟨6126967586572555038036749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084645057715036692024499 6126967586572555038036749)
          ·
            refine ⟨2297612844964708139263781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6126967586572555038036749 2297612844964708139263781)
            ·
              refine ⟨430802408430882776111959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2297612844964708139263781 430802408430882776111959)
              ·
                refine ⟨646203612646324164167939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430802408430882776111959 646203612646324164167939)
                ·
                  refine ⟨969305418969486246251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646203612646324164167939 969305418969486246251909)
                  ·
                    refine ⟨181744766056778671172233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969305418969486246251909 181744766056778671172233)
                    ·
                      rfl

theorem cell22_530920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_530920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530920 prefixEnd_530920 := by exact prefixLift 530920
  have htrace : WordTrace (prefixWord ++ tailWord_530920) baseStart_530920 baseEnd_530920 := by
    simpa [prefixWord, tailWord_530920, baseEnd_530920] using wordTrace_append hprefix tailTrace_530920
  have hstable : (prefixWord ++ tailWord_530920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530920).length < 2 ^ (prefixWord ++ tailWord_530920).sum := by decide
  have hdescent : baseEnd_530920 < baseStart_530920 := by decide
  rcases family_descends (prefixWord ++ tailWord_530920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530931 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_530931 : Nat := 118140960795 + 530931 * 2 ^ 59
def prefixEnd_530931 : Nat := 4983230072969 + 3 ^ 40 * 530931 * 2
def baseEnd_530931 : Nat := 181748531581578309147199

theorem tailTrace_530931 : CollatzResearch.WordTrace tailWord_530931 prefixEnd_530931 181748531581578309147199 := by
  unfold tailWord_530931
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364644439535137640840647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12909762959690091760560431 19364644439535137640840647)
  ·
    refine ⟨29046966659302706461260971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19364644439535137640840647 29046966659302706461260971)
    ·
      refine ⟨43570449988954059691891457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29046966659302706461260971 43570449988954059691891457)
      ·
        refine ⟨32677837491715544768918593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43570449988954059691891457 32677837491715544768918593)
        ·
          refine ⟨24508378118786658576688945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32677837491715544768918593 24508378118786658576688945)
          ·
            refine ⟨18381283589089993932516709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24508378118786658576688945 18381283589089993932516709)
            ·
              refine ⟨3446490672954373862346883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18381283589089993932516709 3446490672954373862346883)
              ·
                refine ⟨5169736009431560793520325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446490672954373862346883 5169736009431560793520325)
                ·
                  refine ⟨969325501768417648785061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5169736009431560793520325 969325501768417648785061)
                  ·
                    refine ⟨181748531581578309147199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969325501768417648785061 181748531581578309147199)
                    ·
                      rfl

theorem cell22_530931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_530931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530931 prefixEnd_530931 := by exact prefixLift 530931
  have htrace : WordTrace (prefixWord ++ tailWord_530931) baseStart_530931 baseEnd_530931 := by
    simpa [prefixWord, tailWord_530931, baseEnd_530931] using wordTrace_append hprefix tailTrace_530931
  have hstable : (prefixWord ++ tailWord_530931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530931).length < 2 ^ (prefixWord ++ tailWord_530931).sum := by decide
  have hdescent : baseEnd_530931 < baseStart_530931 := by decide
  rcases family_descends (prefixWord ++ tailWord_530931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530948 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_530948 : Nat := 118140960795 + 530948 * 2 ^ 59
def prefixEnd_530948 : Nat := 4983230072969 + 3 ^ 40 * 530948 * 2
def baseEnd_530948 : Nat := 181754351028995931472147

theorem tailTrace_530948 : CollatzResearch.WordTrace tailWord_530948 prefixEnd_530948 181754351028995931472147 := by
  unfold tailWord_530948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682632240236774772104749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12910176320315699696139665 9682632240236774772104749)
  ·
    refine ⟨3630987090088790539539281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9682632240236774772104749 3630987090088790539539281)
    ·
      refine ⟨2723240317566592904654461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3630987090088790539539281 2723240317566592904654461)
      ·
        refine ⟨1021215119087472339245423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2723240317566592904654461 1021215119087472339245423)
        ·
          refine ⟨1531822678631208508868135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021215119087472339245423 1531822678631208508868135)
          ·
            refine ⟨2297734017946812763302203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531822678631208508868135 2297734017946812763302203)
            ·
              refine ⟨3446601026920219144953305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297734017946812763302203 3446601026920219144953305)
              ·
                refine ⟨2584950770190164358714979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446601026920219144953305 2584950770190164358714979)
                ·
                  refine ⟨3877426155285246538072469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584950770190164358714979 3877426155285246538072469)
                  ·
                    refine ⟨181754351028995931472147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3877426155285246538072469 181754351028995931472147)
                    ·
                      rfl

theorem cell22_530948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_530948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530948 prefixEnd_530948 := by exact prefixLift 530948
  have htrace : WordTrace (prefixWord ++ tailWord_530948) baseStart_530948 baseEnd_530948 := by
    simpa [prefixWord, tailWord_530948, baseEnd_530948] using wordTrace_append hprefix tailTrace_530948
  have hstable : (prefixWord ++ tailWord_530948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530948).length < 2 ^ (prefixWord ++ tailWord_530948).sum := by decide
  have hdescent : baseEnd_530948 < baseStart_530948 := by decide
  rcases family_descends (prefixWord ++ tailWord_530948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530980 : List Nat := [2, 3, 1, 5, 1, 2, 8]
def baseStart_530980 : Nat := 118140960795 + 530980 * 2 ^ 59
def prefixEnd_530980 : Nat := 4983230072969 + 3 ^ 40 * 530980 * 2
def baseEnd_530980 : Nat := 6732048343813278321187

theorem tailTrace_530980 : CollatzResearch.WordTrace tailWord_530980 prefixEnd_530980 6732048343813278321187 := by
  unfold tailWord_530980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9683215808178809504687197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12910954410905079339582929 9683215808178809504687197)
  ·
    refine ⟨3631205928067053564257699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9683215808178809504687197 3631205928067053564257699)
    ·
      refine ⟨5446808892100580346386549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631205928067053564257699 5446808892100580346386549)
      ·
        refine ⟨510638333634429407473739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5446808892100580346386549 510638333634429407473739)
        ·
          refine ⟨765957500451644111210609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510638333634429407473739 765957500451644111210609)
          ·
            refine ⟨574468125338733083407957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765957500451644111210609 574468125338733083407957)
            ·
              refine ⟨6732048343813278321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 574468125338733083407957 6732048343813278321187)
              ·
                rfl

theorem cell22_530980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 8].length) (baseStart_530980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_530980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_530980 prefixEnd_530980 := by exact prefixLift 530980
  have htrace : WordTrace (prefixWord ++ tailWord_530980) baseStart_530980 baseEnd_530980 := by
    simpa [prefixWord, tailWord_530980, baseEnd_530980] using wordTrace_append hprefix tailTrace_530980
  have hstable : (prefixWord ++ tailWord_530980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530980).length < 2 ^ (prefixWord ++ tailWord_530980).sum := by decide
  have hdescent : baseEnd_530980 < baseStart_530980 := by decide
  rcases family_descends (prefixWord ++ tailWord_530980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531068 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_531068 : Nat := 118140960795 + 531068 * 2 ^ 59
def prefixEnd_531068 : Nat := 4983230072969 + 3 ^ 40 * 531068 * 2
def baseEnd_531068 : Nat := 181795429481355618471779

theorem tailTrace_531068 : CollatzResearch.WordTrace tailWord_531068 prefixEnd_531068 181795429481355618471779 := by
  unfold tailWord_531068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684820620019405019288929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12913094160025873359051905 9684820620019405019288929)
  ·
    refine ⟨7263615465014553764466697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9684820620019405019288929 7263615465014553764466697)
    ·
      refine ⟨5447711598760915323350023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7263615465014553764466697 5447711598760915323350023)
      ·
        refine ⟨8171567398141372985025035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447711598760915323350023 8171567398141372985025035)
        ·
          refine ⟨12257351097212059477537553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171567398141372985025035 12257351097212059477537553)
          ·
            refine ⟨9193013322909044608153165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12257351097212059477537553 9193013322909044608153165)
            ·
              refine ⟨3447379996090891728057437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9193013322909044608153165 3447379996090891728057437)
              ·
                refine ⟨1292767498534084398021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447379996090891728057437 1292767498534084398021539)
                ·
                  refine ⟨1939151247801126597032309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292767498534084398021539 1939151247801126597032309)
                  ·
                    refine ⟨181795429481355618471779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939151247801126597032309 181795429481355618471779)
                    ·
                      rfl

theorem cell22_531068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_531068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531068 prefixEnd_531068 := by exact prefixLift 531068
  have htrace : WordTrace (prefixWord ++ tailWord_531068) baseStart_531068 baseEnd_531068 := by
    simpa [prefixWord, tailWord_531068, baseEnd_531068] using wordTrace_append hprefix tailTrace_531068
  have hstable : (prefixWord ++ tailWord_531068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531068).length < 2 ^ (prefixWord ++ tailWord_531068).sum := by decide
  have hdescent : baseEnd_531068 < baseStart_531068 := by decide
  rcases family_descends (prefixWord ++ tailWord_531068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531083 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_531083 : Nat := 118140960795 + 531083 * 2 ^ 59
def prefixEnd_531083 : Nat := 4983230072969 + 3 ^ 40 * 531083 * 2
def baseEnd_531083 : Nat := 181800564287900579346733

theorem tailTrace_531083 : CollatzResearch.WordTrace tailWord_531083 prefixEnd_531083 181800564287900579346733 := by
  unfold tailWord_531083
  simp only [CollatzResearch.WordTrace]
  refine ⟨19370188334984467600373903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12913458889989645066915935 19370188334984467600373903)
  ·
    refine ⟨29055282502476701400560855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19370188334984467600373903 29055282502476701400560855)
    ·
      refine ⟨43582923753715052100841283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29055282502476701400560855 43582923753715052100841283)
      ·
        refine ⟨65374385630572578151261925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43582923753715052100841283 65374385630572578151261925)
        ·
          refine ⟨12257697305732358403361611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65374385630572578151261925 12257697305732358403361611)
          ·
            refine ⟨18386545958598537605042417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257697305732358403361611 18386545958598537605042417)
            ·
              refine ⟨13789909468948903203781813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18386545958598537605042417 13789909468948903203781813)
              ·
                refine ⟨1292804012713959675354545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13789909468948903203781813 1292804012713959675354545)
                ·
                  refine ⟨969603009535469756515909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292804012713959675354545 969603009535469756515909)
                  ·
                    refine ⟨181800564287900579346733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969603009535469756515909 181800564287900579346733)
                    ·
                      rfl

theorem cell22_531083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_531083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531083 prefixEnd_531083 := by exact prefixLift 531083
  have htrace : WordTrace (prefixWord ++ tailWord_531083) baseStart_531083 baseEnd_531083 := by
    simpa [prefixWord, tailWord_531083, baseEnd_531083] using wordTrace_append hprefix tailTrace_531083
  have hstable : (prefixWord ++ tailWord_531083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531083).length < 2 ^ (prefixWord ++ tailWord_531083).sum := by decide
  have hdescent : baseEnd_531083 < baseStart_531083 := by decide
  rcases family_descends (prefixWord ++ tailWord_531083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531102 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_531102 : Nat := 118140960795 + 531102 * 2 ^ 59
def prefixEnd_531102 : Nat := 4983230072969 + 3 ^ 40 * 531102 * 2
def baseEnd_531102 : Nat := 181807068376190863121675

theorem tailTrace_531102 : CollatzResearch.WordTrace tailWord_531102 prefixEnd_531102 181807068376190863121675 := by
  unfold tailWord_531102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421360165239454230664445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12913920881277089230210373 2421360165239454230664445)
  ·
    refine ⟨908010061964795336499167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2421360165239454230664445 908010061964795336499167)
    ·
      refine ⟨1362015092947193004748751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908010061964795336499167 1362015092947193004748751)
      ·
        refine ⟨2043022639420789507123127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362015092947193004748751 2043022639420789507123127)
        ·
          refine ⟨3064533959131184260684691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043022639420789507123127 3064533959131184260684691)
          ·
            refine ⟨4596800938696776391027037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064533959131184260684691 4596800938696776391027037)
            ·
              refine ⟨1723800352011291146635139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4596800938696776391027037 1723800352011291146635139)
              ·
                refine ⟨2585700528016936719952709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723800352011291146635139 2585700528016936719952709)
                ·
                  refine ⟨484818849003175634991133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2585700528016936719952709 484818849003175634991133)
                  ·
                    refine ⟨181807068376190863121675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484818849003175634991133 181807068376190863121675)
                    ·
                      rfl

theorem cell22_531102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_531102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531102 prefixEnd_531102 := by exact prefixLift 531102
  have htrace : WordTrace (prefixWord ++ tailWord_531102) baseStart_531102 baseEnd_531102 := by
    simpa [prefixWord, tailWord_531102, baseEnd_531102] using wordTrace_append hprefix tailTrace_531102
  have hstable : (prefixWord ++ tailWord_531102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531102).length < 2 ^ (prefixWord ++ tailWord_531102).sum := by decide
  have hdescent : baseEnd_531102 < baseStart_531102 := by decide
  rcases family_descends (prefixWord ++ tailWord_531102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531130 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_531130 : Nat := 118140960795 + 531130 * 2 ^ 59
def prefixEnd_531130 : Nat := 4983230072969 + 3 ^ 40 * 531130 * 2
def baseEnd_531130 : Nat := 181816653348408123421589

theorem tailTrace_531130 : CollatzResearch.WordTrace tailWord_531130 prefixEnd_531130 181816653348408123421589 := by
  unfold tailWord_531130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842975641453548656833711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12914601710542796418223229 4842975641453548656833711)
  ·
    refine ⟨7264463462180322985250567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842975641453548656833711 7264463462180322985250567)
    ·
      refine ⟨10896695193270484477875851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7264463462180322985250567 10896695193270484477875851)
      ·
        refine ⟨16345042789905726716813777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10896695193270484477875851 16345042789905726716813777)
        ·
          refine ⟨12258782092429295037610333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16345042789905726716813777 12258782092429295037610333)
          ·
            refine ⟨4597043284660985639103875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12258782092429295037610333 4597043284660985639103875)
            ·
              refine ⟨6895564926991478458655813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597043284660985639103875 6895564926991478458655813)
              ·
                refine ⟨1292918423810902210997965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6895564926991478458655813 1292918423810902210997965)
                ·
                  refine ⟨484844408929088329124237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1292918423810902210997965 484844408929088329124237)
                  ·
                    refine ⟨181816653348408123421589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484844408929088329124237 181816653348408123421589)
                    ·
                      rfl

theorem cell22_531130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_531130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531130 prefixEnd_531130 := by exact prefixLift 531130
  have htrace : WordTrace (prefixWord ++ tailWord_531130) baseStart_531130 baseEnd_531130 := by
    simpa [prefixWord, tailWord_531130, baseEnd_531130] using wordTrace_append hprefix tailTrace_531130
  have hstable : (prefixWord ++ tailWord_531130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531130).length < 2 ^ (prefixWord ++ tailWord_531130).sum := by decide
  have hdescent : baseEnd_531130 < baseStart_531130 := by decide
  rcases family_descends (prefixWord ++ tailWord_531130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531149 : List Nat := [1, 6, 2, 1, 3, 1, 8]
def baseStart_531149 : Nat := 118140960795 + 531149 * 2 ^ 59
def prefixEnd_531149 : Nat := 4983230072969 + 3 ^ 40 * 531149 * 2
def baseEnd_531149 : Nat := 6734191016174015081353

theorem tailTrace_531149 : CollatzResearch.WordTrace tailWord_531149 prefixEnd_531149 6734191016174015081353 := by
  unfold tailWord_531149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19372595552745360872276501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12915063701830240581517667 19372595552745360872276501)
  ·
    refine ⟨908090416534938790887961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19372595552745360872276501 908090416534938790887961)
    ·
      refine ⟨681067812401204093165971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908090416534938790887961 681067812401204093165971)
      ·
        refine ⟨1021601718601806139748957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681067812401204093165971 1021601718601806139748957)
        ·
          refine ⟨383100644475677302405859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1021601718601806139748957 383100644475677302405859)
          ·
            refine ⟨574650966713515953608789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383100644475677302405859 574650966713515953608789)
            ·
              refine ⟨6734191016174015081353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 574650966713515953608789 6734191016174015081353)
              ·
                rfl

theorem cell22_531149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 8].length) (baseStart_531149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531149 prefixEnd_531149 := by exact prefixLift 531149
  have htrace : WordTrace (prefixWord ++ tailWord_531149) baseStart_531149 baseEnd_531149 := by
    simpa [prefixWord, tailWord_531149, baseEnd_531149] using wordTrace_append hprefix tailTrace_531149
  have hstable : (prefixWord ++ tailWord_531149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531149).length < 2 ^ (prefixWord ++ tailWord_531149).sum := by decide
  have hdescent : baseEnd_531149 < baseStart_531149 := by decide
  rcases family_descends (prefixWord ++ tailWord_531149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531164 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_531164 : Nat := 118140960795 + 531164 * 2 ^ 59
def prefixEnd_531164 : Nat := 4983230072969 + 3 ^ 40 * 531164 * 2
def baseEnd_531164 : Nat := 181828292243243368071485

theorem tailTrace_531164 : CollatzResearch.WordTrace tailWord_531164 prefixEnd_531164 181828292243243368071485 := by
  unfold tailWord_531164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686571323845509217036273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12915428431794012289381697 9686571323845509217036273)
  ·
    refine ⟨7264928492884131912777205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9686571323845509217036273 7264928492884131912777205)
    ·
      refine ⟨681087046207887366822863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7264928492884131912777205 681087046207887366822863)
      ·
        refine ⟨1021630569311831050234295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681087046207887366822863 1021630569311831050234295)
        ·
          refine ⟨1532445853967746575351443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021630569311831050234295 1532445853967746575351443)
          ·
            refine ⟨2298668780951619863027165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532445853967746575351443 2298668780951619863027165)
            ·
              refine ⟨862000792856857448635187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2298668780951619863027165 862000792856857448635187)
              ·
                refine ⟨1293001189285286172952781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862000792856857448635187 1293001189285286172952781)
                ·
                  refine ⟨484875445981982314857293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1293001189285286172952781 484875445981982314857293)
                  ·
                    refine ⟨181828292243243368071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484875445981982314857293 181828292243243368071485)
                    ·
                      rfl

theorem cell22_531164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_531164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531164 prefixEnd_531164 := by exact prefixLift 531164
  have htrace : WordTrace (prefixWord ++ tailWord_531164) baseStart_531164 baseEnd_531164 := by
    simpa [prefixWord, tailWord_531164, baseEnd_531164] using wordTrace_append hprefix tailTrace_531164
  have hstable : (prefixWord ++ tailWord_531164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531164).length < 2 ^ (prefixWord ++ tailWord_531164).sum := by decide
  have hdescent : baseEnd_531164 < baseStart_531164 := by decide
  rcases family_descends (prefixWord ++ tailWord_531164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531237 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_531237 : Nat := 118140960795 + 531237 * 2 ^ 59
def prefixEnd_531237 : Nat := 4983230072969 + 3 ^ 40 * 531237 * 2
def baseEnd_531237 : Nat := 181853281635095510996261

theorem tailTrace_531237 : CollatzResearch.WordTrace tailWord_531237 prefixEnd_531237 181853281635095510996261 := by
  unfold tailWord_531237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19375805176426551901479965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12917203450951034600986643 19375805176426551901479965)
  ·
    refine ⟨7265926941159956963054987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19375805176426551901479965 7265926941159956963054987)
    ·
      refine ⟨10898890411739935444582481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7265926941159956963054987 10898890411739935444582481)
      ·
        refine ⟨8174167808804951583436861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10898890411739935444582481 8174167808804951583436861)
        ·
          refine ⟨3065312928301856843788823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8174167808804951583436861 3065312928301856843788823)
          ·
            refine ⟨4597969392452785265683235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065312928301856843788823 4597969392452785265683235)
            ·
              refine ⟨6896954088679177898524853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597969392452785265683235 6896954088679177898524853)
              ·
                refine ⟨646589445813672927986705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6896954088679177898524853 646589445813672927986705)
                ·
                  refine ⟨484942084360254695990029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646589445813672927986705 484942084360254695990029)
                  ·
                    refine ⟨181853281635095510996261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484942084360254695990029 181853281635095510996261)
                    ·
                      rfl

theorem cell22_531237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_531237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531237 prefixEnd_531237 := by exact prefixLift 531237
  have htrace : WordTrace (prefixWord ++ tailWord_531237) baseStart_531237 baseEnd_531237 := by
    simpa [prefixWord, tailWord_531237, baseEnd_531237] using wordTrace_append hprefix tailTrace_531237
  have hstable : (prefixWord ++ tailWord_531237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531237).length < 2 ^ (prefixWord ++ tailWord_531237).sum := by decide
  have hdescent : baseEnd_531237 < baseStart_531237 := by decide
  rcases family_descends (prefixWord ++ tailWord_531237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531359 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 1, 4]
def baseStart_531359 : Nat := 118140960795 + 531359 * 2 ^ 59
def prefixEnd_531359 : Nat := 4983230072969 + 3 ^ 40 * 531359 * 2
def baseEnd_531359 : Nat := 181895044728327859445887

theorem tailTrace_531359 : CollatzResearch.WordTrace tailWord_531359 prefixEnd_531359 181895044728327859445887 := by
  unfold tailWord_531359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19380254881984566737421131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12920169921323044491614087 19380254881984566737421131)
  ·
    refine ⟨29070382322976850106131697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19380254881984566737421131 29070382322976850106131697)
    ·
      refine ⟨21802786742232637579598773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29070382322976850106131697 21802786742232637579598773)
      ·
        refine ⟨2044011257084309773087385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21802786742232637579598773 2044011257084309773087385)
        ·
          refine ⟨1533008442813232329815539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044011257084309773087385 1533008442813232329815539)
          ·
            refine ⟨2299512664219848494723309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533008442813232329815539 2299512664219848494723309)
            ·
              refine ⟨862317249082443185521241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2299512664219848494723309 862317249082443185521241)
              ·
                refine ⟨646737936811832389140931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862317249082443185521241 646737936811832389140931)
                ·
                  refine ⟨970106905217748583711397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646737936811832389140931 970106905217748583711397)
                  ·
                    refine ⟨181895044728327859445887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970106905217748583711397 181895044728327859445887)
                    ·
                      rfl

theorem cell22_531359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_531359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531359 prefixEnd_531359 := by exact prefixLift 531359
  have htrace : WordTrace (prefixWord ++ tailWord_531359) baseStart_531359 baseEnd_531359 := by
    simpa [prefixWord, tailWord_531359, baseEnd_531359] using wordTrace_append hprefix tailTrace_531359
  have hstable : (prefixWord ++ tailWord_531359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531359).length < 2 ^ (prefixWord ++ tailWord_531359).sum := by decide
  have hdescent : baseEnd_531359 < baseStart_531359 := by decide
  rcases family_descends (prefixWord ++ tailWord_531359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531385 : List Nat := [1, 2, 1, 4, 2, 12]
def baseStart_531385 : Nat := 118140960795 + 531385 * 2 ^ 59
def prefixEnd_531385 : Nat := 4983230072969 + 3 ^ 40 * 531385 * 2
def baseEnd_531385 : Nat := 2245727716786079732047

theorem tailTrace_531385 : CollatzResearch.WordTrace tailWord_531385 prefixEnd_531385 2245727716786079732047 := by
  unfold tailWord_531385
  simp only [CollatzResearch.WordTrace]
  refine ⟨19381203179890373177867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12920802119926915451911739 19381203179890373177867609)
  ·
    refine ⟨14535902384917779883400707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19381203179890373177867609 14535902384917779883400707)
    ·
      refine ⟨21803853577376669825101061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14535902384917779883400707 21803853577376669825101061)
      ·
        refine ⟨4088222545758125592206449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21803853577376669825101061 4088222545758125592206449)
        ·
          refine ⟨3066166909318594194154837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4088222545758125592206449 3066166909318594194154837)
          ·
            refine ⟨2245727716786079732047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3066166909318594194154837 2245727716786079732047)
            ·
              rfl

theorem cell22_531385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 12].length) (baseStart_531385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531385 prefixEnd_531385 := by exact prefixLift 531385
  have htrace : WordTrace (prefixWord ++ tailWord_531385) baseStart_531385 baseEnd_531385 := by
    simpa [prefixWord, tailWord_531385, baseEnd_531385] using wordTrace_append hprefix tailTrace_531385
  have hstable : (prefixWord ++ tailWord_531385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531385).length < 2 ^ (prefixWord ++ tailWord_531385).sum := by decide
  have hdescent : baseEnd_531385 < baseStart_531385 := by decide
  rcases family_descends (prefixWord ++ tailWord_531385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531421 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_531421 : Nat := 118140960795 + 531421 * 2 ^ 59
def prefixEnd_531421 : Nat := 4983230072969 + 3 ^ 40 * 531421 * 2
def baseEnd_531421 : Nat := 181916268595380364395697

theorem tailTrace_531421 : CollatzResearch.WordTrace tailWord_531421 prefixEnd_531421 181916268595380364395697 := by
  unfold tailWord_531421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19382516207759951326178117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12921677471839967550785411 19382516207759951326178117)
  ·
    refine ⟨3634221788954990873658397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19382516207759951326178117 3634221788954990873658397)
    ·
      refine ⟨1362833170858121577621899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3634221788954990873658397 1362833170858121577621899)
      ·
        refine ⟨2044249756287182366432849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362833170858121577621899 2044249756287182366432849)
        ·
          refine ⟨1533187317215386774824637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044249756287182366432849 1533187317215386774824637)
          ·
            refine ⟨574945243955770040559239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1533187317215386774824637 574945243955770040559239)
            ·
              refine ⟨862417865933655060838859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574945243955770040559239 862417865933655060838859)
              ·
                refine ⟨1293626798900482591258289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862417865933655060838859 1293626798900482591258289)
                ·
                  refine ⟨970220099175361943443717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293626798900482591258289 970220099175361943443717)
                  ·
                    refine ⟨181916268595380364395697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970220099175361943443717 181916268595380364395697)
                    ·
                      rfl

theorem cell22_531421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_531421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531421 prefixEnd_531421 := by exact prefixLift 531421
  have htrace : WordTrace (prefixWord ++ tailWord_531421) baseStart_531421 baseEnd_531421 := by
    simpa [prefixWord, tailWord_531421, baseEnd_531421] using wordTrace_append hprefix tailTrace_531421
  have hstable : (prefixWord ++ tailWord_531421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531421).length < 2 ^ (prefixWord ++ tailWord_531421).sum := by decide
  have hdescent : baseEnd_531421 < baseStart_531421 := by decide
  rcases family_descends (prefixWord ++ tailWord_531421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531485 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_531485 : Nat := 118140960795 + 531485 * 2 ^ 59
def prefixEnd_531485 : Nat := 4983230072969 + 3 ^ 40 * 531485 * 2
def baseEnd_531485 : Nat := 181938177103305530795501

theorem tailTrace_531485 : CollatzResearch.WordTrace tailWord_531485 prefixEnd_531485 181938177103305530795501 := by
  unfold tailWord_531485
  simp only [CollatzResearch.WordTrace]
  refine ⟨19384850479528090256507909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12923233653018726837671939 19384850479528090256507909)
  ·
    refine ⟨3634659464911516923095233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19384850479528090256507909 3634659464911516923095233)
    ·
      refine ⟨2725994598683637692321425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3634659464911516923095233 2725994598683637692321425)
      ·
        refine ⟨2044495949012728269241069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2725994598683637692321425 2044495949012728269241069)
        ·
          refine ⟨766685980879773100965401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2044495949012728269241069 766685980879773100965401)
          ·
            refine ⟨575014485659829825724051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766685980879773100965401 575014485659829825724051)
            ·
              refine ⟨862521728489744738586077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575014485659829825724051 862521728489744738586077)
              ·
                refine ⟨323445648183654276969779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862521728489744738586077 323445648183654276969779)
                ·
                  refine ⟨485168472275481415454669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323445648183654276969779 485168472275481415454669)
                  ·
                    refine ⟨181938177103305530795501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485168472275481415454669 181938177103305530795501)
                    ·
                      rfl

theorem cell22_531485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_531485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531485 prefixEnd_531485 := by exact prefixLift 531485
  have htrace : WordTrace (prefixWord ++ tailWord_531485) baseStart_531485 baseEnd_531485 := by
    simpa [prefixWord, tailWord_531485, baseEnd_531485] using wordTrace_append hprefix tailTrace_531485
  have hstable : (prefixWord ++ tailWord_531485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531485).length < 2 ^ (prefixWord ++ tailWord_531485).sum := by decide
  have hdescent : baseEnd_531485 < baseStart_531485 := by decide
  rcases family_descends (prefixWord ++ tailWord_531485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531537 : List Nat := [1, 2, 2, 1, 3, 1, 4, 8]
def baseStart_531537 : Nat := 118140960795 + 531537 * 2 ^ 59
def prefixEnd_531537 : Nat := 4983230072969 + 3 ^ 40 * 531537 * 2
def baseEnd_531537 : Nat := 20217330862888303166149

theorem tailTrace_531537 : CollatzResearch.WordTrace tailWord_531537 prefixEnd_531537 20217330862888303166149 := by
  unfold tailWord_531537
  simp only [CollatzResearch.WordTrace]
  refine ⟨19386747075339703137400865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12924498050226468758267243 19386747075339703137400865)
  ·
    refine ⟨14540060306504777353050649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19386747075339703137400865 14540060306504777353050649)
    ·
      refine ⟨10905045229878583014787987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14540060306504777353050649 10905045229878583014787987)
      ·
        refine ⟨16357567844817874522181981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10905045229878583014787987 16357567844817874522181981)
        ·
          refine ⟨6134087941806702945818243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16357567844817874522181981 6134087941806702945818243)
          ·
            refine ⟨9201131912710054418727365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134087941806702945818243 9201131912710054418727365)
            ·
              refine ⟨1725212233633135203511381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9201131912710054418727365 1725212233633135203511381)
              ·
                refine ⟨20217330862888303166149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1725212233633135203511381 20217330862888303166149)
                ·
                  rfl

theorem cell22_531537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 8].length) (baseStart_531537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531537 prefixEnd_531537 := by exact prefixLift 531537
  have htrace : WordTrace (prefixWord ++ tailWord_531537) baseStart_531537 baseEnd_531537 := by
    simpa [prefixWord, tailWord_531537, baseEnd_531537] using wordTrace_append hprefix tailTrace_531537
  have hstable : (prefixWord ++ tailWord_531537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531537).length < 2 ^ (prefixWord ++ tailWord_531537).sum := by decide
  have hdescent : baseEnd_531537 < baseStart_531537 := by decide
  rcases family_descends (prefixWord ++ tailWord_531537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531554 : List Nat := [3, 3, 2, 2, 1, 11]
def baseStart_531554 : Nat := 118140960795 + 531554 * 2 ^ 59
def prefixEnd_531554 : Nat := 4983230072969 + 3 ^ 40 * 531554 * 2
def baseEnd_531554 : Nat := 2246441940906325318769

theorem tailTrace_531554 : CollatzResearch.WordTrace tailWord_531554 prefixEnd_531554 2246441940906325318769 := by
  unfold tailWord_531554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846841779069528760192429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12924911410852076693846477 4846841779069528760192429)
  ·
    refine ⟨1817565667151073285072161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4846841779069528760192429 1817565667151073285072161)
    ·
      refine ⟨1363174250363304963804121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1817565667151073285072161 1363174250363304963804121)
      ·
        refine ⟨1022380687772478722853091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1363174250363304963804121 1022380687772478722853091)
        ·
          refine ⟨1533571031658718084279637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022380687772478722853091 1533571031658718084279637)
          ·
            refine ⟨2246441940906325318769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1533571031658718084279637 2246441940906325318769)
            ·
              rfl

theorem cell22_531554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 11].length) (baseStart_531554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531554 prefixEnd_531554 := by exact prefixLift 531554
  have htrace : WordTrace (prefixWord ++ tailWord_531554) baseStart_531554 baseEnd_531554 := by
    simpa [prefixWord, tailWord_531554, baseEnd_531554] using wordTrace_append hprefix tailTrace_531554
  have hstable : (prefixWord ++ tailWord_531554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531554).length < 2 ^ (prefixWord ++ tailWord_531554).sum := by decide
  have hdescent : baseEnd_531554 < baseStart_531554 := by decide
  rcases family_descends (prefixWord ++ tailWord_531554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531567 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_531567 : Nat := 118140960795 + 531567 * 2 ^ 59
def prefixEnd_531567 : Nat := 4983230072969 + 3 ^ 40 * 531567 * 2
def baseEnd_531567 : Nat := 181966247379084650245249

theorem tailTrace_531567 : CollatzResearch.WordTrace tailWord_531567 prefixEnd_531567 181966247379084650245249 := by
  unfold tailWord_531567
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387841265231018260992955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925227510154012173995303 19387841265231018260992955)
  ·
    refine ⟨29081761897846527391489433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19387841265231018260992955 29081761897846527391489433)
    ·
      refine ⟨21811321423384895543617075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29081761897846527391489433 21811321423384895543617075)
      ·
        refine ⟨32716982135077343315425613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21811321423384895543617075 32716982135077343315425613)
        ·
          refine ⟨12268868300654003743284605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32716982135077343315425613 12268868300654003743284605)
          ·
            refine ⟨4600825612745251403731727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12268868300654003743284605 4600825612745251403731727)
            ·
              refine ⟨6901238419117877105597591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600825612745251403731727 6901238419117877105597591)
              ·
                refine ⟨10351857628676815658396387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901238419117877105597591 10351857628676815658396387)
                ·
                  refine ⟨15527786443015223487594581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10351857628676815658396387 15527786443015223487594581)
                  ·
                    refine ⟨181966247379084650245249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15527786443015223487594581 181966247379084650245249)
                    ·
                      rfl

theorem cell22_531567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_531567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531567 prefixEnd_531567 := by exact prefixLift 531567
  have htrace : WordTrace (prefixWord ++ tailWord_531567) baseStart_531567 baseEnd_531567 := by
    simpa [prefixWord, tailWord_531567, baseEnd_531567] using wordTrace_append hprefix tailTrace_531567
  have hstable : (prefixWord ++ tailWord_531567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531567).length < 2 ^ (prefixWord ++ tailWord_531567).sum := by decide
  have hdescent : baseEnd_531567 < baseStart_531567 := by decide
  rcases family_descends (prefixWord ++ tailWord_531567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531633 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 5]
def baseStart_531633 : Nat := 118140960795 + 531633 * 2 ^ 59
def prefixEnd_531633 : Nat := 4983230072969 + 3 ^ 40 * 531633 * 2
def baseEnd_531633 : Nat := 60662946842627492698349

theorem tailTrace_531633 : CollatzResearch.WordTrace tailWord_531633 prefixEnd_531633 60662946842627492698349 := by
  unfold tailWord_531633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19390248482991911532895553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12926832321994607688597035 19390248482991911532895553)
  ·
    refine ⟨14542686362243933649671665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19390248482991911532895553 14542686362243933649671665)
    ·
      refine ⟨10907014771682950237253749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14542686362243933649671665 10907014771682950237253749)
      ·
        refine ⟨1022532634845276584742539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10907014771682950237253749 1022532634845276584742539)
        ·
          refine ⟨1533798952267914877113809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022532634845276584742539 1533798952267914877113809)
          ·
            refine ⟨1150349214200936157835357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533798952267914877113809 1150349214200936157835357)
            ·
              refine ⟨431380955325351059188259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150349214200936157835357 431380955325351059188259)
              ·
                refine ⟨647071432988026588782389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431380955325351059188259 647071432988026588782389)
                ·
                  refine ⟨60662946842627492698349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 647071432988026588782389 60662946842627492698349)
                  ·
                    rfl

theorem cell22_531633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_531633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531633 prefixEnd_531633 := by exact prefixLift 531633
  have htrace : WordTrace (prefixWord ++ tailWord_531633) baseStart_531633 baseEnd_531633 := by
    simpa [prefixWord, tailWord_531633, baseEnd_531633] using wordTrace_append hprefix tailTrace_531633
  have hstable : (prefixWord ++ tailWord_531633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531633).length < 2 ^ (prefixWord ++ tailWord_531633).sum := by decide
  have hdescent : baseEnd_531633 < baseStart_531633 := by decide
  rcases family_descends (prefixWord ++ tailWord_531633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531708 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_531708 : Nat := 118140960795 + 531708 * 2 ^ 59
def prefixEnd_531708 : Nat := 4983230072969 + 3 ^ 40 * 531708 * 2
def baseEnd_531708 : Nat := 182014514560607282469817

theorem tailTrace_531708 : CollatzResearch.WordTrace tailWord_531708 prefixEnd_531708 182014514560607282469817 := by
  unfold tailWord_531708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696491978860099670937889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12928655971813466227917185 9696491978860099670937889)
  ·
    refine ⟨7272368984145074753203417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9696491978860099670937889 7272368984145074753203417)
    ·
      refine ⟨5454276738108806064902563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7272368984145074753203417 5454276738108806064902563)
      ·
        refine ⟨8181415107163209097353845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454276738108806064902563 8181415107163209097353845)
        ·
          refine ⟨767007666296550852876923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8181415107163209097353845 767007666296550852876923)
          ·
            refine ⟨1150511499444826279315385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767007666296550852876923 1150511499444826279315385)
            ·
              refine ⟨862883624583619709486539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150511499444826279315385 862883624583619709486539)
              ·
                refine ⟨1294325436875429564229809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862883624583619709486539 1294325436875429564229809)
                ·
                  refine ⟨970744077656572173172357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294325436875429564229809 970744077656572173172357)
                  ·
                    refine ⟨182014514560607282469817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970744077656572173172357 182014514560607282469817)
                    ·
                      rfl

theorem cell22_531708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_531708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531708 prefixEnd_531708 := by exact prefixLift 531708
  have htrace : WordTrace (prefixWord ++ tailWord_531708) baseStart_531708 baseEnd_531708 := by
    simpa [prefixWord, tailWord_531708, baseEnd_531708] using wordTrace_append hprefix tailTrace_531708
  have hstable : (prefixWord ++ tailWord_531708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531708).length < 2 ^ (prefixWord ++ tailWord_531708).sum := by decide
  have hdescent : baseEnd_531708 < baseStart_531708 := by decide
  rcases family_descends (prefixWord ++ tailWord_531708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531779 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 10]
def baseStart_531779 : Nat := 118140960795 + 531779 * 2 ^ 59
def prefixEnd_531779 : Nat := 4983230072969 + 3 ^ 40 * 531779 * 2
def baseEnd_531779 : Nat := 60679606437195587981533

theorem tailTrace_531779 : CollatzResearch.WordTrace tailWord_531779 prefixEnd_531779 60679606437195587981533 := by
  unfold tailWord_531779
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395573540462978467710391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12930382360308652311806927 19395573540462978467710391)
  ·
    refine ⟨29093360310694467701565587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19395573540462978467710391 29093360310694467701565587)
    ·
      refine ⟨43640040466041701552348381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29093360310694467701565587 43640040466041701552348381)
      ·
        refine ⟨16365015174765638082130643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43640040466041701552348381 16365015174765638082130643)
        ·
          refine ⟨24547522762148457123195965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16365015174765638082130643 24547522762148457123195965)
          ·
            refine ⟨9205321035805671421198487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24547522762148457123195965 9205321035805671421198487)
            ·
              refine ⟨13807981553708507131797731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9205321035805671421198487 13807981553708507131797731)
              ·
                refine ⟨20711972330562760697696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13807981553708507131797731 20711972330562760697696597)
                ·
                  refine ⟨60679606437195587981533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20711972330562760697696597 60679606437195587981533)
                  ·
                    rfl

theorem cell22_531779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_531779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531779 prefixEnd_531779 := by exact prefixLift 531779
  have htrace : WordTrace (prefixWord ++ tailWord_531779) baseStart_531779 baseEnd_531779 := by
    simpa [prefixWord, tailWord_531779, baseEnd_531779] using wordTrace_append hprefix tailTrace_531779
  have hstable : (prefixWord ++ tailWord_531779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531779).length < 2 ^ (prefixWord ++ tailWord_531779).sum := by decide
  have hdescent : baseEnd_531779 < baseStart_531779 := by decide
  rcases family_descends (prefixWord ++ tailWord_531779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531815 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 1, 4]
def baseStart_531815 : Nat := 118140960795 + 531815 * 2 ^ 59
def prefixEnd_531815 : Nat := 4983230072969 + 3 ^ 40 * 531815 * 2
def baseEnd_531815 : Nat := 182051142847294670044489

theorem tailTrace_531815 : CollatzResearch.WordTrace tailWord_531815 prefixEnd_531815 182051142847294670044489 := by
  unfold tailWord_531815
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396886568332556616020899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12931257712221704410680599 19396886568332556616020899)
  ·
    refine ⟨29095329852498834924031349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19396886568332556616020899 29095329852498834924031349)
    ·
      refine ⟨2727687173671765774127939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29095329852498834924031349 2727687173671765774127939)
      ·
        refine ⟨4091530760507648661191909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727687173671765774127939 4091530760507648661191909)
        ·
          refine ⟨767162017595184123973483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4091530760507648661191909 767162017595184123973483)
          ·
            refine ⟨1150743026392776185960225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767162017595184123973483 1150743026392776185960225)
            ·
              refine ⟨863057269794582139470169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150743026392776185960225 863057269794582139470169)
              ·
                refine ⟨647292952345936604602627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863057269794582139470169 647292952345936604602627)
                ·
                  refine ⟨970939428518904906903941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647292952345936604602627 970939428518904906903941)
                  ·
                    refine ⟨182051142847294670044489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970939428518904906903941 182051142847294670044489)
                    ·
                      rfl

theorem cell22_531815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_531815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531815 prefixEnd_531815 := by exact prefixLift 531815
  have htrace : WordTrace (prefixWord ++ tailWord_531815) baseStart_531815 baseEnd_531815 := by
    simpa [prefixWord, tailWord_531815, baseEnd_531815] using wordTrace_append hprefix tailTrace_531815
  have hstable : (prefixWord ++ tailWord_531815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531815).length < 2 ^ (prefixWord ++ tailWord_531815).sum := by decide
  have hdescent : baseEnd_531815 < baseStart_531815 := by decide
  rcases family_descends (prefixWord ++ tailWord_531815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531826 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_531826 : Nat := 118140960795 + 531826 * 2 ^ 59
def prefixEnd_531826 : Nat := 4983230072969 + 3 ^ 40 * 531826 * 2
def baseEnd_531826 : Nat := 182054908372094308019455

theorem tailTrace_531826 : CollatzResearch.WordTrace tailWord_531826 prefixEnd_531826 182054908372094308019455 := by
  unfold tailWord_531826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849321942823176373667833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12931525180861803663114221 4849321942823176373667833)
  ·
    refine ⟨3636991457117382280250875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4849321942823176373667833 3636991457117382280250875)
    ·
      refine ⟨5455487185676073420376313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3636991457117382280250875 5455487185676073420376313)
      ·
        refine ⟨4091615389257055065282235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5455487185676073420376313 4091615389257055065282235)
        ·
          refine ⟨6137423083885582597923353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091615389257055065282235 6137423083885582597923353)
          ·
            refine ⟨4603067312914186948442515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6137423083885582597923353 4603067312914186948442515)
            ·
              refine ⟨6904600969371280422663773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603067312914186948442515 6904600969371280422663773)
              ·
                refine ⟨2589225363514230158498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6904600969371280422663773 2589225363514230158498915)
                ·
                  refine ⟨3883838045271345237748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589225363514230158498915 3883838045271345237748373)
                  ·
                    refine ⟨182054908372094308019455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3883838045271345237748373 182054908372094308019455)
                    ·
                      rfl

theorem cell22_531826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_531826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531826 prefixEnd_531826 := by exact prefixLift 531826
  have htrace : WordTrace (prefixWord ++ tailWord_531826) baseStart_531826 baseEnd_531826 := by
    simpa [prefixWord, tailWord_531826, baseEnd_531826] using wordTrace_append hprefix tailTrace_531826
  have hstable : (prefixWord ++ tailWord_531826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531826).length < 2 ^ (prefixWord ++ tailWord_531826).sum := by decide
  have hdescent : baseEnd_531826 < baseStart_531826 := by decide
  rcases family_descends (prefixWord ++ tailWord_531826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531843 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_531843 : Nat := 118140960795 + 531843 * 2 ^ 59
def prefixEnd_531843 : Nat := 4983230072969 + 3 ^ 40 * 531843 * 2
def baseEnd_531843 : Nat := 182060727819511930344403

theorem tailTrace_531843 : CollatzResearch.WordTrace tailWord_531843 prefixEnd_531843 182060727819511930344403 := by
  unfold tailWord_531843
  simp only [CollatzResearch.WordTrace]
  refine ⟨19397907812231117398040183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12931938541487411598693455 19397907812231117398040183)
  ·
    refine ⟨29096861718346676097060275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19397907812231117398040183 29096861718346676097060275)
    ·
      refine ⟨43645292577520014145590413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29096861718346676097060275 43645292577520014145590413)
      ·
        refine ⟨16366984716570005304596405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43645292577520014145590413 16366984716570005304596405)
        ·
          refine ⟨1534404817178437997305913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16366984716570005304596405 1534404817178437997305913)
          ·
            refine ⟨1150803612883828497979435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534404817178437997305913 1150803612883828497979435)
            ·
              refine ⟨1726205419325742746969153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150803612883828497979435 1726205419325742746969153)
              ·
                refine ⟨1294654064494307060226865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726205419325742746969153 1294654064494307060226865)
                ·
                  refine ⟨970990548370730295170149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294654064494307060226865 970990548370730295170149)
                  ·
                    refine ⟨182060727819511930344403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970990548370730295170149 182060727819511930344403)
                    ·
                      rfl

theorem cell22_531843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_531843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531843 prefixEnd_531843 := by exact prefixLift 531843
  have htrace : WordTrace (prefixWord ++ tailWord_531843) baseStart_531843 baseEnd_531843 := by
    simpa [prefixWord, tailWord_531843, baseEnd_531843] using wordTrace_append hprefix tailTrace_531843
  have hstable : (prefixWord ++ tailWord_531843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531843).length < 2 ^ (prefixWord ++ tailWord_531843).sum := by decide
  have hdescent : baseEnd_531843 < baseStart_531843 := by decide
  rcases family_descends (prefixWord ++ tailWord_531843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531907 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 1, 3]
def baseStart_531907 : Nat := 118140960795 + 531907 * 2 ^ 59
def prefixEnd_531907 : Nat := 4983230072969 + 3 ^ 40 * 531907 * 2
def baseEnd_531907 : Nat := 182082636327437096744207

theorem tailTrace_531907 : CollatzResearch.WordTrace tailWord_531907 prefixEnd_531907 182082636327437096744207 := by
  unfold tailWord_531907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19400242083999256328369975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12933494722666170885579983 19400242083999256328369975)
  ·
    refine ⟨29100363125998884492554963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19400242083999256328369975 29100363125998884492554963)
    ·
      refine ⟨43650544688998326738832445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29100363125998884492554963 43650544688998326738832445)
      ·
        refine ⟨16368954258374372527062167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43650544688998326738832445 16368954258374372527062167)
        ·
          refine ⟨24553431387561558790593251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368954258374372527062167 24553431387561558790593251)
          ·
            refine ⟨36830147081342338185889877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24553431387561558790593251 36830147081342338185889877)
            ·
              refine ⟨431603286109480525615897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 36830147081342338185889877 431603286109480525615897)
              ·
                refine ⟨323702464582110394211923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431603286109480525615897 323702464582110394211923)
                ·
                  refine ⟨485553696873165591317885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323702464582110394211923 485553696873165591317885)
                  ·
                    refine ⟨182082636327437096744207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485553696873165591317885 182082636327437096744207)
                    ·
                      rfl

theorem cell22_531907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 3].length) (baseStart_531907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531907 prefixEnd_531907 := by exact prefixLift 531907
  have htrace : WordTrace (prefixWord ++ tailWord_531907) baseStart_531907 baseEnd_531907 := by
    simpa [prefixWord, tailWord_531907, baseEnd_531907] using wordTrace_append hprefix tailTrace_531907
  have hstable : (prefixWord ++ tailWord_531907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531907).length < 2 ^ (prefixWord ++ tailWord_531907).sum := by decide
  have hdescent : baseEnd_531907 < baseStart_531907 := by decide
  rcases family_descends (prefixWord ++ tailWord_531907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531950 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_531950 : Nat := 118140960795 + 531950 * 2 ^ 59
def prefixEnd_531950 : Nat := 4983230072969 + 3 ^ 40 * 531950 * 2
def baseEnd_531950 : Nat := 182097356106199317919075

theorem tailTrace_531950 : CollatzResearch.WordTrace tailWord_531950 prefixEnd_531950 182097356106199317919075 := by
  unfold tailWord_531950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425226302855434334023163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12934540281895649781456869 2425226302855434334023163)
  ·
    refine ⟨3637839454283151501034745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2425226302855434334023163 3637839454283151501034745)
    ·
      refine ⟨2728379590712363625776059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3637839454283151501034745 2728379590712363625776059)
      ·
        refine ⟨4092569386068545438664089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728379590712363625776059 4092569386068545438664089)
        ·
          refine ⟨3069427039551409078998067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092569386068545438664089 3069427039551409078998067)
          ·
            refine ⟨4604140559327113618497101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069427039551409078998067 4604140559327113618497101)
            ·
              refine ⟨1726552709747667606936413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4604140559327113618497101 1726552709747667606936413)
              ·
                refine ⟨647457266155375352601155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1726552709747667606936413 647457266155375352601155)
                ·
                  refine ⟨971185899233063028901733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647457266155375352601155 971185899233063028901733)
                  ·
                    refine ⟨182097356106199317919075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971185899233063028901733 182097356106199317919075)
                    ·
                      rfl

theorem cell22_531950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_531950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531950 prefixEnd_531950 := by exact prefixLift 531950
  have htrace : WordTrace (prefixWord ++ tailWord_531950) baseStart_531950 baseEnd_531950 := by
    simpa [prefixWord, tailWord_531950, baseEnd_531950] using wordTrace_append hprefix tailTrace_531950
  have hstable : (prefixWord ++ tailWord_531950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531950).length < 2 ^ (prefixWord ++ tailWord_531950).sum := by decide
  have hdescent : baseEnd_531950 < baseStart_531950 := by decide
  rcases family_descends (prefixWord ++ tailWord_531950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531963 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 4, 3]
def baseStart_531963 : Nat := 118140960795 + 531963 * 2 ^ 59
def prefixEnd_531963 : Nat := 4983230072969 + 3 ^ 40 * 531963 * 2
def baseEnd_531963 : Nat := 182101806271871617344035

theorem tailTrace_531963 : CollatzResearch.WordTrace tailWord_531963 prefixEnd_531963 182101806271871617344035 := by
  unfold tailWord_531963
  simp only [CollatzResearch.WordTrace]
  refine ⟨19402284571796377892408543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12934856381197585261605695 19402284571796377892408543)
  ·
    refine ⟨29103426857694566838612815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19402284571796377892408543 29103426857694566838612815)
    ·
      refine ⟨43655140286541850257919223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29103426857694566838612815 43655140286541850257919223)
      ·
        refine ⟨65482710429812775386878835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43655140286541850257919223 65482710429812775386878835)
        ·
          refine ⟨98224065644719163080318253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65482710429812775386878835 98224065644719163080318253)
          ·
            refine ⟨36834024616769686155119345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98224065644719163080318253 36834024616769686155119345)
            ·
              refine ⟨27625518462577264616339509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36834024616769686155119345 27625518462577264616339509)
              ·
                refine ⟨2589892355866618557781829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27625518462577264616339509 2589892355866618557781829)
                ·
                  refine ⟨485604816724990979584093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2589892355866618557781829 485604816724990979584093)
                  ·
                    refine ⟨182101806271871617344035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485604816724990979584093 182101806271871617344035)
                    ·
                      rfl

theorem cell22_531963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 3].length) (baseStart_531963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531963 prefixEnd_531963 := by exact prefixLift 531963
  have htrace : WordTrace (prefixWord ++ tailWord_531963) baseStart_531963 baseEnd_531963 := by
    simpa [prefixWord, tailWord_531963, baseEnd_531963] using wordTrace_append hprefix tailTrace_531963
  have hstable : (prefixWord ++ tailWord_531963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531963).length < 2 ^ (prefixWord ++ tailWord_531963).sum := by decide
  have hdescent : baseEnd_531963 < baseStart_531963 := by decide
  rcases family_descends (prefixWord ++ tailWord_531963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531965 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 4]
def baseStart_531965 : Nat := 118140960795 + 531965 * 2 ^ 59
def prefixEnd_531965 : Nat := 4983230072969 + 3 ^ 40 * 531965 * 2
def baseEnd_531965 : Nat := 60700830304248092931343

theorem tailTrace_531965 : CollatzResearch.WordTrace tailWord_531965 prefixEnd_531965 60700830304248092931343 := by
  unfold tailWord_531965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19402357517789132233981349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12934905011859421489320899 19402357517789132233981349)
  ·
    refine ⟨3637942034585462293871503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19402357517789132233981349 3637942034585462293871503)
    ·
      refine ⟨5456913051878193440807255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637942034585462293871503 5456913051878193440807255)
      ·
        refine ⟨8185369577817290161210883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456913051878193440807255 8185369577817290161210883)
        ·
          refine ⟨12278054366725935241816325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8185369577817290161210883 12278054366725935241816325)
          ·
            refine ⟨2302135193761112857840561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12278054366725935241816325 2302135193761112857840561)
            ·
              refine ⟨1726601395320834643380421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302135193761112857840561 1726601395320834643380421)
              ·
                refine ⟨323737761622656495633829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1726601395320834643380421 323737761622656495633829)
                ·
                  refine ⟨60700830304248092931343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323737761622656495633829 60700830304248092931343)
                  ·
                    rfl

theorem cell22_531965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_531965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531965 prefixEnd_531965 := by exact prefixLift 531965
  have htrace : WordTrace (prefixWord ++ tailWord_531965) baseStart_531965 baseEnd_531965 := by
    simpa [prefixWord, tailWord_531965, baseEnd_531965] using wordTrace_append hprefix tailTrace_531965
  have hstable : (prefixWord ++ tailWord_531965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531965).length < 2 ^ (prefixWord ++ tailWord_531965).sum := by decide
  have hdescent : baseEnd_531965 < baseStart_531965 := by decide
  rcases family_descends (prefixWord ++ tailWord_531965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531978 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_531978 : Nat := 118140960795 + 531978 * 2 ^ 59
def prefixEnd_531978 : Nat := 4983230072969 + 3 ^ 40 * 531978 * 2
def baseEnd_531978 : Nat := 182106941078416578218989

theorem tailTrace_531978 : CollatzResearch.WordTrace tailWord_531978 prefixEnd_531978 182106941078416578218989 := by
  unfold tailWord_531978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850707916685508863551147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12935221111161356969469725 4850707916685508863551147)
  ·
    refine ⟨7276061875028263295326721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4850707916685508863551147 7276061875028263295326721)
    ·
      refine ⟨5457046406271197471495041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7276061875028263295326721 5457046406271197471495041)
      ·
        refine ⟨4092784804703398103621281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5457046406271197471495041 4092784804703398103621281)
        ·
          refine ⟨3069588603527548577715961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092784804703398103621281 3069588603527548577715961)
          ·
            refine ⟨2302191452645661433286971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3069588603527548577715961 2302191452645661433286971)
            ·
              refine ⟨3453287178968492149930457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302191452645661433286971 3453287178968492149930457)
              ·
                refine ⟨2589965384226369112447843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453287178968492149930457 2589965384226369112447843)
                ·
                  refine ⟨3884948076339553668671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589965384226369112447843 3884948076339553668671765)
                  ·
                    refine ⟨182106941078416578218989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3884948076339553668671765 182106941078416578218989)
                    ·
                      rfl

theorem cell22_531978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_531978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_531978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_531978 prefixEnd_531978 := by exact prefixLift 531978
  have htrace : WordTrace (prefixWord ++ tailWord_531978) baseStart_531978 baseEnd_531978 := by
    simpa [prefixWord, tailWord_531978, baseEnd_531978] using wordTrace_append hprefix tailTrace_531978
  have hstable : (prefixWord ++ tailWord_531978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531978).length < 2 ^ (prefixWord ++ tailWord_531978).sum := by decide
  have hdescent : baseEnd_531978 < baseStart_531978 := by decide
  rcases family_descends (prefixWord ++ tailWord_531978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532053 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_532053 : Nat := 118140960795 + 532053 * 2 ^ 59
def prefixEnd_532053 : Nat := 4983230072969 + 3 ^ 40 * 532053 * 2
def baseEnd_532053 : Nat := 182132615111141382593759

theorem tailTrace_532053 : CollatzResearch.WordTrace tailWord_532053 prefixEnd_532053 182132615111141382593759 := by
  unfold tailWord_532053
  simp only [CollatzResearch.WordTrace]
  refine ⟨19405567141470323263184813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12937044760980215508789875 19405567141470323263184813)
  ·
    refine ⟨7277087678051371223694305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19405567141470323263184813 7277087678051371223694305)
    ·
      refine ⟨5457815758538528417770729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7277087678051371223694305 5457815758538528417770729)
      ·
        refine ⟨4093361818903896313328047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5457815758538528417770729 4093361818903896313328047)
        ·
          refine ⟨6140042728355844469992071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093361818903896313328047 6140042728355844469992071)
          ·
            refine ⟨9210064092533766704988107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140042728355844469992071 9210064092533766704988107)
            ·
              refine ⟨13815096138800650057482161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9210064092533766704988107 13815096138800650057482161)
              ·
                refine ⟨10361322104100487543111621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13815096138800650057482161 10361322104100487543111621)
                ·
                  refine ⟨1942747894518841414333429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10361322104100487543111621 1942747894518841414333429)
                  ·
                    refine ⟨182132615111141382593759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1942747894518841414333429 182132615111141382593759)
                    ·
                      rfl

theorem cell22_532053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_532053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532053 prefixEnd_532053 := by exact prefixLift 532053
  have htrace : WordTrace (prefixWord ++ tailWord_532053) baseStart_532053 baseEnd_532053 := by
    simpa [prefixWord, tailWord_532053, baseEnd_532053] using wordTrace_append hprefix tailTrace_532053
  have hstable : (prefixWord ++ tailWord_532053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532053).length < 2 ^ (prefixWord ++ tailWord_532053).sum := by decide
  have hdescent : baseEnd_532053 < baseStart_532053 := by decide
  rcases family_descends (prefixWord ++ tailWord_532053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532072 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_532072 : Nat := 118140960795 + 532072 * 2 ^ 59
def prefixEnd_532072 : Nat := 4983230072969 + 3 ^ 40 * 532072 * 2
def baseEnd_532072 : Nat := 60713039733143888789567

theorem tailTrace_532072 : CollatzResearch.WordTrace tailWord_532072 prefixEnd_532072 60713039733143888789567 := by
  unfold tailWord_532072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703130064200744754063235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12937506752267659672084313 9703130064200744754063235)
  ·
    refine ⟨14554695096301117131094853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9703130064200744754063235 14554695096301117131094853)
    ·
      refine ⟨2729005330556459462080285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14554695096301117131094853 2729005330556459462080285)
      ·
        refine ⟨1023376998958672298280107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2729005330556459462080285 1023376998958672298280107)
        ·
          refine ⟨1535065498438008447420161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023376998958672298280107 1535065498438008447420161)
          ·
            refine ⟨1151299123828506335565121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535065498438008447420161 1151299123828506335565121)
            ·
              refine ⟨863474342871379751673841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151299123828506335565121 863474342871379751673841)
              ·
                refine ⟨647605757153534813755381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863474342871379751673841 647605757153534813755381)
                ·
                  refine ⟨60713039733143888789567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 647605757153534813755381 60713039733143888789567)
                  ·
                    rfl

theorem cell22_532072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_532072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532072 prefixEnd_532072 := by exact prefixLift 532072
  have htrace : WordTrace (prefixWord ++ tailWord_532072) baseStart_532072 baseEnd_532072 := by
    simpa [prefixWord, tailWord_532072, baseEnd_532072] using wordTrace_append hprefix tailTrace_532072
  have hstable : (prefixWord ++ tailWord_532072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532072).length < 2 ^ (prefixWord ++ tailWord_532072).sum := by decide
  have hdescent : baseEnd_532072 < baseStart_532072 := by decide
  rcases family_descends (prefixWord ++ tailWord_532072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532119 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 1, 4]
def baseStart_532119 : Nat := 118140960795 + 532119 * 2 ^ 59
def prefixEnd_532119 : Nat := 4983230072969 + 3 ^ 40 * 532119 * 2
def baseEnd_532119 : Nat := 182155208259939210443557

theorem tailTrace_532119 : CollatzResearch.WordTrace tailWord_532119 prefixEnd_532119 182155208259939210443557 := by
  unfold tailWord_532119
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407974359231216535087411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12938649572820811023391607 19407974359231216535087411)
  ·
    refine ⟨29111961538846824802631117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19407974359231216535087411 29111961538846824802631117)
    ·
      refine ⟨10916985577067559300986669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29111961538846824802631117 10916985577067559300986669)
      ·
        refine ⟨4093869591400334737870001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10916985577067559300986669 4093869591400334737870001)
        ·
          refine ⟨3070402193550251053402501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093869591400334737870001 3070402193550251053402501)
          ·
            refine ⟨575700411290672072512969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3070402193550251053402501 575700411290672072512969)
            ·
              refine ⟨431775308468004054384727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575700411290672072512969 431775308468004054384727)
              ·
                refine ⟨647662962702006081577091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431775308468004054384727 647662962702006081577091)
                ·
                  refine ⟨971494444053009122365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647662962702006081577091 971494444053009122365637)
                  ·
                    refine ⟨182155208259939210443557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971494444053009122365637 182155208259939210443557)
                    ·
                      rfl

theorem cell22_532119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_532119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532119 prefixEnd_532119 := by exact prefixLift 532119
  have htrace : WordTrace (prefixWord ++ tailWord_532119) baseStart_532119 baseEnd_532119 := by
    simpa [prefixWord, tailWord_532119, baseEnd_532119] using wordTrace_append hprefix tailTrace_532119
  have hstable : (prefixWord ++ tailWord_532119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532119).length < 2 ^ (prefixWord ++ tailWord_532119).sum := by decide
  have hdescent : baseEnd_532119 < baseStart_532119 := by decide
  rcases family_descends (prefixWord ++ tailWord_532119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532132 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_532132 : Nat := 118140960795 + 532132 * 2 ^ 59
def prefixEnd_532132 : Nat := 4983230072969 + 3 ^ 40 * 532132 * 2
def baseEnd_532132 : Nat := 182159658425611509868517

theorem tailTrace_532132 : CollatzResearch.WordTrace tailWord_532132 prefixEnd_532132 182159658425611509868517 := by
  unfold tailWord_532132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9704224254092059877655325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12938965672122746503540433 9704224254092059877655325)
  ·
    refine ⟨3639084095284522454120747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9704224254092059877655325 3639084095284522454120747)
    ·
      refine ⟨5458626142926783681181121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3639084095284522454120747 5458626142926783681181121)
      ·
        refine ⟨4093969607195087760885841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5458626142926783681181121 4093969607195087760885841)
        ·
          refine ⟨3070477205396315820664381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093969607195087760885841 3070477205396315820664381)
          ·
            refine ⟨1151428952023618432749143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3070477205396315820664381 1151428952023618432749143)
            ·
              refine ⟨1727143428035427649123715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151428952023618432749143 1727143428035427649123715)
              ·
                refine ⟨2590715142053141473685573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727143428035427649123715 2590715142053141473685573)
                ·
                  refine ⟨485759089134964026316045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2590715142053141473685573 485759089134964026316045)
                  ·
                    refine ⟨182159658425611509868517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485759089134964026316045 182159658425611509868517)
                    ·
                      rfl

theorem cell22_532132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_532132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532132 prefixEnd_532132 := by exact prefixLift 532132
  have htrace : WordTrace (prefixWord ++ tailWord_532132) baseStart_532132 baseEnd_532132 := by
    simpa [prefixWord, tailWord_532132, baseEnd_532132] using wordTrace_append hprefix tailTrace_532132
  have hstable : (prefixWord ++ tailWord_532132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532132).length < 2 ^ (prefixWord ++ tailWord_532132).sum := by decide
  have hdescent : baseEnd_532132 < baseStart_532132 := by decide
  rcases family_descends (prefixWord ++ tailWord_532132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532149 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_532149 : Nat := 118140960795 + 532149 * 2 ^ 59
def prefixEnd_532149 : Nat := 4983230072969 + 3 ^ 40 * 532149 * 2
def baseEnd_532149 : Nat := 182165477873029132193465

theorem tailTrace_532149 : CollatzResearch.WordTrace tailWord_532149 prefixEnd_532149 182165477873029132193465 := by
  unfold tailWord_532149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409068549122531658679501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12939379032748354439119667 19409068549122531658679501)
  ·
    refine ⟨7278400705920949372004813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19409068549122531658679501 7278400705920949372004813)
    ·
      refine ⟨2729400264720356014501805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7278400705920949372004813 2729400264720356014501805)
      ·
        refine ⟨1023525099270133505438177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2729400264720356014501805 1023525099270133505438177)
        ·
          refine ⟨767643824452600129078633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023525099270133505438177 767643824452600129078633)
          ·
            refine ⟨575732868339450096808975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767643824452600129078633 575732868339450096808975)
            ·
              refine ⟨863599302509175145213463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575732868339450096808975 863599302509175145213463)
              ·
                refine ⟨1295398953763762717820195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863599302509175145213463 1295398953763762717820195)
                ·
                  refine ⟨1943098430645644076730293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295398953763762717820195 1943098430645644076730293)
                  ·
                    refine ⟨182165477873029132193465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1943098430645644076730293 182165477873029132193465)
                    ·
                      rfl

theorem cell22_532149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_532149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532149 prefixEnd_532149 := by exact prefixLift 532149
  have htrace : WordTrace (prefixWord ++ tailWord_532149) baseStart_532149 baseEnd_532149 := by
    simpa [prefixWord, tailWord_532149, baseEnd_532149] using wordTrace_append hprefix tailTrace_532149
  have hstable : (prefixWord ++ tailWord_532149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532149).length < 2 ^ (prefixWord ++ tailWord_532149).sum := by decide
  have hdescent : baseEnd_532149 < baseStart_532149 := by decide
  rcases family_descends (prefixWord ++ tailWord_532149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532166 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_532166 : Nat := 118140960795 + 532166 * 2 ^ 59
def prefixEnd_532166 : Nat := 4983230072969 + 3 ^ 40 * 532166 * 2
def baseEnd_532166 : Nat := 182171297320446754518413

theorem tailTrace_532166 : CollatzResearch.WordTrace tailWord_532166 prefixEnd_532166 182171297320446754518413 := by
  unfold tailWord_532166
  simp only [CollatzResearch.WordTrace]
  refine ⟨606552768439404486314011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12939792393373962374698901 606552768439404486314011)
  ·
    refine ⟨909829152659106729471017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 606552768439404486314011 909829152659106729471017)
    ·
      refine ⟨682371864494330047103263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909829152659106729471017 682371864494330047103263)
      ·
        refine ⟨1023557796741495070654895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682371864494330047103263 1023557796741495070654895)
        ·
          refine ⟨1535336695112242605982343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023557796741495070654895 1535336695112242605982343)
          ·
            refine ⟨2303005042668363908973515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535336695112242605982343 2303005042668363908973515)
            ·
              refine ⟨3454507564002545863460273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303005042668363908973515 3454507564002545863460273)
              ·
                refine ⟨2590880673001909397595205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454507564002545863460273 2590880673001909397595205)
                ·
                  refine ⟨485790126187858012049101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2590880673001909397595205 485790126187858012049101)
                  ·
                    refine ⟨182171297320446754518413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485790126187858012049101 182171297320446754518413)
                    ·
                      rfl

theorem cell22_532166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_532166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532166 prefixEnd_532166 := by exact prefixLift 532166
  have htrace : WordTrace (prefixWord ++ tailWord_532166) baseStart_532166 baseEnd_532166 := by
    simpa [prefixWord, tailWord_532166, baseEnd_532166] using wordTrace_append hprefix tailTrace_532166
  have hstable : (prefixWord ++ tailWord_532166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532166).length < 2 ^ (prefixWord ++ tailWord_532166).sum := by decide
  have hdescent : baseEnd_532166 < baseStart_532166 := by decide
  rcases family_descends (prefixWord ++ tailWord_532166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532282 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_532282 : Nat := 118140960795 + 532282 * 2 ^ 59
def prefixEnd_532282 : Nat := 4983230072969 + 3 ^ 40 * 532282 * 2
def baseEnd_532282 : Nat := 182211006491061118618057

theorem tailTrace_532282 : CollatzResearch.WordTrace tailWord_532282 prefixEnd_532282 182211006491061118618057 := by
  unfold tailWord_532282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853479864410173843317775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12942612971760463582180733 4853479864410173843317775)
  ·
    refine ⟨7280219796615260764976663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853479864410173843317775 7280219796615260764976663)
    ·
      refine ⟨10920329694922891147464995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280219796615260764976663 10920329694922891147464995)
      ·
        refine ⟨16380494542384336721197493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10920329694922891147464995 16380494542384336721197493)
        ·
          refine ⟨1535671363348531567612265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16380494542384336721197493 1535671363348531567612265)
          ·
            refine ⟨1151753522511398675709199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535671363348531567612265 1151753522511398675709199)
            ·
              refine ⟨1727630283767098013563799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151753522511398675709199 1727630283767098013563799)
              ·
                refine ⟨2591445425650647020345699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727630283767098013563799 2591445425650647020345699)
                ·
                  refine ⟨3887168138475970530518549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591445425650647020345699 3887168138475970530518549)
                  ·
                    refine ⟨182211006491061118618057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3887168138475970530518549 182211006491061118618057)
                    ·
                      rfl

theorem cell22_532282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_532282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532282 prefixEnd_532282 := by exact prefixLift 532282
  have htrace : WordTrace (prefixWord ++ tailWord_532282) baseStart_532282 baseEnd_532282 := by
    simpa [prefixWord, tailWord_532282, baseEnd_532282] using wordTrace_append hprefix tailTrace_532282
  have hstable : (prefixWord ++ tailWord_532282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532282).length < 2 ^ (prefixWord ++ tailWord_532282).sum := by decide
  have hdescent : baseEnd_532282 < baseStart_532282 := by decide
  rcases family_descends (prefixWord ++ tailWord_532282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532286 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_532286 : Nat := 118140960795 + 532286 * 2 ^ 59
def prefixEnd_532286 : Nat := 4983230072969 + 3 ^ 40 * 532286 * 2
def baseEnd_532286 : Nat := 60737458590935480506015

theorem tailTrace_532286 : CollatzResearch.WordTrace tailWord_532286 prefixEnd_532286 60737458590935480506015 := by
  unfold tailWord_532286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426758168703275507052089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12942710233084136037611141 2426758168703275507052089)
  ·
    refine ⟨1820068626527456630289067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2426758168703275507052089 1820068626527456630289067)
    ·
      refine ⟨2730102939791184945433601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820068626527456630289067 2730102939791184945433601)
      ·
        refine ⟨2047577204843388709075201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2730102939791184945433601 2047577204843388709075201)
        ·
          refine ⟨1535682903632541531806401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047577204843388709075201 1535682903632541531806401)
          ·
            refine ⟨1151762177724406148854801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535682903632541531806401 1151762177724406148854801)
            ·
              refine ⟨863821633293304611641101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151762177724406148854801 863821633293304611641101)
              ·
                refine ⟨323933112484989229365413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863821633293304611641101 323933112484989229365413)
                ·
                  refine ⟨60737458590935480506015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323933112484989229365413 60737458590935480506015)
                  ·
                    rfl

theorem cell22_532286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_532286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532286 prefixEnd_532286 := by exact prefixLift 532286
  have htrace : WordTrace (prefixWord ++ tailWord_532286) baseStart_532286 baseEnd_532286 := by
    simpa [prefixWord, tailWord_532286, baseEnd_532286] using wordTrace_append hprefix tailTrace_532286
  have hstable : (prefixWord ++ tailWord_532286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532286).length < 2 ^ (prefixWord ++ tailWord_532286).sum := by decide
  have hdescent : baseEnd_532286 < baseStart_532286 := by decide
  rcases family_descends (prefixWord ++ tailWord_532286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532301 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_532301 : Nat := 118140960795 + 532301 * 2 ^ 59
def prefixEnd_532301 : Nat := 4983230072969 + 3 ^ 40 * 532301 * 2
def baseEnd_532301 : Nat := 182217510579351402392999

theorem tailTrace_532301 : CollatzResearch.WordTrace tailWord_532301 prefixEnd_532301 182217510579351402392999 := by
  unfold tailWord_532301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414612444571861618212757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12943074963047907745475171 19414612444571861618212757)
  ·
    refine ⟨910059958339306013353723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19414612444571861618212757 910059958339306013353723)
    ·
      refine ⟨1365089937508959020030585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910059958339306013353723 1365089937508959020030585)
      ·
        refine ⟨1023817453131719265022939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365089937508959020030585 1023817453131719265022939)
        ·
          refine ⟨1535726179697578897534409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023817453131719265022939 1535726179697578897534409)
          ·
            refine ⟨1151794634773184173150807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535726179697578897534409 1151794634773184173150807)
            ·
              refine ⟨1727691952159776259726211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151794634773184173150807 1727691952159776259726211)
              ·
                refine ⟨2591537928239664389589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727691952159776259726211 2591537928239664389589317)
                ·
                  refine ⟨485913361544937073047997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2591537928239664389589317 485913361544937073047997)
                  ·
                    refine ⟨182217510579351402392999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485913361544937073047997 182217510579351402392999)
                    ·
                      rfl

theorem cell22_532301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_532301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532301 prefixEnd_532301 := by exact prefixLift 532301
  have htrace : WordTrace (prefixWord ++ tailWord_532301) baseStart_532301 baseEnd_532301 := by
    simpa [prefixWord, tailWord_532301, baseEnd_532301] using wordTrace_append hprefix tailTrace_532301
  have hstable : (prefixWord ++ tailWord_532301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532301).length < 2 ^ (prefixWord ++ tailWord_532301).sum := by decide
  have hdescent : baseEnd_532301 < baseStart_532301 := by decide
  rcases family_descends (prefixWord ++ tailWord_532301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532346 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_532346 : Nat := 118140960795 + 532346 * 2 ^ 59
def prefixEnd_532346 : Nat := 4983230072969 + 3 ^ 40 * 532346 * 2
def baseEnd_532346 : Nat := 182232914998986285017861

theorem tailTrace_532346 : CollatzResearch.WordTrace tailWord_532346 prefixEnd_532346 182232914998986285017861 := by
  unfold tailWord_532346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854063432352208575900223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12944169152939222869067261 4854063432352208575900223)
  ·
    refine ⟨7281095148528312863850335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4854063432352208575900223 7281095148528312863850335)
    ·
      refine ⟨10921642722792469295775503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7281095148528312863850335 10921642722792469295775503)
      ·
        refine ⟨16382464084188703943663255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921642722792469295775503 16382464084188703943663255)
        ·
          refine ⟨24573696126283055915494883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16382464084188703943663255 24573696126283055915494883)
          ·
            refine ⟨36860544189424583873242325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24573696126283055915494883 36860544189424583873242325)
            ·
              refine ⟨863919004439638684529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36860544189424583873242325 863919004439638684529117)
              ·
                refine ⟨323969626664864506698419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863919004439638684529117 323969626664864506698419)
                ·
                  refine ⟨485954439997296760047629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323969626664864506698419 485954439997296760047629)
                  ·
                    refine ⟨182232914998986285017861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485954439997296760047629 182232914998986285017861)
                    ·
                      rfl

theorem cell22_532346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_532346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532346 prefixEnd_532346 := by exact prefixLift 532346
  have htrace : WordTrace (prefixWord ++ tailWord_532346) baseStart_532346 baseEnd_532346 := by
    simpa [prefixWord, tailWord_532346, baseEnd_532346] using wordTrace_append hprefix tailTrace_532346
  have hstable : (prefixWord ++ tailWord_532346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532346).length < 2 ^ (prefixWord ++ tailWord_532346).sum := by decide
  have hdescent : baseEnd_532346 < baseStart_532346 := by decide
  rcases family_descends (prefixWord ++ tailWord_532346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532376 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_532376 : Nat := 118140960795 + 532376 * 2 ^ 59
def prefixEnd_532376 : Nat := 4983230072969 + 3 ^ 40 * 532376 * 2
def baseEnd_532376 : Nat := 60747728204025402255923

theorem tailTrace_532376 : CollatzResearch.WordTrace tailWord_532376 prefixEnd_532376 60747728204025402255923 := by
  unfold tailWord_532376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708673959650074713596491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12944898612866766284795321 9708673959650074713596491)
  ·
    refine ⟨14563010939475112070394737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9708673959650074713596491 14563010939475112070394737)
    ·
      refine ⟨10922258204606334052796053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14563010939475112070394737 10922258204606334052796053)
      ·
        refine ⟨511980853340921908724815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10922258204606334052796053 511980853340921908724815)
        ·
          refine ⟨767971280011382863087223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511980853340921908724815 767971280011382863087223)
          ·
            refine ⟨1151956920017074294630835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767971280011382863087223 1151956920017074294630835)
            ·
              refine ⟨1727935380025611441946253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151956920017074294630835 1727935380025611441946253)
              ·
                refine ⟨647975767509604290729845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727935380025611441946253 647975767509604290729845)
                ·
                  refine ⟨60747728204025402255923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 647975767509604290729845 60747728204025402255923)
                  ·
                    rfl

theorem cell22_532376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_532376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532376 prefixEnd_532376 := by exact prefixLift 532376
  have htrace : WordTrace (prefixWord ++ tailWord_532376) baseStart_532376 baseEnd_532376 := by
    simpa [prefixWord, tailWord_532376, baseEnd_532376] using wordTrace_append hprefix tailTrace_532376
  have hstable : (prefixWord ++ tailWord_532376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532376).length < 2 ^ (prefixWord ++ tailWord_532376).sum := by decide
  have hdescent : baseEnd_532376 < baseStart_532376 := by decide
  rcases family_descends (prefixWord ++ tailWord_532376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532432 : List Nat := [2, 1, 1, 1, 1, 2, 7, 7]
def baseStart_532432 : Nat := 118140960795 + 532432 * 2 ^ 59
def prefixEnd_532432 : Nat := 4983230072969 + 3 ^ 40 * 532432 * 2
def baseEnd_532432 : Nat := 20251372728501191929733

theorem tailTrace_532432 : CollatzResearch.WordTrace tailWord_532432 prefixEnd_532432 20251372728501191929733 := by
  unfold tailWord_532432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709695203548635495615775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12946260271398180660821033 9709695203548635495615775)
  ·
    refine ⟨14564542805322953243423663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709695203548635495615775 14564542805322953243423663)
    ·
      refine ⟨21846814207984429865135495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564542805322953243423663 21846814207984429865135495)
      ·
        refine ⟨32770221311976644797703243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846814207984429865135495 32770221311976644797703243)
        ·
          refine ⟨49155331967964967196554865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32770221311976644797703243 49155331967964967196554865)
          ·
            refine ⟨36866498975973725397416149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49155331967964967196554865 36866498975973725397416149)
            ·
              refine ⟨864058569749384189001941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36866498975973725397416149 864058569749384189001941)
              ·
                refine ⟨20251372728501191929733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 864058569749384189001941 20251372728501191929733)
                ·
                  rfl

theorem cell22_532432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_532432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532432 prefixEnd_532432 := by exact prefixLift 532432
  have htrace : WordTrace (prefixWord ++ tailWord_532432) baseStart_532432 baseEnd_532432 := by
    simpa [prefixWord, tailWord_532432, baseEnd_532432] using wordTrace_append hprefix tailTrace_532432
  have hstable : (prefixWord ++ tailWord_532432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532432).length < 2 ^ (prefixWord ++ tailWord_532432).sum := by decide
  have hdescent : baseEnd_532432 < baseStart_532432 := by decide
  rcases family_descends (prefixWord ++ tailWord_532432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532436 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_532436 : Nat := 118140960795 + 532436 * 2 ^ 59
def prefixEnd_532436 : Nat := 4983230072969 + 3 ^ 40 * 532436 * 2
def baseEnd_532436 : Nat := 182263723838256050267585

theorem tailTrace_532436 : CollatzResearch.WordTrace tailWord_532436 prefixEnd_532436 182263723838256050267585 := by
  unfold tailWord_532436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709768149541389837188581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12946357532721853116251441 9709768149541389837188581)
  ·
    refine ⟨1820581528039010594472859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9709768149541389837188581 1820581528039010594472859)
    ·
      refine ⟨2730872292058515891709289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820581528039010594472859 2730872292058515891709289)
      ·
        refine ⟨2048154219043886918781967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2730872292058515891709289 2048154219043886918781967)
        ·
          refine ⟨3072231328565830378172951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048154219043886918781967 3072231328565830378172951)
          ·
            refine ⟨4608346992848745567259427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072231328565830378172951 4608346992848745567259427)
            ·
              refine ⟨6912520489273118350889141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608346992848745567259427 6912520489273118350889141)
              ·
                refine ⟨648048795869354845395857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6912520489273118350889141 648048795869354845395857)
                ·
                  refine ⟨486036596902016134046893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648048795869354845395857 486036596902016134046893)
                  ·
                    refine ⟨182263723838256050267585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486036596902016134046893 182263723838256050267585)
                    ·
                      rfl

theorem cell22_532436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_532436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532436 prefixEnd_532436 := by exact prefixLift 532436
  have htrace : WordTrace (prefixWord ++ tailWord_532436) baseStart_532436 baseEnd_532436 := by
    simpa [prefixWord, tailWord_532436, baseEnd_532436] using wordTrace_append hprefix tailTrace_532436
  have hstable : (prefixWord ++ tailWord_532436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532436).length < 2 ^ (prefixWord ++ tailWord_532436).sum := by decide
  have hdescent : baseEnd_532436 < baseStart_532436 := by decide
  rcases family_descends (prefixWord ++ tailWord_532436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532451 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 2, 4]
def baseStart_532451 : Nat := 118140960795 + 532451 * 2 ^ 59
def prefixEnd_532451 : Nat := 4983230072969 + 3 ^ 40 * 532451 * 2
def baseEnd_532451 : Nat := 182268858644801011142539

theorem tailTrace_532451 : CollatzResearch.WordTrace tailWord_532451 prefixEnd_532451 182268858644801011142539 := by
  unfold tailWord_532451
  simp only [CollatzResearch.WordTrace]
  refine ⟨19420083394028437236173207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12946722262685624824115471 19420083394028437236173207)
  ·
    refine ⟨29130125091042655854259811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19420083394028437236173207 29130125091042655854259811)
    ·
      refine ⟨43695187636563983781389717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29130125091042655854259811 43695187636563983781389717)
      ·
        refine ⟨2048211920463936739752643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43695187636563983781389717 2048211920463936739752643)
        ·
          refine ⟨3072317880695905109628965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048211920463936739752643 3072317880695905109628965)
          ·
            refine ⟨576059602630482208055431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3072317880695905109628965 576059602630482208055431)
            ·
              refine ⟨864089403945723312083147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576059602630482208055431 864089403945723312083147)
              ·
                refine ⟨1296134105918584968124721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864089403945723312083147 1296134105918584968124721)
                ·
                  refine ⟨972100579438938726093541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296134105918584968124721 972100579438938726093541)
                  ·
                    refine ⟨182268858644801011142539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972100579438938726093541 182268858644801011142539)
                    ·
                      rfl

theorem cell22_532451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].length) (baseStart_532451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532451 prefixEnd_532451 := by exact prefixLift 532451
  have htrace : WordTrace (prefixWord ++ tailWord_532451) baseStart_532451 baseEnd_532451 := by
    simpa [prefixWord, tailWord_532451, baseEnd_532451] using wordTrace_append hprefix tailTrace_532451
  have hstable : (prefixWord ++ tailWord_532451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532451).length < 2 ^ (prefixWord ++ tailWord_532451).sum := by decide
  have hdescent : baseEnd_532451 < baseStart_532451 := by decide
  rcases family_descends (prefixWord ++ tailWord_532451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532470 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_532470 : Nat := 118140960795 + 532470 * 2 ^ 59
def prefixEnd_532470 : Nat := 4983230072969 + 3 ^ 40 * 532470 * 2
def baseEnd_532470 : Nat := 182275362733091294917481

theorem tailTrace_532470 : CollatzResearch.WordTrace tailWord_532470 prefixEnd_532470 182275362733091294917481 := by
  unfold tailWord_532470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213798523809975217569679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12947184253973068987409909 1213798523809975217569679)
  ·
    refine ⟨1820697785714962826354519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213798523809975217569679 1820697785714962826354519)
    ·
      refine ⟨2731046678572444239531779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820697785714962826354519 2731046678572444239531779)
      ·
        refine ⟨4096570017858666359297669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731046678572444239531779 4096570017858666359297669)
        ·
          refine ⟨768106878348499942368313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4096570017858666359297669 768106878348499942368313)
          ·
            refine ⟨576080158761374956776235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768106878348499942368313 576080158761374956776235)
            ·
              refine ⟨864120238142062435164353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576080158761374956776235 864120238142062435164353)
              ·
                refine ⟨648090178606546826373265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864120238142062435164353 648090178606546826373265)
                ·
                  refine ⟨486067633954910119779949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648090178606546826373265 486067633954910119779949)
                  ·
                    refine ⟨182275362733091294917481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486067633954910119779949 182275362733091294917481)
                    ·
                      rfl

theorem cell22_532470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_532470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532470 prefixEnd_532470 := by exact prefixLift 532470
  have htrace : WordTrace (prefixWord ++ tailWord_532470) baseStart_532470 baseEnd_532470 := by
    simpa [prefixWord, tailWord_532470, baseEnd_532470] using wordTrace_append hprefix tailTrace_532470
  have hstable : (prefixWord ++ tailWord_532470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532470).length < 2 ^ (prefixWord ++ tailWord_532470).sum := by decide
  have hdescent : baseEnd_532470 < baseStart_532470 := by decide
  rcases family_descends (prefixWord ++ tailWord_532470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532481 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_532481 : Nat := 118140960795 + 532481 * 2 ^ 59
def prefixEnd_532481 : Nat := 4983230072969 + 3 ^ 40 * 532481 * 2
def baseEnd_532481 : Nat := 182279128257890932892447

theorem tailTrace_532481 : CollatzResearch.WordTrace tailWord_532481 prefixEnd_532481 182279128257890932892447 := by
  unfold tailWord_532481
  simp only [CollatzResearch.WordTrace]
  refine ⟨19421177583919752359765297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12947451722613168239843531 19421177583919752359765297)
  ·
    refine ⟨14565883187939814269823973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19421177583919752359765297 14565883187939814269823973)
    ·
      refine ⟨2731103097738715175591995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14565883187939814269823973 2731103097738715175591995)
      ·
        refine ⟨4096654646608072763387993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731103097738715175591995 4096654646608072763387993)
        ·
          refine ⟨3072490984956054572540995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4096654646608072763387993 3072490984956054572540995)
          ·
            refine ⟨4608736477434081858811493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072490984956054572540995 4608736477434081858811493)
            ·
              refine ⟨864138089518890348527155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4608736477434081858811493 864138089518890348527155)
              ·
                refine ⟨1296207134278335522790733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864138089518890348527155 1296207134278335522790733)
                ·
                  refine ⟨486077675354375821046525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1296207134278335522790733 486077675354375821046525)
                  ·
                    refine ⟨182279128257890932892447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486077675354375821046525 182279128257890932892447)
                    ·
                      rfl

theorem cell22_532481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_532481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532481 prefixEnd_532481 := by exact prefixLift 532481
  have htrace : WordTrace (prefixWord ++ tailWord_532481) baseStart_532481 baseEnd_532481 := by
    simpa [prefixWord, tailWord_532481, baseEnd_532481] using wordTrace_append hprefix tailTrace_532481
  have hstable : (prefixWord ++ tailWord_532481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532481).length < 2 ^ (prefixWord ++ tailWord_532481).sum := by decide
  have hdescent : baseEnd_532481 < baseStart_532481 := by decide
  rcases family_descends (prefixWord ++ tailWord_532481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532500 : List Nat := [2, 4, 3, 2, 1, 2, 2, 6]
def baseStart_532500 : Nat := 118140960795 + 532500 * 2 ^ 59
def prefixEnd_532500 : Nat := 4983230072969 + 3 ^ 40 * 532500 * 2
def baseEnd_532500 : Nat := 20253959149575690740821

theorem tailTrace_532500 : CollatzResearch.WordTrace tailWord_532500 prefixEnd_532500 20253959149575690740821 := by
  unfold tailWord_532500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9710935285425459302353477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12947913713900612403137969 9710935285425459302353477)
  ·
    refine ⟨1820800366017273619191277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9710935285425459302353477 1820800366017273619191277)
    ·
      refine ⟨682800137256477607196729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1820800366017273619191277 682800137256477607196729)
      ·
        refine ⟨512100102942358205397547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 682800137256477607196729 512100102942358205397547)
        ·
          refine ⟨768150154413537308096321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512100102942358205397547 768150154413537308096321)
          ·
            refine ⟨576112615810152981072241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768150154413537308096321 576112615810152981072241)
            ·
              refine ⟨432084461857614735804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576112615810152981072241 432084461857614735804181)
              ·
                refine ⟨20253959149575690740821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432084461857614735804181 20253959149575690740821)
                ·
                  rfl

theorem cell22_532500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_532500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532500 prefixEnd_532500 := by exact prefixLift 532500
  have htrace : WordTrace (prefixWord ++ tailWord_532500) baseStart_532500 baseEnd_532500 := by
    simpa [prefixWord, tailWord_532500, baseEnd_532500] using wordTrace_append hprefix tailTrace_532500
  have hstable : (prefixWord ++ tailWord_532500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532500).length < 2 ^ (prefixWord ++ tailWord_532500).sum := by decide
  have hdescent : baseEnd_532500 < baseStart_532500 := by decide
  rcases family_descends (prefixWord ++ tailWord_532500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532532 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_532532 : Nat := 118140960795 + 532532 * 2 ^ 59
def prefixEnd_532532 : Nat := 4983230072969 + 3 ^ 40 * 532532 * 2
def baseEnd_532532 : Nat := 182296586600143799867291

theorem tailTrace_532532 : CollatzResearch.WordTrace tailWord_532532 prefixEnd_532532 182296586600143799867291 := by
  unfold tailWord_532532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711518853367494034935925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12948691804489992046581233 9711518853367494034935925)
  ·
    refine ⟨910454892503202565775243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9711518853367494034935925 910454892503202565775243)
    ·
      refine ⟨1365682338754803848662865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910454892503202565775243 1365682338754803848662865)
      ·
        refine ⟨1024261754066102886497149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365682338754803848662865 1024261754066102886497149)
        ·
          refine ⟨384098157774788582436431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1024261754066102886497149 384098157774788582436431)
          ·
            refine ⟨576147236662182873654647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384098157774788582436431 576147236662182873654647)
            ·
              refine ⟨864220854993274310481971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576147236662182873654647 864220854993274310481971)
              ·
                refine ⟨1296331282489911465722957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864220854993274310481971 1296331282489911465722957)
                ·
                  refine ⟨486124230933716799646109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1296331282489911465722957 486124230933716799646109)
                  ·
                    refine ⟨182296586600143799867291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486124230933716799646109 182296586600143799867291)
                    ·
                      rfl

theorem cell22_532532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_532532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532532 prefixEnd_532532 := by exact prefixLift 532532
  have htrace : WordTrace (prefixWord ++ tailWord_532532) baseStart_532532 baseEnd_532532 := by
    simpa [prefixWord, tailWord_532532, baseEnd_532532] using wordTrace_append hprefix tailTrace_532532
  have hstable : (prefixWord ++ tailWord_532532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532532).length < 2 ^ (prefixWord ++ tailWord_532532).sum := by decide
  have hdescent : baseEnd_532532 < baseStart_532532 := by decide
  rcases family_descends (prefixWord ++ tailWord_532532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532554 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_532554 : Nat := 118140960795 + 532554 * 2 ^ 59
def prefixEnd_532554 : Nat := 4983230072969 + 3 ^ 40 * 532554 * 2
def baseEnd_532554 : Nat := 182304117649743075817223

theorem tailTrace_532554 : CollatzResearch.WordTrace tailWord_532554 prefixEnd_532554 182304117649743075817223 := by
  unfold tailWord_532554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855960028163821456793179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12949226741770190551448477 4855960028163821456793179)
  ·
    refine ⟨7283940042245732185189769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4855960028163821456793179 7283940042245732185189769)
    ·
      refine ⟨5462955031684299138892327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7283940042245732185189769 5462955031684299138892327)
      ·
        refine ⟨8194432547526448708338491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462955031684299138892327 8194432547526448708338491)
        ·
          refine ⟨12291648821289673062507737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8194432547526448708338491 12291648821289673062507737)
          ·
            refine ⟨9218736615967254796880803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12291648821289673062507737 9218736615967254796880803)
            ·
              refine ⟨13828104923950882195321205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9218736615967254796880803 13828104923950882195321205)
              ·
                refine ⟨1296384836620395205811363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13828104923950882195321205 1296384836620395205811363)
                ·
                  refine ⟨1944577254930592808717045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296384836620395205811363 1944577254930592808717045)
                  ·
                    refine ⟨182304117649743075817223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1944577254930592808717045 182304117649743075817223)
                    ·
                      rfl

theorem cell22_532554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_532554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532554 prefixEnd_532554 := by exact prefixLift 532554
  have htrace : WordTrace (prefixWord ++ tailWord_532554) baseStart_532554 baseEnd_532554 := by
    simpa [prefixWord, tailWord_532554, baseEnd_532554] using wordTrace_append hprefix tailTrace_532554
  have hstable : (prefixWord ++ tailWord_532554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532554).length < 2 ^ (prefixWord ++ tailWord_532554).sum := by decide
  have hdescent : baseEnd_532554 < baseStart_532554 := by decide
  rcases family_descends (prefixWord ++ tailWord_532554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532558 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_532558 : Nat := 118140960795 + 532558 * 2 ^ 59
def prefixEnd_532558 : Nat := 4983230072969 + 3 ^ 40 * 532558 * 2
def baseEnd_532558 : Nat := 182305486931488398717211

theorem tailTrace_532558 : CollatzResearch.WordTrace tailWord_532558 prefixEnd_532558 182305486931488398717211 := by
  unfold tailWord_532558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427998250580099313789791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12949324003093863006878885 2427998250580099313789791)
  ·
    refine ⟨3641997375870148970684687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2427998250580099313789791 3641997375870148970684687)
    ·
      refine ⟨5462996063805223456027031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3641997375870148970684687 5462996063805223456027031)
      ·
        refine ⟨8194494095707835184040547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462996063805223456027031 8194494095707835184040547)
        ·
          refine ⟨12291741143561752776060821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8194494095707835184040547 12291741143561752776060821)
          ·
            refine ⟨576175366104457161377851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12291741143561752776060821 576175366104457161377851)
            ·
              refine ⟨864263049156685742066777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576175366104457161377851 864263049156685742066777)
              ·
                refine ⟨648197286867514306550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864263049156685742066777 648197286867514306550083)
                ·
                  refine ⟨972295930301271459825125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648197286867514306550083 972295930301271459825125)
                  ·
                    refine ⟨182305486931488398717211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972295930301271459825125 182305486931488398717211)
                    ·
                      rfl

theorem cell22_532558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_532558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532558 prefixEnd_532558 := by exact prefixLift 532558
  have htrace : WordTrace (prefixWord ++ tailWord_532558) baseStart_532558 baseEnd_532558 := by
    simpa [prefixWord, tailWord_532558, baseEnd_532558] using wordTrace_append hprefix tailTrace_532558
  have hstable : (prefixWord ++ tailWord_532558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532558).length < 2 ^ (prefixWord ++ tailWord_532558).sum := by decide
  have hdescent : baseEnd_532558 < baseStart_532558 := by decide
  rcases family_descends (prefixWord ++ tailWord_532558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532588 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_532588 : Nat := 118140960795 + 532588 * 2 ^ 59
def prefixEnd_532588 : Nat := 4983230072969 + 3 ^ 40 * 532588 * 2
def baseEnd_532588 : Nat := 182315756544578320467119

theorem tailTrace_532588 : CollatzResearch.WordTrace tailWord_532588 prefixEnd_532588 182315756544578320467119 := by
  unfold tailWord_532588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712540097266054816955209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12950053463021406422606945 9712540097266054816955209)
  ·
    refine ⟨7284405072949541112716407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712540097266054816955209 7284405072949541112716407)
    ·
      refine ⟨10926607609424311669074611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284405072949541112716407 10926607609424311669074611)
      ·
        refine ⟨16389911414136467503611917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926607609424311669074611 16389911414136467503611917)
        ·
          refine ⟨6146216780301175313854469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16389911414136467503611917 6146216780301175313854469)
          ·
            refine ⟨1152415646306470371347713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6146216780301175313854469 1152415646306470371347713)
            ·
              refine ⟨864311734729852778510785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152415646306470371347713 864311734729852778510785)
              ·
                refine ⟨648233801047389583883089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864311734729852778510785 648233801047389583883089)
                ·
                  refine ⟨486175350785542187912317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648233801047389583883089 486175350785542187912317)
                  ·
                    refine ⟨182315756544578320467119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486175350785542187912317 182315756544578320467119)
                    ·
                      rfl

theorem cell22_532588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_532588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532588 prefixEnd_532588 := by exact prefixLift 532588
  have htrace : WordTrace (prefixWord ++ tailWord_532588) baseStart_532588 baseEnd_532588 := by
    simpa [prefixWord, tailWord_532588, baseEnd_532588] using wordTrace_append hprefix tailTrace_532588
  have hstable : (prefixWord ++ tailWord_532588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532588).length < 2 ^ (prefixWord ++ tailWord_532588).sum := by decide
  have hdescent : baseEnd_532588 < baseStart_532588 := by decide
  rcases family_descends (prefixWord ++ tailWord_532588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532601 : List Nat := [1, 2, 1, 3, 4, 3, 1, 7]
def baseStart_532601 : Nat := 118140960795 + 532601 * 2 ^ 59
def prefixEnd_532601 : Nat := 4983230072969 + 3 ^ 40 * 532601 * 2
def baseEnd_532601 : Nat := 20257800745583402210231

theorem tailTrace_532601 : CollatzResearch.WordTrace tailWord_532601 prefixEnd_532601 20257800745583402210231 := by
  unfold tailWord_532601
  simp only [CollatzResearch.WordTrace]
  refine ⟨19425554343485012854133657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12950369562323341902755771 19425554343485012854133657)
  ·
    refine ⟨14569165757613759640600243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19425554343485012854133657 14569165757613759640600243)
    ·
      refine ⟨21853748636420639460900365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14569165757613759640600243 21853748636420639460900365)
      ·
        refine ⟨8195155738657739797837637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21853748636420639460900365 8195155738657739797837637)
        ·
          refine ⟨1536591700998326212094557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8195155738657739797837637 1536591700998326212094557)
          ·
            refine ⟨576221887874372329535459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1536591700998326212094557 576221887874372329535459)
            ·
              refine ⟨864332831811558494303189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576221887874372329535459 864332831811558494303189)
              ·
                refine ⟨20257800745583402210231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 864332831811558494303189 20257800745583402210231)
                ·
                  rfl

theorem cell22_532601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 7].length) (baseStart_532601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532601 prefixEnd_532601 := by exact prefixLift 532601
  have htrace : WordTrace (prefixWord ++ tailWord_532601) baseStart_532601 baseEnd_532601 := by
    simpa [prefixWord, tailWord_532601, baseEnd_532601] using wordTrace_append hprefix tailTrace_532601
  have hstable : (prefixWord ++ tailWord_532601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532601).length < 2 ^ (prefixWord ++ tailWord_532601).sum := by decide
  have hdescent : baseEnd_532601 < baseStart_532601 := by decide
  rcases family_descends (prefixWord ++ tailWord_532601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532629 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 7]
def baseStart_532629 : Nat := 118140960795 + 532629 * 2 ^ 59
def prefixEnd_532629 : Nat := 4983230072969 + 3 ^ 40 * 532629 * 2
def baseEnd_532629 : Nat := 60776597227489293397331

theorem tailTrace_532629 : CollatzResearch.WordTrace tailWord_532629 prefixEnd_532629 60776597227489293397331 := by
  unfold tailWord_532629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19426575587383573636152941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12951050391589049090768627 19426575587383573636152941)
  ·
    refine ⟨7284965845268840113557353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19426575587383573636152941 7284965845268840113557353)
    ·
      refine ⟨5463724383951630085168015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7284965845268840113557353 5463724383951630085168015)
      ·
        refine ⟨8195586575927445127752023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5463724383951630085168015 8195586575927445127752023)
        ·
          refine ⟨12293379863891167691628035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195586575927445127752023 12293379863891167691628035)
          ·
            refine ⟨18440069795836751537442053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12293379863891167691628035 18440069795836751537442053)
            ·
              refine ⟨3457513086719390913270385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18440069795836751537442053 3457513086719390913270385)
              ·
                refine ⟨2593134815039543184952789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3457513086719390913270385 2593134815039543184952789)
                ·
                  refine ⟨60776597227489293397331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2593134815039543184952789 60776597227489293397331)
                  ·
                    rfl

theorem cell22_532629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_532629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532629 prefixEnd_532629 := by exact prefixLift 532629
  have htrace : WordTrace (prefixWord ++ tailWord_532629) baseStart_532629 baseEnd_532629 := by
    simpa [prefixWord, tailWord_532629, baseEnd_532629] using wordTrace_append hprefix tailTrace_532629
  have hstable : (prefixWord ++ tailWord_532629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532629).length < 2 ^ (prefixWord ++ tailWord_532629).sum := by decide
  have hdescent : baseEnd_532629 < baseStart_532629 := by decide
  rcases family_descends (prefixWord ++ tailWord_532629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532663 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 5]
def baseStart_532663 : Nat := 118140960795 + 532663 * 2 ^ 59
def prefixEnd_532663 : Nat := 4983230072969 + 3 ^ 40 * 532663 * 2
def baseEnd_532663 : Nat := 60780476859101041613963

theorem tailTrace_532663 : CollatzResearch.WordTrace tailWord_532663 prefixEnd_532663 60780476859101041613963 := by
  unfold tailWord_532663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19427815669260397442890643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12951877112840264961927095 19427815669260397442890643)
  ·
    refine ⟨29141723503890596164335965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19427815669260397442890643 29141723503890596164335965)
    ·
      refine ⟨10928146313958973561625987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29141723503890596164335965 10928146313958973561625987)
      ·
        refine ⟨16392219470938460342438981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928146313958973561625987 16392219470938460342438981)
        ·
          refine ⟨3073541150800961314207309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16392219470938460342438981 3073541150800961314207309)
          ·
            refine ⟨1152577931550360492827741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073541150800961314207309 1152577931550360492827741)
            ·
              refine ⟨432216724331385184810403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1152577931550360492827741 432216724331385184810403)
              ·
                refine ⟨648325086497077777215605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432216724331385184810403 648325086497077777215605)
                ·
                  refine ⟨60780476859101041613963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 648325086497077777215605 60780476859101041613963)
                  ·
                    rfl

theorem cell22_532663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 5].length) (baseStart_532663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532663 prefixEnd_532663 := by exact prefixLift 532663
  have htrace : WordTrace (prefixWord ++ tailWord_532663) baseStart_532663 baseEnd_532663 := by
    simpa [prefixWord, tailWord_532663, baseEnd_532663] using wordTrace_append hprefix tailTrace_532663
  have hstable : (prefixWord ++ tailWord_532663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532663).length < 2 ^ (prefixWord ++ tailWord_532663).sum := by decide
  have hdescent : baseEnd_532663 < baseStart_532663 := by decide
  rcases family_descends (prefixWord ++ tailWord_532663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532684 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_532684 : Nat := 118140960795 + 532684 * 2 ^ 59
def prefixEnd_532684 : Nat := 4983230072969 + 3 ^ 40 * 532684 * 2
def baseEnd_532684 : Nat := 182348619306466070066825

theorem tailTrace_532684 : CollatzResearch.WordTrace tailWord_532684 prefixEnd_532684 182348619306466070066825 := by
  unfold tailWord_532684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714290801092159014702553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12952387734789545352936737 9714290801092159014702553)
  ·
    refine ⟨7285718100819119261026915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9714290801092159014702553 7285718100819119261026915)
    ·
      refine ⟨10928577151228678891540373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285718100819119261026915 10928577151228678891540373)
      ·
        refine ⟨512277053963844323040955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10928577151228678891540373 512277053963844323040955)
        ·
          refine ⟨768415580945766484561433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512277053963844323040955 768415580945766484561433)
          ·
            refine ⟨576311685709324863421075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768415580945766484561433 576311685709324863421075)
            ·
              refine ⟨864467528563987295131613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576311685709324863421075 864467528563987295131613)
              ·
                refine ⟨324175323211495235674355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864467528563987295131613 324175323211495235674355)
                ·
                  refine ⟨486262984817242853511533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324175323211495235674355 486262984817242853511533)
                  ·
                    refine ⟨182348619306466070066825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486262984817242853511533 182348619306466070066825)
                    ·
                      rfl

theorem cell22_532684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_532684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532684 prefixEnd_532684 := by exact prefixLift 532684
  have htrace : WordTrace (prefixWord ++ tailWord_532684) baseStart_532684 baseEnd_532684 := by
    simpa [prefixWord, tailWord_532684, baseEnd_532684] using wordTrace_append hprefix tailTrace_532684
  have hstable : (prefixWord ++ tailWord_532684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532684).length < 2 ^ (prefixWord ++ tailWord_532684).sum := by decide
  have hdescent : baseEnd_532684 < baseStart_532684 := by decide
  rcases family_descends (prefixWord ++ tailWord_532684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532723 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 2, 3]
def baseStart_532723 : Nat := 118140960795 + 532723 * 2 ^ 59
def prefixEnd_532723 : Nat := 4983230072969 + 3 ^ 40 * 532723 * 2
def baseEnd_532723 : Nat := 182361969803482968341705

theorem tailTrace_532723 : CollatzResearch.WordTrace tailWord_532723 prefixEnd_532723 182361969803482968341705 := by
  unfold tailWord_532723
  simp only [CollatzResearch.WordTrace]
  refine ⟨19430004049043027690074823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12953336032695351793383215 19430004049043027690074823)
  ·
    refine ⟨29145006073564541535112235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19430004049043027690074823 29145006073564541535112235)
    ·
      refine ⟨43717509110346812302668353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29145006073564541535112235 43717509110346812302668353)
      ·
        refine ⟨32788131832760109227001265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43717509110346812302668353 32788131832760109227001265)
        ·
          refine ⟨24591098874570081920250949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32788131832760109227001265 24591098874570081920250949)
          ·
            refine ⟨4610831038981890360047053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24591098874570081920250949 4610831038981890360047053)
            ·
              refine ⟨1729061639618208885017645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4610831038981890360047053 1729061639618208885017645)
              ·
                refine ⟨648398114856828331881617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1729061639618208885017645 648398114856828331881617)
                ·
                  refine ⟨486298586142621248911213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648398114856828331881617 486298586142621248911213)
                  ·
                    refine ⟨182361969803482968341705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486298586142621248911213 182361969803482968341705)
                    ·
                      rfl

theorem cell22_532723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 3].length) (baseStart_532723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532723 prefixEnd_532723 := by exact prefixLift 532723
  have htrace : WordTrace (prefixWord ++ tailWord_532723) baseStart_532723 baseEnd_532723 := by
    simpa [prefixWord, tailWord_532723, baseEnd_532723] using wordTrace_append hprefix tailTrace_532723
  have hstable : (prefixWord ++ tailWord_532723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532723).length < 2 ^ (prefixWord ++ tailWord_532723).sum := by decide
  have hdescent : baseEnd_532723 < baseStart_532723 := by decide
  rcases family_descends (prefixWord ++ tailWord_532723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532785 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_532785 : Nat := 118140960795 + 532785 * 2 ^ 59
def prefixEnd_532785 : Nat := 4983230072969 + 3 ^ 40 * 532785 * 2
def baseEnd_532785 : Nat := 182383193670535473291515

theorem tailTrace_532785 : CollatzResearch.WordTrace tailWord_532785 prefixEnd_532785 182383193670535473291515 := by
  unfold tailWord_532785
  simp only [CollatzResearch.WordTrace]
  refine ⟨19432265374818412278831809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12954843583212274852554539 19432265374818412278831809)
  ·
    refine ⟨14574199031113809209123857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19432265374818412278831809 14574199031113809209123857)
    ·
      refine ⟨10930649273335356906842893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14574199031113809209123857 10930649273335356906842893)
      ·
        refine ⟨4098993477500758840066085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10930649273335356906842893 4098993477500758840066085)
        ·
          refine ⟨768561277031392282512391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4098993477500758840066085 768561277031392282512391)
          ·
            refine ⟨1152841915547088423768587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768561277031392282512391 1152841915547088423768587)
            ·
              refine ⟨1729262873320632635652881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152841915547088423768587 1729262873320632635652881)
              ·
                refine ⟨1296947154990474476739661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729262873320632635652881 1296947154990474476739661)
                ·
                  refine ⟨486355183121427928777373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1296947154990474476739661 486355183121427928777373)
                  ·
                    refine ⟨182383193670535473291515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486355183121427928777373 182383193670535473291515)
                    ·
                      rfl

theorem cell22_532785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_532785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532785 prefixEnd_532785 := by exact prefixLift 532785
  have htrace : WordTrace (prefixWord ++ tailWord_532785) baseStart_532785 baseEnd_532785 := by
    simpa [prefixWord, tailWord_532785, baseEnd_532785] using wordTrace_append hprefix tailTrace_532785
  have hstable : (prefixWord ++ tailWord_532785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532785).length < 2 ^ (prefixWord ++ tailWord_532785).sum := by decide
  have hdescent : baseEnd_532785 < baseStart_532785 := by decide
  rcases family_descends (prefixWord ++ tailWord_532785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532796 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_532796 : Nat := 118140960795 + 532796 * 2 ^ 59
def prefixEnd_532796 : Nat := 4983230072969 + 3 ^ 40 * 532796 * 2
def baseEnd_532796 : Nat := 182386959195335111266481

theorem tailTrace_532796 : CollatzResearch.WordTrace tailWord_532796 prefixEnd_532796 182386959195335111266481 := by
  unfold tailWord_532796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9716333288889280578741121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12955111051852374104988161 9716333288889280578741121)
  ·
    refine ⟨7287249966666960434055841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9716333288889280578741121 7287249966666960434055841)
    ·
      refine ⟨5465437475000220325541881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7287249966666960434055841 5465437475000220325541881)
      ·
        refine ⟨4099078106250165244156411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465437475000220325541881 4099078106250165244156411)
        ·
          refine ⟨6148617159375247866234617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099078106250165244156411 6148617159375247866234617)
          ·
            refine ⟨4611462869531435899675963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6148617159375247866234617 4611462869531435899675963)
            ·
              refine ⟨6917194304297153849513945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611462869531435899675963 6917194304297153849513945)
              ·
                refine ⟨5187895728222865387135459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6917194304297153849513945 5187895728222865387135459)
                ·
                  refine ⟨7781843592334298080703189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187895728222865387135459 7781843592334298080703189)
                  ·
                    refine ⟨182386959195335111266481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7781843592334298080703189 182386959195335111266481)
                    ·
                      rfl

theorem cell22_532796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_532796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532796 prefixEnd_532796 := by exact prefixLift 532796
  have htrace : WordTrace (prefixWord ++ tailWord_532796) baseStart_532796 baseEnd_532796 := by
    simpa [prefixWord, tailWord_532796, baseEnd_532796] using wordTrace_append hprefix tailTrace_532796
  have hstable : (prefixWord ++ tailWord_532796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532796).length < 2 ^ (prefixWord ++ tailWord_532796).sum := by decide
  have hdescent : baseEnd_532796 < baseStart_532796 := by decide
  rcases family_descends (prefixWord ++ tailWord_532796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_532811 : Nat := 118140960795 + 532811 * 2 ^ 59
def prefixEnd_532811 : Nat := 4983230072969 + 3 ^ 40 * 532811 * 2
def baseEnd_532811 : Nat := 182392094001880072141435

theorem tailTrace_532811 : CollatzResearch.WordTrace tailWord_532811 prefixEnd_532811 182392094001880072141435 := by
  unfold tailWord_532811
  simp only [CollatzResearch.WordTrace]
  refine ⟨19433213672724218719278287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12955475781816145812852191 19433213672724218719278287)
  ·
    refine ⟨29149820509086328078917431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19433213672724218719278287 29149820509086328078917431)
    ·
      refine ⟨43724730763629492118376147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29149820509086328078917431 43724730763629492118376147)
      ·
        refine ⟨65587096145444238177564221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43724730763629492118376147 65587096145444238177564221)
        ·
          refine ⟨24595161054541589316586583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65587096145444238177564221 24595161054541589316586583)
          ·
            refine ⟨36892741581812383974879875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24595161054541589316586583 36892741581812383974879875)
            ·
              refine ⟨55339112372718575962319813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36892741581812383974879875 55339112372718575962319813)
              ·
                refine ⟨10376083569884732992934965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55339112372718575962319813 10376083569884732992934965)
                ·
                  refine ⟨972757834676693718087653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10376083569884732992934965 972757834676693718087653)
                  ·
                    refine ⟨182392094001880072141435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972757834676693718087653 182392094001880072141435)
                    ·
                      rfl

theorem cell22_532811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_532811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532811 prefixEnd_532811 := by exact prefixLift 532811
  have htrace : WordTrace (prefixWord ++ tailWord_532811) baseStart_532811 baseEnd_532811 := by
    simpa [prefixWord, tailWord_532811, baseEnd_532811] using wordTrace_append hprefix tailTrace_532811
  have hstable : (prefixWord ++ tailWord_532811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532811).length < 2 ^ (prefixWord ++ tailWord_532811).sum := by decide
  have hdescent : baseEnd_532811 < baseStart_532811 := by decide
  rcases family_descends (prefixWord ++ tailWord_532811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532845 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_532845 : Nat := 118140960795 + 532845 * 2 ^ 59
def prefixEnd_532845 : Nat := 4983230072969 + 3 ^ 40 * 532845 * 2
def baseEnd_532845 : Nat := 182403732896715316791331

theorem tailTrace_532845 : CollatzResearch.WordTrace tailWord_532845 prefixEnd_532845 182403732896715316791331 := by
  unfold tailWord_532845
  simp only [CollatzResearch.WordTrace]
  refine ⟨19434453754601042526015989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12956302503067361684010659 19434453754601042526015989)
  ·
    refine ⟨1821980039493847736813999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19434453754601042526015989 1821980039493847736813999)
    ·
      refine ⟨2732970059240771605220999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821980039493847736813999 2732970059240771605220999)
      ·
        refine ⟨4099455088861157407831499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732970059240771605220999 4099455088861157407831499)
        ·
          refine ⟨6149182633291736111747249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4099455088861157407831499 6149182633291736111747249)
          ·
            refine ⟨4611886974968802083810437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6149182633291736111747249 4611886974968802083810437)
            ·
              refine ⟨864728807806650390714457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4611886974968802083810437 864728807806650390714457)
              ·
                refine ⟨648546605854987793035843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864728807806650390714457 648546605854987793035843)
                ·
                  refine ⟨972819908782481689553765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648546605854987793035843 972819908782481689553765)
                  ·
                    refine ⟨182403732896715316791331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972819908782481689553765 182403732896715316791331)
                    ·
                      rfl

theorem cell22_532845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_532845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532845 prefixEnd_532845 := by exact prefixLift 532845
  have htrace : WordTrace (prefixWord ++ tailWord_532845) baseStart_532845 baseEnd_532845 := by
    simpa [prefixWord, tailWord_532845, baseEnd_532845] using wordTrace_append hprefix tailTrace_532845
  have hstable : (prefixWord ++ tailWord_532845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532845).length < 2 ^ (prefixWord ++ tailWord_532845).sum := by decide
  have hdescent : baseEnd_532845 < baseStart_532845 := by decide
  rcases family_descends (prefixWord ++ tailWord_532845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532873 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_532873 : Nat := 118140960795 + 532873 * 2 ^ 59
def prefixEnd_532873 : Nat := 4983230072969 + 3 ^ 40 * 532873 * 2
def baseEnd_532873 : Nat := 182413317868932577091245

theorem tailTrace_532873 : CollatzResearch.WordTrace tailWord_532873 prefixEnd_532873 182413317868932577091245 := by
  unfold tailWord_532873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19435474998499603308035273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12956983332333068872023515 19435474998499603308035273)
  ·
    refine ⟨14576606248874702481026455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19435474998499603308035273 14576606248874702481026455)
    ·
      refine ⟨21864909373312053721539683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14576606248874702481026455 21864909373312053721539683)
      ·
        refine ⟨32797364059968080582309525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21864909373312053721539683 32797364059968080582309525)
        ·
          refine ⟨1537376440311003777295759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32797364059968080582309525 1537376440311003777295759)
          ·
            refine ⟨2306064660466505665943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537376440311003777295759 2306064660466505665943639)
            ·
              refine ⟨3459096990699758498915459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306064660466505665943639 3459096990699758498915459)
              ·
                refine ⟨5188645486049637748373189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459096990699758498915459 5188645486049637748373189)
                ·
                  refine ⟨972871028634307077819973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5188645486049637748373189 972871028634307077819973)
                  ·
                    refine ⟨182413317868932577091245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972871028634307077819973 182413317868932577091245)
                    ·
                      rfl

theorem cell22_532873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_532873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532873 prefixEnd_532873 := by exact prefixLift 532873
  have htrace : WordTrace (prefixWord ++ tailWord_532873) baseStart_532873 baseEnd_532873 := by
    simpa [prefixWord, tailWord_532873, baseEnd_532873] using wordTrace_append hprefix tailTrace_532873
  have hstable : (prefixWord ++ tailWord_532873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532873).length < 2 ^ (prefixWord ++ tailWord_532873).sum := by decide
  have hdescent : baseEnd_532873 < baseStart_532873 := by decide
  rcases family_descends (prefixWord ++ tailWord_532873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532888 : List Nat := [2, 1, 2, 5, 1, 1, 1, 9]
def baseStart_532888 : Nat := 118140960795 + 532888 * 2 ^ 59
def prefixEnd_532888 : Nat := 4983230072969 + 3 ^ 40 * 532888 * 2
def baseEnd_532888 : Nat := 20268716963941948662911

theorem tailTrace_532888 : CollatzResearch.WordTrace tailWord_532888 prefixEnd_532888 20268716963941948662911 := by
  unfold tailWord_532888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718011046722630434915659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12957348062296840579887545 9718011046722630434915659)
  ·
    refine ⟨14577016570083945652373489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9718011046722630434915659 14577016570083945652373489)
    ·
      refine ⟨10932762427562959239280117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14577016570083945652373489 10932762427562959239280117)
      ·
        refine ⟨1024946477584027428682511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10932762427562959239280117 1024946477584027428682511)
        ·
          refine ⟨1537419716376041143023767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024946477584027428682511 1537419716376041143023767)
          ·
            refine ⟨2306129574564061714535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537419716376041143023767 2306129574564061714535651)
            ·
              refine ⟨3459194361846092571803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2306129574564061714535651 3459194361846092571803477)
              ·
                refine ⟨20268716963941948662911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3459194361846092571803477 20268716963941948662911)
                ·
                  rfl

theorem cell22_532888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_532888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532888 prefixEnd_532888 := by exact prefixLift 532888
  have htrace : WordTrace (prefixWord ++ tailWord_532888) baseStart_532888 baseEnd_532888 := by
    simpa [prefixWord, tailWord_532888, baseEnd_532888] using wordTrace_append hprefix tailTrace_532888
  have hstable : (prefixWord ++ tailWord_532888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532888).length < 2 ^ (prefixWord ++ tailWord_532888).sum := by decide
  have hdescent : baseEnd_532888 < baseStart_532888 := by decide
  rcases family_descends (prefixWord ++ tailWord_532888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532995 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 4]
def baseStart_532995 : Nat := 118140960795 + 532995 * 2 ^ 59
def prefixEnd_532995 : Nat := 4983230072969 + 3 ^ 40 * 532995 * 2
def baseEnd_532995 : Nat := 60818360320721641846957

theorem tailTrace_532995 : CollatzResearch.WordTrace tailWord_532995 prefixEnd_532995 60818360320721641846957 := by
  unfold tailWord_532995
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439924704057618143976439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959949802705078762650959 19439924704057618143976439)
  ·
    refine ⟨29159887056086427215964659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19439924704057618143976439 29159887056086427215964659)
    ·
      refine ⟨43739830584129640823946989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29159887056086427215964659 43739830584129640823946989)
      ·
        refine ⟨16402436469048615308980121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43739830584129640823946989 16402436469048615308980121)
        ·
          refine ⟨12301827351786461481735091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16402436469048615308980121 12301827351786461481735091)
          ·
            refine ⟨18452741027679692222602637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12301827351786461481735091 18452741027679692222602637)
            ·
              refine ⟨6919777885379884583475989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18452741027679692222602637 6919777885379884583475989)
              ·
                refine ⟨324364588377182089850437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6919777885379884583475989 324364588377182089850437)
                ·
                  refine ⟨60818360320721641846957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324364588377182089850437 60818360320721641846957)
                  ·
                    rfl

theorem cell22_532995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 4].length) (baseStart_532995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_532995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_532995 prefixEnd_532995 := by exact prefixLift 532995
  have htrace : WordTrace (prefixWord ++ tailWord_532995) baseStart_532995 baseEnd_532995 := by
    simpa [prefixWord, tailWord_532995, baseEnd_532995] using wordTrace_append hprefix tailTrace_532995
  have hstable : (prefixWord ++ tailWord_532995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532995).length < 2 ^ (prefixWord ++ tailWord_532995).sum := by decide
  have hdescent : baseEnd_532995 < baseStart_532995 := by decide
  rcases family_descends (prefixWord ++ tailWord_532995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533012 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_533012 : Nat := 118140960795 + 533012 * 2 ^ 59
def prefixEnd_533012 : Nat := 4983230072969 + 3 ^ 40 * 533012 * 2
def baseEnd_533012 : Nat := 60820300136527515955273

theorem tailTrace_533012 : CollatzResearch.WordTrace tailWord_533012 prefixEnd_533012 60820300136527515955273 := by
  unfold tailWord_533012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720272372498015023672645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12960363163330686698230193 9720272372498015023672645)
  ·
    refine ⟨1822551069843377816938621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9720272372498015023672645 1822551069843377816938621)
    ·
      refine ⟨683456651191266681351983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1822551069843377816938621 683456651191266681351983)
      ·
        refine ⟨1025184976786900022027975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683456651191266681351983 1025184976786900022027975)
        ·
          refine ⟨1537777465180350033041963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025184976786900022027975 1537777465180350033041963)
          ·
            refine ⟨2306666197770525049562945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537777465180350033041963 2306666197770525049562945)
            ·
              refine ⟨1729999648327893787172209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306666197770525049562945 1729999648327893787172209)
              ·
                refine ⟨1297499736245920340379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729999648327893787172209 1297499736245920340379157)
                ·
                  refine ⟨60820300136527515955273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1297499736245920340379157 60820300136527515955273)
                  ·
                    rfl

theorem cell22_533012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_533012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533012 prefixEnd_533012 := by exact prefixLift 533012
  have htrace : WordTrace (prefixWord ++ tailWord_533012) baseStart_533012 baseEnd_533012 := by
    simpa [prefixWord, tailWord_533012, baseEnd_533012] using wordTrace_append hprefix tailTrace_533012
  have hstable : (prefixWord ++ tailWord_533012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533012).length < 2 ^ (prefixWord ++ tailWord_533012).sum := by decide
  have hdescent : baseEnd_533012 < baseStart_533012 := by decide
  rcases family_descends (prefixWord ++ tailWord_533012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533025 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_533025 : Nat := 118140960795 + 533025 * 2 ^ 59
def prefixEnd_533025 : Nat := 4983230072969 + 3 ^ 40 * 533025 * 2
def baseEnd_533025 : Nat := 182465350575254847290779

theorem tailTrace_533025 : CollatzResearch.WordTrace tailWord_533025 prefixEnd_533025 182465350575254847290779 := by
  unfold tailWord_533025
  simp only [CollatzResearch.WordTrace]
  refine ⟨19441018893948933267568529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12960679262632622178379019 19441018893948933267568529)
  ·
    refine ⟨14580764170461699950676397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19441018893948933267568529 14580764170461699950676397)
    ·
      refine ⟨5467786563923137481503649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14580764170461699950676397 5467786563923137481503649)
      ·
        refine ⟨4100839922942353111127737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5467786563923137481503649 4100839922942353111127737)
        ·
          refine ⟨3075629942206764833345803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4100839922942353111127737 3075629942206764833345803)
          ·
            refine ⟨4613444913310147250018705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075629942206764833345803 4613444913310147250018705)
            ·
              refine ⟨3460083684982610437514029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4613444913310147250018705 3460083684982610437514029)
              ·
                refine ⟨1297531381868478914067761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3460083684982610437514029 1297531381868478914067761)
                ·
                  refine ⟨973148536401359185550821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297531381868478914067761 973148536401359185550821)
                  ·
                    refine ⟨182465350575254847290779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 973148536401359185550821 182465350575254847290779)
                    ·
                      rfl

theorem cell22_533025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_533025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533025 prefixEnd_533025 := by exact prefixLift 533025
  have htrace : WordTrace (prefixWord ++ tailWord_533025) baseStart_533025 baseEnd_533025 := by
    simpa [prefixWord, tailWord_533025, baseEnd_533025] using wordTrace_append hprefix tailTrace_533025
  have hstable : (prefixWord ++ tailWord_533025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533025).length < 2 ^ (prefixWord ++ tailWord_533025).sum := by decide
  have hdescent : baseEnd_533025 < baseStart_533025 := by decide
  rcases family_descends (prefixWord ++ tailWord_533025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533046 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_533046 : Nat := 118140960795 + 533046 * 2 ^ 59
def prefixEnd_533046 : Nat := 4983230072969 + 3 ^ 40 * 533046 * 2
def baseEnd_533046 : Nat := 60824179768139264171905

theorem tailTrace_533046 : CollatzResearch.WordTrace tailWord_533046 prefixEnd_533046 60824179768139264171905 := by
  unfold tailWord_533046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215111551679553365880187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12961189884581902569388661 1215111551679553365880187)
  ·
    refine ⟨1822667327519330048820281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215111551679553365880187 1822667327519330048820281)
    ·
      refine ⟨1367000495639497536615211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822667327519330048820281 1367000495639497536615211)
      ·
        refine ⟨2050500743459246304922817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367000495639497536615211 2050500743459246304922817)
        ·
          refine ⟨1537875557594434728692113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050500743459246304922817 1537875557594434728692113)
          ·
            refine ⟨1153406668195826046519085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537875557594434728692113 1153406668195826046519085)
            ·
              refine ⟨432527500573434767444657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153406668195826046519085 432527500573434767444657)
              ·
                refine ⟨324395625430076075583493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432527500573434767444657 324395625430076075583493)
                ·
                  refine ⟨60824179768139264171905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324395625430076075583493 60824179768139264171905)
                  ·
                    rfl

theorem cell22_533046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_533046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533046 prefixEnd_533046 := by exact prefixLift 533046
  have htrace : WordTrace (prefixWord ++ tailWord_533046) baseStart_533046 baseEnd_533046 := by
    simpa [prefixWord, tailWord_533046, baseEnd_533046] using wordTrace_append hprefix tailTrace_533046
  have hstable : (prefixWord ++ tailWord_533046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533046).length < 2 ^ (prefixWord ++ tailWord_533046).sum := by decide
  have hdescent : baseEnd_533046 < baseStart_533046 := by decide
  rcases family_descends (prefixWord ++ tailWord_533046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533102 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_533102 : Nat := 118140960795 + 533102 * 2 ^ 59
def prefixEnd_533102 : Nat := 4983230072969 + 3 ^ 40 * 533102 * 2
def baseEnd_533102 : Nat := 60830569749617437705181

theorem tailTrace_533102 : CollatzResearch.WordTrace tailWord_533102 prefixEnd_533102 60830569749617437705181 := by
  unfold tailWord_533102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430478414333746927265195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12962551543113316945414373 2430478414333746927265195)
  ·
    refine ⟨3645717621500620390897793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2430478414333746927265195 3645717621500620390897793)
    ·
      refine ⟨2734288216125465293173345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3645717621500620390897793 2734288216125465293173345)
      ·
        refine ⟨2050716162094098969880009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734288216125465293173345 2050716162094098969880009)
        ·
          refine ⟨1538037121570574227410007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050716162094098969880009 1538037121570574227410007)
          ·
            refine ⟨2307055682355861341115011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538037121570574227410007 2307055682355861341115011)
            ·
              refine ⟨3460583523533792011672517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307055682355861341115011 3460583523533792011672517)
              ·
                refine ⟨648859410662586002188597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3460583523533792011672517 648859410662586002188597)
                ·
                  refine ⟨60830569749617437705181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 648859410662586002188597 60830569749617437705181)
                  ·
                    rfl

theorem cell22_533102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_533102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533102 prefixEnd_533102 := by exact prefixLift 533102
  have htrace : WordTrace (prefixWord ++ tailWord_533102) baseStart_533102 baseEnd_533102 := by
    simpa [prefixWord, tailWord_533102, baseEnd_533102] using wordTrace_append hprefix tailTrace_533102
  have hstable : (prefixWord ++ tailWord_533102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533102).length < 2 ^ (prefixWord ++ tailWord_533102).sum := by decide
  have hdescent : baseEnd_533102 < baseStart_533102 := by decide
  rcases family_descends (prefixWord ++ tailWord_533102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533106 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_533106 : Nat := 118140960795 + 533106 * 2 ^ 59
def prefixEnd_533106 : Nat := 4983230072969 + 3 ^ 40 * 533106 * 2
def baseEnd_533106 : Nat := 182493078530597636015531

theorem tailTrace_533106 : CollatzResearch.WordTrace tailWord_533106 prefixEnd_533106 182493078530597636015531 := by
  unfold tailWord_533106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860993301663871025316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12962648804436989400844781 4860993301663871025316793)
  ·
    refine ⟨3645744976247903268987595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4860993301663871025316793 3645744976247903268987595)
    ·
      refine ⟨5468617464371854903481393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645744976247903268987595 5468617464371854903481393)
      ·
        refine ⟨4101463098278891177611045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5468617464371854903481393 4101463098278891177611045)
        ·
          refine ⟨769024330927292095802071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4101463098278891177611045 769024330927292095802071)
          ·
            refine ⟨1153536496390938143703107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769024330927292095802071 1153536496390938143703107)
            ·
              refine ⟨1730304744586407215554661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153536496390938143703107 1730304744586407215554661)
              ·
                refine ⟨324432139609951352916499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1730304744586407215554661 324432139609951352916499)
                ·
                  refine ⟨486648209414927029374749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324432139609951352916499 486648209414927029374749)
                  ·
                    refine ⟨182493078530597636015531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486648209414927029374749 182493078530597636015531)
                    ·
                      rfl

theorem cell22_533106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_533106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533106 prefixEnd_533106 := by exact prefixLift 533106
  have htrace : WordTrace (prefixWord ++ tailWord_533106) baseStart_533106 baseEnd_533106 := by
    simpa [prefixWord, tailWord_533106, baseEnd_533106] using wordTrace_append hprefix tailTrace_533106
  have hstable : (prefixWord ++ tailWord_533106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533106).length < 2 ^ (prefixWord ++ tailWord_533106).sum := by decide
  have hdescent : baseEnd_533106 < baseStart_533106 := by decide
  rcases family_descends (prefixWord ++ tailWord_533106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533117 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_533117 : Nat := 118140960795 + 533117 * 2 ^ 59
def prefixEnd_533117 : Nat := 4983230072969 + 3 ^ 40 * 533117 * 2
def baseEnd_533117 : Nat := 182496844055397273990497

theorem tailTrace_533117 : CollatzResearch.WordTrace tailWord_533117 prefixEnd_533117 182496844055397273990497 := by
  unfold tailWord_533117
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444374409615632979917605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12962916273077088653278403 19444374409615632979917605)
  ·
    refine ⟨3645820201802931183734551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19444374409615632979917605 3645820201802931183734551)
    ·
      refine ⟨5468730302704396775601827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645820201802931183734551 5468730302704396775601827)
      ·
        refine ⟨8203095454056595163402741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468730302704396775601827 8203095454056595163402741)
        ·
          refine ⟨769040198817805796569007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8203095454056595163402741 769040198817805796569007)
          ·
            refine ⟨1153560298226708694853511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769040198817805796569007 1153560298226708694853511)
            ·
              refine ⟨1730340447340063042280267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153560298226708694853511 1730340447340063042280267)
              ·
                refine ⟨2595510671010094563420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730340447340063042280267 2595510671010094563420401)
                ·
                  refine ⟨1946633003257570922565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2595510671010094563420401 1946633003257570922565301)
                  ·
                    refine ⟨182496844055397273990497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1946633003257570922565301 182496844055397273990497)
                    ·
                      rfl

theorem cell22_533117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_533117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533117 prefixEnd_533117 := by exact prefixLift 533117
  have htrace : WordTrace (prefixWord ++ tailWord_533117) baseStart_533117 baseEnd_533117 := by
    simpa [prefixWord, tailWord_533117, baseEnd_533117] using wordTrace_append hprefix tailTrace_533117
  have hstable : (prefixWord ++ tailWord_533117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533117).length < 2 ^ (prefixWord ++ tailWord_533117).sum := by decide
  have hdescent : baseEnd_533117 < baseStart_533117 := by decide
  rcases family_descends (prefixWord ++ tailWord_533117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533145 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_533145 : Nat := 118140960795 + 533145 * 2 ^ 59
def prefixEnd_533145 : Nat := 4983230072969 + 3 ^ 40 * 533145 * 2
def baseEnd_533145 : Nat := 182506429027614534290411

theorem tailTrace_533145 : CollatzResearch.WordTrace tailWord_533145 prefixEnd_533145 182506429027614534290411 := by
  unfold tailWord_533145
  simp only [CollatzResearch.WordTrace]
  refine ⟨19445395653514193761936889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12963597102342795841291259 19445395653514193761936889)
  ·
    refine ⟨14584046740135645321452667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19445395653514193761936889 14584046740135645321452667)
    ·
      refine ⟨21876070110203467982179001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14584046740135645321452667 21876070110203467982179001)
      ·
        refine ⟨16407052582652600986634251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21876070110203467982179001 16407052582652600986634251)
        ·
          refine ⟨24610578873978901479951377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16407052582652600986634251 24610578873978901479951377)
          ·
            refine ⟨18457934155484176109963533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24610578873978901479951377 18457934155484176109963533)
            ·
              refine ⟨6921725308306566041236325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18457934155484176109963533 6921725308306566041236325)
              ·
                refine ⟨1297823495307481132731811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6921725308306566041236325 1297823495307481132731811)
                ·
                  refine ⟨1946735242961221699097717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297823495307481132731811 1946735242961221699097717)
                  ·
                    refine ⟨182506429027614534290411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1946735242961221699097717 182506429027614534290411)
                    ·
                      rfl

theorem cell22_533145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_533145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533145 prefixEnd_533145 := by exact prefixLift 533145
  have htrace : WordTrace (prefixWord ++ tailWord_533145) baseStart_533145 baseEnd_533145 := by
    simpa [prefixWord, tailWord_533145, baseEnd_533145] using wordTrace_append hprefix tailTrace_533145
  have hstable : (prefixWord ++ tailWord_533145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533145).length < 2 ^ (prefixWord ++ tailWord_533145).sum := by decide
  have hdescent : baseEnd_533145 < baseStart_533145 := by decide
  rcases family_descends (prefixWord ++ tailWord_533145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533149 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_533149 : Nat := 118140960795 + 533149 * 2 ^ 59
def prefixEnd_533149 : Nat := 4983230072969 + 3 ^ 40 * 533149 * 2
def baseEnd_533149 : Nat := 182507798309359857190399

theorem tailTrace_533149 : CollatzResearch.WordTrace tailWord_533149 prefixEnd_533149 182507798309359857190399 := by
  unfold tailWord_533149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19445541545499702445082501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12963694363666468296721667 19445541545499702445082501)
  ·
    refine ⟨3646039039781194208452969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19445541545499702445082501 3646039039781194208452969)
    ·
      refine ⟨2734529279835895656339727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3646039039781194208452969 2734529279835895656339727)
      ·
        refine ⟨4101793919753843484509591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734529279835895656339727 4101793919753843484509591)
        ·
          refine ⟨6152690879630765226764387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4101793919753843484509591 6152690879630765226764387)
          ·
            refine ⟨9229036319446147840146581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152690879630765226764387 9229036319446147840146581)
            ·
              refine ⟨432611077474038180006871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9229036319446147840146581 432611077474038180006871)
              ·
                refine ⟨648916616211057270010307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432611077474038180006871 648916616211057270010307)
                ·
                  refine ⟨973374924316585905015461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648916616211057270010307 973374924316585905015461)
                  ·
                    refine ⟨182507798309359857190399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 973374924316585905015461 182507798309359857190399)
                    ·
                      rfl

theorem cell22_533149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_533149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533149 prefixEnd_533149 := by exact prefixLift 533149
  have htrace : WordTrace (prefixWord ++ tailWord_533149) baseStart_533149 baseEnd_533149 := by
    simpa [prefixWord, tailWord_533149, baseEnd_533149] using wordTrace_append hprefix tailTrace_533149
  have hstable : (prefixWord ++ tailWord_533149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533149).length < 2 ^ (prefixWord ++ tailWord_533149).sum := by decide
  have hdescent : baseEnd_533149 < baseStart_533149 := by decide
  rcases family_descends (prefixWord ++ tailWord_533149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533192 : List Nat := [2, 1, 3, 1, 2, 3, 4, 6]
def baseStart_533192 : Nat := 118140960795 + 533192 * 2 ^ 59
def prefixEnd_533192 : Nat := 4983230072969 + 3 ^ 40 * 533192 * 2
def baseEnd_533192 : Nat := 20280279787569119818363

theorem tailTrace_533192 : CollatzResearch.WordTrace tailWord_533192 prefixEnd_533192 20280279787569119818363 := by
  unfold tailWord_533192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723554942171960394448915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12964739922895947192598553 9723554942171960394448915)
  ·
    refine ⟨14585332413257940591673373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723554942171960394448915 14585332413257940591673373)
    ·
      refine ⟨5469499654971727721877515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14585332413257940591673373 5469499654971727721877515)
      ·
        refine ⟨8204249482457591582816273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469499654971727721877515 8204249482457591582816273)
        ·
          refine ⟨6153187111843193687112205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8204249482457591582816273 6153187111843193687112205)
          ·
            refine ⟨2307445166941197632667077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6153187111843193687112205 2307445166941197632667077)
            ·
              refine ⟨432645968801474556125077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2307445166941197632667077 432645968801474556125077)
              ·
                refine ⟨20280279787569119818363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432645968801474556125077 20280279787569119818363)
                ·
                  rfl

theorem cell22_533192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_533192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533192 prefixEnd_533192 := by exact prefixLift 533192
  have htrace : WordTrace (prefixWord ++ tailWord_533192) baseStart_533192 baseEnd_533192 := by
    simpa [prefixWord, tailWord_533192, baseEnd_533192] using wordTrace_append hprefix tailTrace_533192
  have hstable : (prefixWord ++ tailWord_533192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533192).length < 2 ^ (prefixWord ++ tailWord_533192).sum := by decide
  have hdescent : baseEnd_533192 < baseStart_533192 := by decide
  rcases family_descends (prefixWord ++ tailWord_533192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533235 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_533235 : Nat := 118140960795 + 533235 * 2 ^ 59
def prefixEnd_533235 : Nat := 4983230072969 + 3 ^ 40 * 533235 * 2
def baseEnd_533235 : Nat := 182537237866884299540135

theorem tailTrace_533235 : CollatzResearch.WordTrace tailWord_533235 prefixEnd_533235 182537237866884299540135 := by
  unfold tailWord_533235
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448678223188139132713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12965785482125426088475439 19448678223188139132713159)
  ·
    refine ⟨29173017334782208699069739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19448678223188139132713159 29173017334782208699069739)
    ·
      refine ⟨43759526002173313048604609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29173017334782208699069739 43759526002173313048604609)
      ·
        refine ⟨32819644501629984786453457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43759526002173313048604609 32819644501629984786453457)
        ·
          refine ⟨24614733376222488589840093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32819644501629984786453457 24614733376222488589840093)
          ·
            refine ⟨9230525016083433221190035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24614733376222488589840093 9230525016083433221190035)
            ·
              refine ⟨13845787524125149831785053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9230525016083433221190035 13845787524125149831785053)
              ·
                refine ⟨5192170321546931186919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13845787524125149831785053 5192170321546931186919395)
                ·
                  refine ⟨7788255482320396780379093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192170321546931186919395 7788255482320396780379093)
                  ·
                    refine ⟨182537237866884299540135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7788255482320396780379093 182537237866884299540135)
                    ·
                      rfl

theorem cell22_533235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_533235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533235 prefixEnd_533235 := by exact prefixLift 533235
  have htrace : WordTrace (prefixWord ++ tailWord_533235) baseStart_533235 baseEnd_533235 := by
    simpa [prefixWord, tailWord_533235, baseEnd_533235] using wordTrace_append hprefix tailTrace_533235
  have hstable : (prefixWord ++ tailWord_533235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533235).length < 2 ^ (prefixWord ++ tailWord_533235).sum := by decide
  have hdescent : baseEnd_533235 < baseStart_533235 := by decide
  rcases family_descends (prefixWord ++ tailWord_533235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533348 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_533348 : Nat := 118140960795 + 533348 * 2 ^ 59
def prefixEnd_533348 : Nat := 4983230072969 + 3 ^ 40 * 533348 * 2
def baseEnd_533348 : Nat := 182575920076189671464789

theorem tailTrace_533348 : CollatzResearch.WordTrace tailWord_533348 prefixEnd_533348 182575920076189671464789 := by
  unfold tailWord_533348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726399835889379715788349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12968533114519172954384465 9726399835889379715788349)
  ·
    refine ⟨3647399938458517393420631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9726399835889379715788349 3647399938458517393420631)
    ·
      refine ⟨5471099907687776090130947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647399938458517393420631 5471099907687776090130947)
      ·
        refine ⟨8206649861531664135196421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5471099907687776090130947 8206649861531664135196421)
        ·
          refine ⟨1538746849037187025349329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8206649861531664135196421 1538746849037187025349329)
          ·
            refine ⟨1154060136777890269011997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538746849037187025349329 1154060136777890269011997)
            ·
              refine ⟨432772551291708850879499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154060136777890269011997 432772551291708850879499)
              ·
                refine ⟨649158826937563276319249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432772551291708850879499 649158826937563276319249)
                ·
                  refine ⟨486869120203172457239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649158826937563276319249 486869120203172457239437)
                  ·
                    refine ⟨182575920076189671464789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486869120203172457239437 182575920076189671464789)
                    ·
                      rfl

theorem cell22_533348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_533348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533348 prefixEnd_533348 := by exact prefixLift 533348
  have htrace : WordTrace (prefixWord ++ tailWord_533348) baseStart_533348 baseEnd_533348 := by
    simpa [prefixWord, tailWord_533348, baseEnd_533348] using wordTrace_append hprefix tailTrace_533348
  have hstable : (prefixWord ++ tailWord_533348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533348).length < 2 ^ (prefixWord ++ tailWord_533348).sum := by decide
  have hdescent : baseEnd_533348 < baseStart_533348 := by decide
  rcases family_descends (prefixWord ++ tailWord_533348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533376 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 1, 3]
def baseStart_533376 : Nat := 118140960795 + 533376 * 2 ^ 59
def prefixEnd_533376 : Nat := 4983230072969 + 3 ^ 40 * 533376 * 2
def baseEnd_533376 : Nat := 182585505048406931764703

theorem tailTrace_533376 : CollatzResearch.WordTrace tailWord_533376 prefixEnd_533376 182585505048406931764703 := by
  unfold tailWord_533376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9726910457838660106797991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12969213943784880142397321 9726910457838660106797991)
  ·
    refine ⟨14590365686757990160196987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9726910457838660106797991 14590365686757990160196987)
    ·
      refine ⟨21885548530136985240295481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14590365686757990160196987 21885548530136985240295481)
      ·
        refine ⟨16414161397602738930221611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21885548530136985240295481 16414161397602738930221611)
        ·
          refine ⟨24621242096404108395332417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16414161397602738930221611 24621242096404108395332417)
          ·
            refine ⟨18465931572303081296499313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24621242096404108395332417 18465931572303081296499313)
            ·
              refine ⟨13849448679227310972374485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18465931572303081296499313 13849448679227310972374485)
              ·
                refine ⟨324596453419390100915027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13849448679227310972374485 324596453419390100915027)
                ·
                  refine ⟨486894680129085151372541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324596453419390100915027 486894680129085151372541)
                  ·
                    refine ⟨182585505048406931764703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486894680129085151372541 182585505048406931764703)
                    ·
                      rfl

theorem cell22_533376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_533376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533376 prefixEnd_533376 := by exact prefixLift 533376
  have htrace : WordTrace (prefixWord ++ tailWord_533376) baseStart_533376 baseEnd_533376 := by
    simpa [prefixWord, tailWord_533376, baseEnd_533376] using wordTrace_append hprefix tailTrace_533376
  have hstable : (prefixWord ++ tailWord_533376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533376).length < 2 ^ (prefixWord ++ tailWord_533376).sum := by decide
  have hdescent : baseEnd_533376 < baseStart_533376 := by decide
  rcases family_descends (prefixWord ++ tailWord_533376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533378 : List Nat := [3, 4, 2, 2, 1, 2, 8]
def baseStart_533378 : Nat := 118140960795 + 533378 * 2 ^ 59
def prefixEnd_533378 : Nat := 4983230072969 + 3 ^ 40 * 533378 * 2
def baseEnd_533378 : Nat := 6762451469973318267211

theorem tailTrace_533378 : CollatzResearch.WordTrace tailWord_533378 prefixEnd_533378 6762451469973318267211 := by
  unfold tailWord_533378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863473465417518638792197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12969262574446716370112525 4863473465417518638792197)
  ·
    refine ⟨911901274765784744773537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4863473465417518638792197 911901274765784744773537)
    ·
      refine ⟨683925956074338558580153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 911901274765784744773537 683925956074338558580153)
      ·
        refine ⟨512944467055753918935115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683925956074338558580153 512944467055753918935115)
        ·
          refine ⟨769416700583630878402673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512944467055753918935115 769416700583630878402673)
          ·
            refine ⟨577062525437723158802005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769416700583630878402673 577062525437723158802005)
            ·
              refine ⟨6762451469973318267211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 577062525437723158802005 6762451469973318267211)
              ·
                rfl

theorem cell22_533378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 8].length) (baseStart_533378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533378 prefixEnd_533378 := by exact prefixLift 533378
  have htrace : WordTrace (prefixWord ++ tailWord_533378) baseStart_533378 baseEnd_533378 := by
    simpa [prefixWord, tailWord_533378, baseEnd_533378] using wordTrace_append hprefix tailTrace_533378
  have hstable : (prefixWord ++ tailWord_533378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533378).length < 2 ^ (prefixWord ++ tailWord_533378).sum := by decide
  have hdescent : baseEnd_533378 < baseStart_533378 := by decide
  rcases family_descends (prefixWord ++ tailWord_533378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533387 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_533387 : Nat := 118140960795 + 533387 * 2 ^ 59
def prefixEnd_533387 : Nat := 4983230072969 + 3 ^ 40 * 533387 * 2
def baseEnd_533387 : Nat := 182589270573206569739669

theorem tailTrace_533387 : CollatzResearch.WordTrace tailWord_533387 prefixEnd_533387 182589270573206569739669 := by
  unfold tailWord_533387
  simp only [CollatzResearch.WordTrace]
  refine ⟨19454222118637469092246415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12969481412424979394830943 19454222118637469092246415)
  ·
    refine ⟨29181333177956203638369623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19454222118637469092246415 29181333177956203638369623)
    ·
      refine ⟨43771999766934305457554435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29181333177956203638369623 43771999766934305457554435)
      ·
        refine ⟨65657999650401458186331653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43771999766934305457554435 65657999650401458186331653)
        ·
          refine ⟨12310874934450273409937185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65657999650401458186331653 12310874934450273409937185)
          ·
            refine ⟨9233156200837705057452889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12310874934450273409937185 9233156200837705057452889)
            ·
              refine ⟨6924867150628278793089667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9233156200837705057452889 6924867150628278793089667)
              ·
                refine ⟨10387300725942418189634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6924867150628278793089667 10387300725942418189634501)
                ·
                  refine ⟨1947618886114203410556469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10387300725942418189634501 1947618886114203410556469)
                  ·
                    refine ⟨182589270573206569739669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1947618886114203410556469 182589270573206569739669)
                    ·
                      rfl

theorem cell22_533387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_533387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533387 prefixEnd_533387 := by exact prefixLift 533387
  have htrace : WordTrace (prefixWord ++ tailWord_533387) baseStart_533387 baseEnd_533387 := by
    simpa [prefixWord, tailWord_533387, baseEnd_533387] using wordTrace_append hprefix tailTrace_533387
  have hstable : (prefixWord ++ tailWord_533387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533387).length < 2 ^ (prefixWord ++ tailWord_533387).sum := by decide
  have hdescent : baseEnd_533387 < baseStart_533387 := by decide
  rcases family_descends (prefixWord ++ tailWord_533387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533417 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 8]
def baseStart_533417 : Nat := 118140960795 + 533417 * 2 ^ 59
def prefixEnd_533417 : Nat := 4983230072969 + 3 ^ 40 * 533417 * 2
def baseEnd_533417 : Nat := 60866513395432163829859

theorem tailTrace_533417 : CollatzResearch.WordTrace tailWord_533417 prefixEnd_533417 60866513395432163829859 := by
  unfold tailWord_533417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19455316308528784215838505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12970210872352522810559003 19455316308528784215838505)
  ·
    refine ⟨14591487231396588161878879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19455316308528784215838505 14591487231396588161878879)
    ·
      refine ⟨21887230847094882242818319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14591487231396588161878879 21887230847094882242818319)
      ·
        refine ⟨32830846270642323364227479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21887230847094882242818319 32830846270642323364227479)
        ·
          refine ⟨49246269405963485046341219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32830846270642323364227479 49246269405963485046341219)
          ·
            refine ⟨73869404108945227569511829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49246269405963485046341219 73869404108945227569511829)
            ·
              refine ⟨3462628317606807542320867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73869404108945227569511829 3462628317606807542320867)
              ·
                refine ⟨5193942476410211313481301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3462628317606807542320867 5193942476410211313481301)
                ·
                  refine ⟨60866513395432163829859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5193942476410211313481301 60866513395432163829859)
                  ·
                    rfl

theorem cell22_533417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_533417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533417 prefixEnd_533417 := by exact prefixLift 533417
  have htrace : WordTrace (prefixWord ++ tailWord_533417) baseStart_533417 baseEnd_533417 := by
    simpa [prefixWord, tailWord_533417, baseEnd_533417] using wordTrace_append hprefix tailTrace_533417
  have hstable : (prefixWord ++ tailWord_533417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533417).length < 2 ^ (prefixWord ++ tailWord_533417).sum := by decide
  have hdescent : baseEnd_533417 < baseStart_533417 := by decide
  rcases family_descends (prefixWord ++ tailWord_533417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533444 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_533444 : Nat := 118140960795 + 533444 * 2 ^ 59
def prefixEnd_533444 : Nat := 4983230072969 + 3 ^ 40 * 533444 * 2
def baseEnd_533444 : Nat := 182608782838077421064495

theorem tailTrace_533444 : CollatzResearch.WordTrace tailWord_533444 prefixEnd_533444 182608782838077421064495 := by
  unfold tailWord_533444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9728150539715483913535693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12970867386287311884714257 9728150539715483913535693)
  ·
    refine ⟨3648056452393306467575885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9728150539715483913535693 3648056452393306467575885)
    ·
      refine ⟨1368021169647489925340957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3648056452393306467575885 1368021169647489925340957)
      ·
        refine ⟨513007938617808722002859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1368021169647489925340957 513007938617808722002859)
        ·
          refine ⟨769511907926713083004289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513007938617808722002859 769511907926713083004289)
          ·
            refine ⟨577133930945034812253217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769511907926713083004289 577133930945034812253217)
            ·
              refine ⟨432850448208776109189913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577133930945034812253217 432850448208776109189913)
              ·
                refine ⟨324637836156582081892435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432850448208776109189913 324637836156582081892435)
                ·
                  refine ⟨486956754234873122838653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324637836156582081892435 486956754234873122838653)
                  ·
                    refine ⟨182608782838077421064495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486956754234873122838653 182608782838077421064495)
                    ·
                      rfl

theorem cell22_533444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_533444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533444 prefixEnd_533444 := by exact prefixLift 533444
  have htrace : WordTrace (prefixWord ++ tailWord_533444) baseStart_533444 baseEnd_533444 := by
    simpa [prefixWord, tailWord_533444, baseEnd_533444] using wordTrace_append hprefix tailTrace_533444
  have hstable : (prefixWord ++ tailWord_533444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533444).length < 2 ^ (prefixWord ++ tailWord_533444).sum := by decide
  have hdescent : baseEnd_533444 < baseStart_533444 := by decide
  rcases family_descends (prefixWord ++ tailWord_533444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533451 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 4]
def baseStart_533451 : Nat := 118140960795 + 533451 * 2 ^ 59
def prefixEnd_533451 : Nat := 4983230072969 + 3 ^ 40 * 533451 * 2
def baseEnd_533451 : Nat := 60870393027043912046491

theorem tailTrace_533451 : CollatzResearch.WordTrace tailWord_533451 prefixEnd_533451 60870393027043912046491 := by
  unfold tailWord_533451
  simp only [CollatzResearch.WordTrace]
  refine ⟨19456556390405608022576207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12971037593603738681717471 19456556390405608022576207)
  ·
    refine ⟨29184834585608412033864311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19456556390405608022576207 29184834585608412033864311)
    ·
      refine ⟨43777251878412618050796467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29184834585608412033864311 43777251878412618050796467)
      ·
        refine ⟨65665877817618927076194701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43777251878412618050796467 65665877817618927076194701)
        ·
          refine ⟨24624704181607097653573013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65665877817618927076194701 24624704181607097653573013)
          ·
            refine ⟨1154283008512832702511235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24624704181607097653573013 1154283008512832702511235)
            ·
              refine ⟨1731424512769249053766853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154283008512832702511235 1731424512769249053766853)
              ·
                refine ⟨324642096144234197581285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1731424512769249053766853 324642096144234197581285)
                ·
                  refine ⟨60870393027043912046491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324642096144234197581285 60870393027043912046491)
                  ·
                    rfl

theorem cell22_533451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 4].length) (baseStart_533451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533451 prefixEnd_533451 := by exact prefixLift 533451
  have htrace : WordTrace (prefixWord ++ tailWord_533451) baseStart_533451 baseEnd_533451 := by
    simpa [prefixWord, tailWord_533451, baseEnd_533451] using wordTrace_append hprefix tailTrace_533451
  have hstable : (prefixWord ++ tailWord_533451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533451).length < 2 ^ (prefixWord ++ tailWord_533451).sum := by decide
  have hdescent : baseEnd_533451 < baseStart_533451 := by decide
  rcases family_descends (prefixWord ++ tailWord_533451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533466 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_533466 : Nat := 118140960795 + 533466 * 2 ^ 59
def prefixEnd_533466 : Nat := 4983230072969 + 3 ^ 40 * 533466 * 2
def baseEnd_533466 : Nat := 182616313887676697014427

theorem tailTrace_533466 : CollatzResearch.WordTrace tailWord_533466 prefixEnd_533466 182616313887676697014427 := by
  unfold tailWord_533466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864275871337816396093063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12971402323567510389581501 4864275871337816396093063)
  ·
    refine ⟨7296413807006724594139595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864275871337816396093063 7296413807006724594139595)
    ·
      refine ⟨10944620710510086891209393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7296413807006724594139595 10944620710510086891209393)
      ·
        refine ⟨8208465532882565168407045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10944620710510086891209393 8208465532882565168407045)
        ·
          refine ⟨1539087287415480969076321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8208465532882565168407045 1539087287415480969076321)
          ·
            refine ⟨1154315465561610726807241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539087287415480969076321 1154315465561610726807241)
            ·
              refine ⟨865736599171208045105431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154315465561610726807241 865736599171208045105431)
              ·
                refine ⟨1298604898756812067658147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865736599171208045105431 1298604898756812067658147)
                ·
                  refine ⟨1947907348135218101487221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298604898756812067658147 1947907348135218101487221)
                  ·
                    refine ⟨182616313887676697014427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1947907348135218101487221 182616313887676697014427)
                    ·
                      rfl

theorem cell22_533466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_533466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533466 prefixEnd_533466 := by exact prefixLift 533466
  have htrace : WordTrace (prefixWord ++ tailWord_533466) baseStart_533466 baseEnd_533466 := by
    simpa [prefixWord, tailWord_533466, baseEnd_533466] using wordTrace_append hprefix tailTrace_533466
  have hstable : (prefixWord ++ tailWord_533466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533466).length < 2 ^ (prefixWord ++ tailWord_533466).sum := by decide
  have hdescent : baseEnd_533466 < baseStart_533466 := by decide
  rcases family_descends (prefixWord ++ tailWord_533466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533584 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_533584 : Nat := 118140960795 + 533584 * 2 ^ 59
def prefixEnd_533584 : Nat := 4983230072969 + 3 ^ 40 * 533584 * 2
def baseEnd_533584 : Nat := 182656707699163722564065

theorem tailTrace_533584 : CollatzResearch.WordTrace tailWord_533584 prefixEnd_533584 182656707699163722564065 := by
  unfold tailWord_533584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730703649461885868583903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12974271532615847824778537 9730703649461885868583903)
  ·
    refine ⟨14596055474192828802875855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9730703649461885868583903 14596055474192828802875855)
    ·
      refine ⟨21894083211289243204313783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596055474192828802875855 21894083211289243204313783)
      ·
        refine ⟨32841124816933864806470675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21894083211289243204313783 32841124816933864806470675)
        ·
          refine ⟨49261687225400797209706013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32841124816933864806470675 49261687225400797209706013)
          ·
            refine ⟨18473132709525298953639755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49261687225400797209706013 18473132709525298953639755)
            ·
              refine ⟨27709699064287948430459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18473132709525298953639755 27709699064287948430459633)
              ·
                refine ⟨20782274298215961322844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27709699064287948430459633 20782274298215961322844725)
                ·
                  refine ⟨1948338215457746374016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20782274298215961322844725 1948338215457746374016693)
                  ·
                    refine ⟨182656707699163722564065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1948338215457746374016693 182656707699163722564065)
                    ·
                      rfl

theorem cell22_533584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_533584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533584 prefixEnd_533584 := by exact prefixLift 533584
  have htrace : WordTrace (prefixWord ++ tailWord_533584) baseStart_533584 baseEnd_533584 := by
    simpa [prefixWord, tailWord_533584, baseEnd_533584] using wordTrace_append hprefix tailTrace_533584
  have hstable : (prefixWord ++ tailWord_533584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533584).length < 2 ^ (prefixWord ++ tailWord_533584).sum := by decide
  have hdescent : baseEnd_533584 < baseStart_533584 := by decide
  rcases family_descends (prefixWord ++ tailWord_533584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533588 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_533588 : Nat := 118140960795 + 533588 * 2 ^ 59
def prefixEnd_533588 : Nat := 4983230072969 + 3 ^ 40 * 533588 * 2
def baseEnd_533588 : Nat := 182658076980909045464053

theorem tailTrace_533588 : CollatzResearch.WordTrace tailWord_533588 prefixEnd_533588 182658076980909045464053 := by
  unfold tailWord_533588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730776595454640210156709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12974368793939520280208945 9730776595454640210156709)
  ·
    refine ⟨1824520611647745039404383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9730776595454640210156709 1824520611647745039404383)
    ·
      refine ⟨2736780917471617559106575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824520611647745039404383 2736780917471617559106575)
      ·
        refine ⟨4105171376207426338659863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736780917471617559106575 4105171376207426338659863)
        ·
          refine ⟨6157757064311139507989795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105171376207426338659863 6157757064311139507989795)
          ·
            refine ⟨9236635596466709261984693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6157757064311139507989795 9236635596466709261984693)
            ·
              refine ⟨865934587168753993311065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9236635596466709261984693 865934587168753993311065)
              ·
                refine ⟨649450940376565494983299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865934587168753993311065 649450940376565494983299)
                ·
                  refine ⟨974176410564848242474949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649450940376565494983299 974176410564848242474949)
                  ·
                    refine ⟨182658076980909045464053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974176410564848242474949 182658076980909045464053)
                    ·
                      rfl

theorem cell22_533588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_533588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533588 prefixEnd_533588 := by exact prefixLift 533588
  have htrace : WordTrace (prefixWord ++ tailWord_533588) baseStart_533588 baseEnd_533588 := by
    simpa [prefixWord, tailWord_533588, baseEnd_533588] using wordTrace_append hprefix tailTrace_533588
  have hstable : (prefixWord ++ tailWord_533588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533588).length < 2 ^ (prefixWord ++ tailWord_533588).sum := by decide
  have hdescent : baseEnd_533588 < baseStart_533588 := by decide
  rcases family_descends (prefixWord ++ tailWord_533588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533601 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_533601 : Nat := 118140960795 + 533601 * 2 ^ 59
def prefixEnd_533601 : Nat := 4983230072969 + 3 ^ 40 * 533601 * 2
def baseEnd_533601 : Nat := 182662527146581344889013

theorem tailTrace_533601 : CollatzResearch.WordTrace tailWord_533601 prefixEnd_533601 182662527146581344889013 := by
  unfold tailWord_533601
  simp only [CollatzResearch.WordTrace]
  refine ⟨19462027339862183640536657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12974684893241455760357771 19462027339862183640536657)
  ·
    refine ⟨14596520504896637730402493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19462027339862183640536657 14596520504896637730402493)
    ·
      refine ⟨5473695189336239148900935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14596520504896637730402493 5473695189336239148900935)
      ·
        refine ⟨8210542784004358723351403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5473695189336239148900935 8210542784004358723351403)
        ·
          refine ⟨12315814176006538085027105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8210542784004358723351403 12315814176006538085027105)
          ·
            refine ⟨9236860632004903563770329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12315814176006538085027105 9236860632004903563770329)
            ·
              refine ⟨6927645474003677672827747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9236860632004903563770329 6927645474003677672827747)
              ·
                refine ⟨10391468211005516509241621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6927645474003677672827747 10391468211005516509241621)
                ·
                  refine ⟨487100072390883586370701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10391468211005516509241621 487100072390883586370701)
                  ·
                    refine ⟨182662527146581344889013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487100072390883586370701 182662527146581344889013)
                    ·
                      rfl

theorem cell22_533601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_533601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533601 prefixEnd_533601 := by exact prefixLift 533601
  have htrace : WordTrace (prefixWord ++ tailWord_533601) baseStart_533601 baseEnd_533601 := by
    simpa [prefixWord, tailWord_533601, baseEnd_533601] using wordTrace_append hprefix tailTrace_533601
  have hstable : (prefixWord ++ tailWord_533601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533601).length < 2 ^ (prefixWord ++ tailWord_533601).sum := by decide
  have hdescent : baseEnd_533601 < baseStart_533601 := by decide
  rcases family_descends (prefixWord ++ tailWord_533601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533616 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_533616 : Nat := 118140960795 + 533616 * 2 ^ 59
def prefixEnd_533616 : Nat := 4983230072969 + 3 ^ 40 * 533616 * 2
def baseEnd_533616 : Nat := 182667661953126305763967

theorem tailTrace_533616 : CollatzResearch.WordTrace tailWord_533616 prefixEnd_533616 182667661953126305763967 := by
  unfold tailWord_533616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731287217403920601166351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12975049623205227468221801 9731287217403920601166351)
  ·
    refine ⟨14596930826105880901749527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9731287217403920601166351 14596930826105880901749527)
    ·
      refine ⟨21895396239158821352624291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596930826105880901749527 21895396239158821352624291)
      ·
        refine ⟨32843094358738232028936437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21895396239158821352624291 32843094358738232028936437)
        ·
          refine ⟨3079040096131709252712791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32843094358738232028936437 3079040096131709252712791)
          ·
            refine ⟨4618560144197563879069187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3079040096131709252712791 4618560144197563879069187)
            ·
              refine ⟨6927840216296345818603781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4618560144197563879069187 6927840216296345818603781)
              ·
                refine ⟨1298970040555564840988209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6927840216296345818603781 1298970040555564840988209)
                ·
                  refine ⟨974227530416673630741157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1298970040555564840988209 974227530416673630741157)
                  ·
                    refine ⟨182667661953126305763967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974227530416673630741157 182667661953126305763967)
                    ·
                      rfl

theorem cell22_533616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_533616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533616 prefixEnd_533616 := by exact prefixLift 533616
  have htrace : WordTrace (prefixWord ++ tailWord_533616) baseStart_533616 baseEnd_533616 := by
    simpa [prefixWord, tailWord_533616, baseEnd_533616] using wordTrace_append hprefix tailTrace_533616
  have hstable : (prefixWord ++ tailWord_533616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533616).length < 2 ^ (prefixWord ++ tailWord_533616).sum := by decide
  have hdescent : baseEnd_533616 < baseStart_533616 := by decide
  rcases family_descends (prefixWord ++ tailWord_533616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533650 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_533650 : Nat := 118140960795 + 533650 * 2 ^ 59
def prefixEnd_533650 : Nat := 4983230072969 + 3 ^ 40 * 533650 * 2
def baseEnd_533650 : Nat := 182679300847961550413863

theorem tailTrace_533650 : CollatzResearch.WordTrace tailWord_533650 prefixEnd_533650 182679300847961550413863 := by
  unfold tailWord_533650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865953629171166252267601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12975876344456443339380269 4865953629171166252267601)
  ·
    refine ⟨3649465221878374689200701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4865953629171166252267601 3649465221878374689200701)
    ·
      refine ⟨1368549458204390508450263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3649465221878374689200701 1368549458204390508450263)
      ·
        refine ⟨2052824187306585762675395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368549458204390508450263 2052824187306585762675395)
        ·
          refine ⟨3079236280959878644013093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052824187306585762675395 3079236280959878644013093)
          ·
            refine ⟨577356802679977245752455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3079236280959878644013093 577356802679977245752455)
            ·
              refine ⟨866035204019965868628683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577356802679977245752455 866035204019965868628683)
              ·
                refine ⟨1299052806029948802943025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866035204019965868628683 1299052806029948802943025)
                ·
                  refine ⟨974289604522461602207269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1299052806029948802943025 974289604522461602207269)
                  ·
                    refine ⟨182679300847961550413863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974289604522461602207269 182679300847961550413863)
                    ·
                      rfl

theorem cell22_533650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_533650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533650 prefixEnd_533650 := by exact prefixLift 533650
  have htrace : WordTrace (prefixWord ++ tailWord_533650) baseStart_533650 baseEnd_533650 := by
    simpa [prefixWord, tailWord_533650, baseEnd_533650] using wordTrace_append hprefix tailTrace_533650
  have hstable : (prefixWord ++ tailWord_533650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533650).length < 2 ^ (prefixWord ++ tailWord_533650).sum := by decide
  have hdescent : baseEnd_533650 < baseStart_533650 := by decide
  rcases family_descends (prefixWord ++ tailWord_533650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533676 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_533676 : Nat := 118140960795 + 533676 * 2 ^ 59
def prefixEnd_533676 : Nat := 4983230072969 + 3 ^ 40 * 533676 * 2
def baseEnd_533676 : Nat := 60896067059768716421261

theorem tailTrace_533676 : CollatzResearch.WordTrace tailWord_533676 prefixEnd_533676 60896067059768716421261 := by
  unfold tailWord_533676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732381407295235724758441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12976508543060314299677921 9732381407295235724758441)
  ·
    refine ⟨7299286055471426793568831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9732381407295235724758441 7299286055471426793568831)
    ·
      refine ⟨10948929083207140190353247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7299286055471426793568831 10948929083207140190353247)
      ·
        refine ⟨16423393624810710285529871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10948929083207140190353247 16423393624810710285529871)
        ·
          refine ⟨24635090437216065428294807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16423393624810710285529871 24635090437216065428294807)
          ·
            refine ⟨36952635655824098142442211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24635090437216065428294807 36952635655824098142442211)
            ·
              refine ⟨55428953483736147213663317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36952635655824098142442211 55428953483736147213663317)
              ·
                refine ⟨649558048637532975160117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 55428953483736147213663317 649558048637532975160117)
                ·
                  refine ⟨60896067059768716421261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649558048637532975160117 60896067059768716421261)
                  ·
                    rfl

theorem cell22_533676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_533676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533676 prefixEnd_533676 := by exact prefixLift 533676
  have htrace : WordTrace (prefixWord ++ tailWord_533676) baseStart_533676 baseEnd_533676 := by
    simpa [prefixWord, tailWord_533676, baseEnd_533676] using wordTrace_append hprefix tailTrace_533676
  have hstable : (prefixWord ++ tailWord_533676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533676).length < 2 ^ (prefixWord ++ tailWord_533676).sum := by decide
  have hdescent : baseEnd_533676 < baseStart_533676 := by decide
  rcases family_descends (prefixWord ++ tailWord_533676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533686 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_533686 : Nat := 118140960795 + 533686 * 2 ^ 59
def prefixEnd_533686 : Nat := 4983230072969 + 3 ^ 40 * 533686 * 2
def baseEnd_533686 : Nat := 182691624383669456513753

theorem tailTrace_533686 : CollatzResearch.WordTrace tailWord_533686 prefixEnd_533686 182691624383669456513753 := by
  unfold tailWord_533686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216570471534640197336307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12976751696369495438253941 1216570471534640197336307)
  ·
    refine ⟨1824855707301960296004461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216570471534640197336307 1824855707301960296004461)
    ·
      refine ⟨684320890238235111001673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1824855707301960296004461 684320890238235111001673)
      ·
        refine ⟨513240667678676333251255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684320890238235111001673 513240667678676333251255)
        ·
          refine ⟨769861001518014499876883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513240667678676333251255 769861001518014499876883)
          ·
            refine ⟨1154791502277021749815325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769861001518014499876883 1154791502277021749815325)
            ·
              refine ⟨433046813353883156180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154791502277021749815325 433046813353883156180747)
              ·
                refine ⟨649570220030824734271121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433046813353883156180747 649570220030824734271121)
                ·
                  refine ⟨487177665023118550703341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649570220030824734271121 487177665023118550703341)
                  ·
                    refine ⟨182691624383669456513753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487177665023118550703341 182691624383669456513753)
                    ·
                      rfl

theorem cell22_533686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_533686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533686 prefixEnd_533686 := by exact prefixLift 533686
  have htrace : WordTrace (prefixWord ++ tailWord_533686) baseStart_533686 baseEnd_533686 := by
    simpa [prefixWord, tailWord_533686, baseEnd_533686] using wordTrace_append hprefix tailTrace_533686
  have hstable : (prefixWord ++ tailWord_533686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533686).length < 2 ^ (prefixWord ++ tailWord_533686).sum := by decide
  have hdescent : baseEnd_533686 < baseStart_533686 := by decide
  rcases family_descends (prefixWord ++ tailWord_533686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533738 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_533738 : Nat := 118140960795 + 533738 * 2 ^ 59
def prefixEnd_533738 : Nat := 4983230072969 + 3 ^ 40 * 533738 * 2
def baseEnd_533738 : Nat := 60903141682119551404531

theorem tailTrace_533738 : CollatzResearch.WordTrace tailWord_533738 prefixEnd_533738 60903141682119551404531 := by
  unfold tailWord_533738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866756035091464009568467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12978016093577237358849245 4866756035091464009568467)
  ·
    refine ⟨7300134052637196014352701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4866756035091464009568467 7300134052637196014352701)
    ·
      refine ⟨2737550269738948505382263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7300134052637196014352701 2737550269738948505382263)
      ·
        refine ⟨4106325404608422758073395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737550269738948505382263 4106325404608422758073395)
        ·
          refine ⟨6159488106912634137110093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4106325404608422758073395 6159488106912634137110093)
          ·
            refine ⟨2309808040092237801416285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6159488106912634137110093 2309808040092237801416285)
            ·
              refine ⟨866178015034589175531107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309808040092237801416285 866178015034589175531107)
              ·
                refine ⟨1299267022551883763296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866178015034589175531107 1299267022551883763296661)
                ·
                  refine ⟨60903141682119551404531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299267022551883763296661 60903141682119551404531)
                  ·
                    rfl

theorem cell22_533738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_533738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533738 prefixEnd_533738 := by exact prefixLift 533738
  have htrace : WordTrace (prefixWord ++ tailWord_533738) baseStart_533738 baseEnd_533738 := by
    simpa [prefixWord, tailWord_533738, baseEnd_533738] using wordTrace_append hprefix tailTrace_533738
  have hstable : (prefixWord ++ tailWord_533738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533738).length < 2 ^ (prefixWord ++ tailWord_533738).sum := by decide
  have hdescent : baseEnd_533738 < baseStart_533738 := by decide
  rcases family_descends (prefixWord ++ tailWord_533738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533789 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 4]
def baseStart_533789 : Nat := 118140960795 + 533789 * 2 ^ 59
def prefixEnd_533789 : Nat := 4983230072969 + 3 ^ 40 * 533789 * 2
def baseEnd_533789 : Nat := 60908961129537173729479

theorem tailTrace_533789 : CollatzResearch.WordTrace tailWord_533789 prefixEnd_533789 60908961129537173729479 := by
  unfold tailWord_533789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19468884263181091748380421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12979256175454061165586947 19468884263181091748380421)
  ·
    refine ⟨3650415799346454702821329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19468884263181091748380421 3650415799346454702821329)
    ·
      refine ⟨2737811849509841027115997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650415799346454702821329 2737811849509841027115997)
      ·
        refine ⟨1026679443566190385168499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2737811849509841027115997 1026679443566190385168499)
        ·
          refine ⟨1540019165349285577752749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026679443566190385168499 1540019165349285577752749)
          ·
            refine ⟨577507187005982091657281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1540019165349285577752749 577507187005982091657281)
            ·
              refine ⟨433130390254486568742961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577507187005982091657281 433130390254486568742961)
              ·
                refine ⟨324847792690864926557221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433130390254486568742961 324847792690864926557221)
                ·
                  refine ⟨60908961129537173729479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324847792690864926557221 60908961129537173729479)
                  ·
                    rfl

theorem cell22_533789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_533789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533789 prefixEnd_533789 := by exact prefixLift 533789
  have htrace : WordTrace (prefixWord ++ tailWord_533789) baseStart_533789 baseEnd_533789 := by
    simpa [prefixWord, tailWord_533789, baseEnd_533789] using wordTrace_append hprefix tailTrace_533789
  have hstable : (prefixWord ++ tailWord_533789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533789).length < 2 ^ (prefixWord ++ tailWord_533789).sum := by decide
  have hdescent : baseEnd_533789 < baseStart_533789 := by decide
  rcases family_descends (prefixWord ++ tailWord_533789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533800 : List Nat := [2, 1, 5, 1, 2, 3, 1, 7]
def baseStart_533800 : Nat := 118140960795 + 533800 * 2 ^ 59
def prefixEnd_533800 : Nat := 4983230072969 + 3 ^ 40 * 533800 * 2
def baseEnd_533800 : Nat := 20303405434823462129267

theorem tailTrace_533800 : CollatzResearch.WordTrace tailWord_533800 prefixEnd_533800 20303405434823462129267 := by
  unfold tailWord_533800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9734642733070620313515427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12979523644094160418020569 9734642733070620313515427)
  ·
    refine ⟨14601964099605930470273141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9734642733070620313515427 14601964099605930470273141)
    ·
      refine ⟨1368934134338055981588107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14601964099605930470273141 1368934134338055981588107)
      ·
        refine ⟨2053401201507083972382161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368934134338055981588107 2053401201507083972382161)
        ·
          refine ⟨1540050901130312979286621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053401201507083972382161 1540050901130312979286621)
          ·
            refine ⟨577519087923867367232483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1540050901130312979286621 577519087923867367232483)
            ·
              refine ⟨866278631885801050848725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577519087923867367232483 866278631885801050848725)
              ·
                refine ⟨20303405434823462129267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 866278631885801050848725 20303405434823462129267)
                ·
                  rfl

theorem cell22_533800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_533800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533800 prefixEnd_533800 := by exact prefixLift 533800
  have htrace : WordTrace (prefixWord ++ tailWord_533800) baseStart_533800 baseEnd_533800 := by
    simpa [prefixWord, tailWord_533800, baseEnd_533800] using wordTrace_append hprefix tailTrace_533800
  have hstable : (prefixWord ++ tailWord_533800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533800).length < 2 ^ (prefixWord ++ tailWord_533800).sum := by decide
  have hdescent : baseEnd_533800 < baseStart_533800 := by decide
  rcases family_descends (prefixWord ++ tailWord_533800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533845 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 5]
def baseStart_533845 : Nat := 118140960795 + 533845 * 2 ^ 59
def prefixEnd_533845 : Nat := 4983230072969 + 3 ^ 40 * 533845 * 2
def baseEnd_533845 : Nat := 60915351111015347262755

theorem tailTrace_533845 : CollatzResearch.WordTrace tailWord_533845 prefixEnd_533845 60915351111015347262755 := by
  unfold tailWord_533845
  simp only [CollatzResearch.WordTrace]
  refine ⟨19470926750978213312418989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12980617833985475541612659 19470926750978213312418989)
  ·
    refine ⟨7301597531616829992157121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19470926750978213312418989 7301597531616829992157121)
    ·
      refine ⟨5476198148712622494117841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7301597531616829992157121 5476198148712622494117841)
      ·
        refine ⟨4107148611534466870588381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5476198148712622494117841 4107148611534466870588381)
        ·
          refine ⟨1540180729325425076470643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4107148611534466870588381 1540180729325425076470643)
          ·
            refine ⟨2310271093988137614705965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540180729325425076470643 2310271093988137614705965)
            ·
              refine ⟨866351660245551605514737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2310271093988137614705965 866351660245551605514737)
              ·
                refine ⟨649763745184163704136053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866351660245551605514737 649763745184163704136053)
                ·
                  refine ⟨60915351111015347262755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649763745184163704136053 60915351111015347262755)
                  ·
                    rfl

theorem cell22_533845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_533845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533845 prefixEnd_533845 := by exact prefixLift 533845
  have htrace : WordTrace (prefixWord ++ tailWord_533845) baseStart_533845 baseEnd_533845 := by
    simpa [prefixWord, tailWord_533845, baseEnd_533845] using wordTrace_append hprefix tailTrace_533845
  have hstable : (prefixWord ++ tailWord_533845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533845).length < 2 ^ (prefixWord ++ tailWord_533845).sum := by decide
  have hdescent : baseEnd_533845 < baseStart_533845 := by decide
  rcases family_descends (prefixWord ++ tailWord_533845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533873 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 6]
def baseStart_533873 : Nat := 118140960795 + 533873 * 2 ^ 59
def prefixEnd_533873 : Nat := 4983230072969 + 3 ^ 40 * 533873 * 2
def baseEnd_533873 : Nat := 60918546101754434029393

theorem tailTrace_533873 : CollatzResearch.WordTrace tailWord_533873 prefixEnd_533873 60918546101754434029393 := by
  unfold tailWord_533873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19471947994876774094438273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12981298663251182729625515 19471947994876774094438273)
  ·
    refine ⟨14603960996157580570828705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19471947994876774094438273 14603960996157580570828705)
    ·
      refine ⟨10952970747118185428121529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14603960996157580570828705 10952970747118185428121529)
      ·
        refine ⟨8214728060338639071091147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10952970747118185428121529 8214728060338639071091147)
        ·
          refine ⟨12322092090507958606636721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8214728060338639071091147 12322092090507958606636721)
          ·
            refine ⟨9241569067880968954977541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12322092090507958606636721 9241569067880968954977541)
            ·
              refine ⟨1732794200227681679058289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9241569067880968954977541 1732794200227681679058289)
              ·
                refine ⟨1299595650170761259293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1732794200227681679058289 1299595650170761259293717)
                ·
                  refine ⟨60918546101754434029393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299595650170761259293717 60918546101754434029393)
                  ·
                    rfl

theorem cell22_533873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_533873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533873 prefixEnd_533873 := by exact prefixLift 533873
  have htrace : WordTrace (prefixWord ++ tailWord_533873) baseStart_533873 baseEnd_533873 := by
    simpa [prefixWord, tailWord_533873, baseEnd_533873] using wordTrace_append hprefix tailTrace_533873
  have hstable : (prefixWord ++ tailWord_533873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533873).length < 2 ^ (prefixWord ++ tailWord_533873).sum := by decide
  have hdescent : baseEnd_533873 < baseStart_533873 := by decide
  rcases family_descends (prefixWord ++ tailWord_533873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533888 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_533888 : Nat := 118140960795 + 533888 * 2 ^ 59
def prefixEnd_533888 : Nat := 4983230072969 + 3 ^ 40 * 533888 * 2
def baseEnd_533888 : Nat := 182760773111808262963133

theorem tailTrace_533888 : CollatzResearch.WordTrace tailWord_533888 prefixEnd_533888 182760773111808262963133 := by
  unfold tailWord_533888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9736247544911215828117159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12981663393214954437489545 9736247544911215828117159)
  ·
    refine ⟨14604371317366823742175739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9736247544911215828117159 14604371317366823742175739)
    ·
      refine ⟨21906556976050235613263609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14604371317366823742175739 21906556976050235613263609)
      ·
        refine ⟨16429917732037676709947707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21906556976050235613263609 16429917732037676709947707)
        ·
          refine ⟨24644876598056515064921561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16429917732037676709947707 24644876598056515064921561)
          ·
            refine ⟨18483657448542386298691171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24644876598056515064921561 18483657448542386298691171)
            ·
              refine ⟨27725486172813579448036757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18483657448542386298691171 27725486172813579448036757)
              ·
                refine ⟨1299632164350636536626723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27725486172813579448036757 1299632164350636536626723)
                ·
                  refine ⟨1949448246525954804940085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299632164350636536626723 1949448246525954804940085)
                  ·
                    refine ⟨182760773111808262963133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1949448246525954804940085 182760773111808262963133)
                    ·
                      rfl

theorem cell22_533888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_533888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533888 prefixEnd_533888 := by exact prefixLift 533888
  have htrace : WordTrace (prefixWord ++ tailWord_533888) baseStart_533888 baseEnd_533888 := by
    simpa [prefixWord, tailWord_533888, baseEnd_533888] using wordTrace_append hprefix tailTrace_533888
  have hstable : (prefixWord ++ tailWord_533888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533888).length < 2 ^ (prefixWord ++ tailWord_533888).sum := by decide
  have hdescent : baseEnd_533888 < baseStart_533888 := by decide
  rcases family_descends (prefixWord ++ tailWord_533888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533963 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 7]
def baseStart_533963 : Nat := 118140960795 + 533963 * 2 ^ 59
def prefixEnd_533963 : Nat := 4983230072969 + 3 ^ 40 * 533963 * 2
def baseEnd_533963 : Nat := 60928815714844355779301

theorem tailTrace_533963 : CollatzResearch.WordTrace tailWord_533963 prefixEnd_533963 60928815714844355779301 := by
  unfold tailWord_533963
  simp only [CollatzResearch.WordTrace]
  refine ⟨19475230564550719465214543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12983487043033812976809695 19475230564550719465214543)
  ·
    refine ⟨29212845846826079197821815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19475230564550719465214543 29212845846826079197821815)
    ·
      refine ⟨43819268770239118796732723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29212845846826079197821815 43819268770239118796732723)
      ·
        refine ⟨65728903155358678195099085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43819268770239118796732723 65728903155358678195099085)
        ·
          refine ⟨24648338683259504323162157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65728903155358678195099085 24648338683259504323162157)
          ·
            refine ⟨9243127006222314121185809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24648338683259504323162157 9243127006222314121185809)
            ·
              refine ⟨6932345254666735590889357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9243127006222314121185809 6932345254666735590889357)
              ·
                refine ⟨2599629470500025846583509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6932345254666735590889357 2599629470500025846583509)
                ·
                  refine ⟨60928815714844355779301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2599629470500025846583509 60928815714844355779301)
                  ·
                    rfl

theorem cell22_533963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_533963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_533963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_533963 prefixEnd_533963 := by exact prefixLift 533963
  have htrace : WordTrace (prefixWord ++ tailWord_533963) baseStart_533963 baseEnd_533963 := by
    simpa [prefixWord, tailWord_533963, baseEnd_533963] using wordTrace_append hprefix tailTrace_533963
  have hstable : (prefixWord ++ tailWord_533963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533963).length < 2 ^ (prefixWord ++ tailWord_533963).sum := by decide
  have hdescent : baseEnd_533963 < baseStart_533963 := by decide
  rcases family_descends (prefixWord ++ tailWord_533963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534014 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_534014 : Nat := 118140960795 + 534014 * 2 ^ 59
def prefixEnd_534014 : Nat := 4983230072969 + 3 ^ 40 * 534014 * 2
def baseEnd_534014 : Nat := 60934635162261978104249

theorem tailTrace_534014 : CollatzResearch.WordTrace tailWord_534014 prefixEnd_534014 60934635162261978104249 := by
  unfold tailWord_534014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434636335920744396915137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12984727124910636783547397 2434636335920744396915137)
  ·
    refine ⟨1825977251940558297686353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2434636335920744396915137 1825977251940558297686353)
    ·
      refine ⟨1369482938955418723264765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825977251940558297686353 1369482938955418723264765)
      ·
        refine ⟨513556102108282021224287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1369482938955418723264765 513556102108282021224287)
        ·
          refine ⟨770334153162423031836431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513556102108282021224287 770334153162423031836431)
          ·
            refine ⟨1155501229743634547754647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770334153162423031836431 1155501229743634547754647)
            ·
              refine ⟨1733251844615451821631971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155501229743634547754647 1733251844615451821631971)
              ·
                refine ⟨2599877766923177732447957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1733251844615451821631971 2599877766923177732447957)
                ·
                  refine ⟨60934635162261978104249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2599877766923177732447957 60934635162261978104249)
                  ·
                    rfl

theorem cell22_534014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_534014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534014 prefixEnd_534014 := by exact prefixLift 534014
  have htrace : WordTrace (prefixWord ++ tailWord_534014) baseStart_534014 baseEnd_534014 := by
    simpa [prefixWord, tailWord_534014, baseEnd_534014] using wordTrace_append hprefix tailTrace_534014
  have hstable : (prefixWord ++ tailWord_534014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534014).length < 2 ^ (prefixWord ++ tailWord_534014).sum := by decide
  have hdescent : baseEnd_534014 < baseStart_534014 := by decide
  rcases family_descends (prefixWord ++ tailWord_534014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534025 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 6]
def baseStart_534025 : Nat := 118140960795 + 534025 * 2 ^ 59
def prefixEnd_534025 : Nat := 4983230072969 + 3 ^ 40 * 534025 * 2
def baseEnd_534025 : Nat := 60935890337195190762571

theorem tailTrace_534025 : CollatzResearch.WordTrace tailWord_534025 prefixEnd_534025 60935890337195190762571 := by
  unfold tailWord_534025
  simp only [CollatzResearch.WordTrace]
  refine ⟨19477491890326104053971529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12984994593550736035981019 19477491890326104053971529)
  ·
    refine ⟨14608118917744578040478647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19477491890326104053971529 14608118917744578040478647)
    ·
      refine ⟨21912178376616867060717971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14608118917744578040478647 21912178376616867060717971)
      ·
        refine ⟨32868267564925300591076957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21912178376616867060717971 32868267564925300591076957)
        ·
          refine ⟨12325600336846987721653859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32868267564925300591076957 12325600336846987721653859)
          ·
            refine ⟨18488400505270481582480789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12325600336846987721653859 18488400505270481582480789)
            ·
              refine ⟨866643773684553824178787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18488400505270481582480789 866643773684553824178787)
              ·
                refine ⟨1299965660526830736268181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866643773684553824178787 1299965660526830736268181)
                ·
                  refine ⟨60935890337195190762571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299965660526830736268181 60935890337195190762571)
                  ·
                    rfl

theorem cell22_534025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_534025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534025 prefixEnd_534025 := by exact prefixLift 534025
  have htrace : WordTrace (prefixWord ++ tailWord_534025) baseStart_534025 baseEnd_534025 := by
    simpa [prefixWord, tailWord_534025, baseEnd_534025] using wordTrace_append hprefix tailTrace_534025
  have hstable : (prefixWord ++ tailWord_534025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534025).length < 2 ^ (prefixWord ++ tailWord_534025).sum := by decide
  have hdescent : baseEnd_534025 < baseStart_534025 := by decide
  rcases family_descends (prefixWord ++ tailWord_534025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534072 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_534072 : Nat := 118140960795 + 534072 * 2 ^ 59
def prefixEnd_534072 : Nat := 4983230072969 + 3 ^ 40 * 534072 * 2
def baseEnd_534072 : Nat := 182823760072093116362569

theorem tailTrace_534072 : CollatzResearch.WordTrace tailWord_534072 prefixEnd_534072 182823760072093116362569 := by
  unfold tailWord_534072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739603060577915540466235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12986137414103887387288313 9739603060577915540466235)
  ·
    refine ⟨14609404590866873310699353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9739603060577915540466235 14609404590866873310699353)
    ·
      refine ⟨10957053443150154983024515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14609404590866873310699353 10957053443150154983024515)
      ·
        refine ⟨16435580164725232474536773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10957053443150154983024515 16435580164725232474536773)
        ·
          refine ⟨3081671280885981088975645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16435580164725232474536773 3081671280885981088975645)
          ·
            refine ⟨1155626730332242908365867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3081671280885981088975645 1155626730332242908365867)
            ·
              refine ⟨1733440095498364362548801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155626730332242908365867 1733440095498364362548801)
              ·
                refine ⟨1300080071623773271911601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733440095498364362548801 1300080071623773271911601)
                ·
                  refine ⟨975060053717829953933701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300080071623773271911601 975060053717829953933701)
                  ·
                    refine ⟨182823760072093116362569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 975060053717829953933701 182823760072093116362569)
                    ·
                      rfl

theorem cell22_534072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_534072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534072 prefixEnd_534072 := by exact prefixLift 534072
  have htrace : WordTrace (prefixWord ++ tailWord_534072) baseStart_534072 baseEnd_534072 := by
    simpa [prefixWord, tailWord_534072, baseEnd_534072] using wordTrace_append hprefix tailTrace_534072
  have hstable : (prefixWord ++ tailWord_534072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534072).length < 2 ^ (prefixWord ++ tailWord_534072).sum := by decide
  have hdescent : baseEnd_534072 < baseStart_534072 := by decide
  rcases family_descends (prefixWord ++ tailWord_534072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534076 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_534076 : Nat := 118140960795 + 534076 * 2 ^ 59
def prefixEnd_534076 : Nat := 4983230072969 + 3 ^ 40 * 534076 * 2
def baseEnd_534076 : Nat := 60941709784612813087519

theorem tailTrace_534076 : CollatzResearch.WordTrace tailWord_534076 prefixEnd_534076 60941709784612813087519 := by
  unfold tailWord_534076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9739676006570669882039041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12986234675427559842718721 9739676006570669882039041)
  ·
    refine ⟨7304757004928002411529281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9739676006570669882039041 7304757004928002411529281)
    ·
      refine ⟨5478567753696001808646961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7304757004928002411529281 5478567753696001808646961)
      ·
        refine ⟨4108925815272001356485221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5478567753696001808646961 4108925815272001356485221)
        ·
          refine ⟨770423590363500254340979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4108925815272001356485221 770423590363500254340979)
          ·
            refine ⟨1155635385545250381511469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770423590363500254340979 1155635385545250381511469)
            ·
              refine ⟨433363269579468893066801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1155635385545250381511469 433363269579468893066801)
              ·
                refine ⟨325022452184601669800101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433363269579468893066801 325022452184601669800101)
                ·
                  refine ⟨60941709784612813087519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325022452184601669800101 60941709784612813087519)
                  ·
                    rfl

theorem cell22_534076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_534076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534076 prefixEnd_534076 := by exact prefixLift 534076
  have htrace : WordTrace (prefixWord ++ tailWord_534076) baseStart_534076 baseEnd_534076 := by
    simpa [prefixWord, tailWord_534076, baseEnd_534076] using wordTrace_append hprefix tailTrace_534076
  have hstable : (prefixWord ++ tailWord_534076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534076).length < 2 ^ (prefixWord ++ tailWord_534076).sum := by decide
  have hdescent : baseEnd_534076 < baseStart_534076 := by decide
  rcases family_descends (prefixWord ++ tailWord_534076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534087 : List Nat := [1, 1, 4, 1, 5, 1, 2, 7]
def baseStart_534087 : Nat := 118140960795 + 534087 * 2 ^ 59
def prefixEnd_534087 : Nat := 4983230072969 + 3 ^ 40 * 534087 * 2
def baseEnd_534087 : Nat := 20314321653182008581947

theorem tailTrace_534087 : CollatzResearch.WordTrace tailWord_534087 prefixEnd_534087 20314321653182008581947 := by
  unfold tailWord_534087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19479753216101488642728515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12986502144067659095152343 19479753216101488642728515)
  ·
    refine ⟨29219629824152232964092773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19479753216101488642728515 29219629824152232964092773)
    ·
      refine ⟨5478680592028543680767395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29219629824152232964092773 5478680592028543680767395)
      ·
        refine ⟨8218020888042815521151093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5478680592028543680767395 8218020888042815521151093)
        ·
          refine ⟨770439458254013955107915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8218020888042815521151093 770439458254013955107915)
          ·
            refine ⟨1155659187381020932661873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770439458254013955107915 1155659187381020932661873)
            ·
              refine ⟨866744390535765699496405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155659187381020932661873 866744390535765699496405)
              ·
                refine ⟨20314321653182008581947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 866744390535765699496405 20314321653182008581947)
                ·
                  rfl

theorem cell22_534087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 7].length) (baseStart_534087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534087 prefixEnd_534087 := by exact prefixLift 534087
  have htrace : WordTrace (prefixWord ++ tailWord_534087) baseStart_534087 baseEnd_534087 := by
    simpa [prefixWord, tailWord_534087, baseEnd_534087] using wordTrace_append hprefix tailTrace_534087
  have hstable : (prefixWord ++ tailWord_534087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534087).length < 2 ^ (prefixWord ++ tailWord_534087).sum := by decide
  have hdescent : baseEnd_534087 < baseStart_534087 := by decide
  rcases family_descends (prefixWord ++ tailWord_534087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534194 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_534194 : Nat := 118140960795 + 534194 * 2 ^ 59
def prefixEnd_534194 : Nat := 4983230072969 + 3 ^ 40 * 534194 * 2
def baseEnd_534194 : Nat := 60955174388441821604065

theorem tailTrace_534194 : CollatzResearch.WordTrace tailWord_534194 prefixEnd_534194 60955174388441821604065 := by
  unfold tailWord_534194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870913956678461479218409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12989103884475897277915757 4870913956678461479218409)
  ·
    refine ⟨3653185467508846109413807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4870913956678461479218409 3653185467508846109413807)
    ·
      refine ⟨5479778201263269164120711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653185467508846109413807 5479778201263269164120711)
      ·
        refine ⟨8219667301894903746181067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479778201263269164120711 8219667301894903746181067)
        ·
          refine ⟨12329500952842355619271601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8219667301894903746181067 12329500952842355619271601)
          ·
            refine ⟨9247125714631766714453701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12329500952842355619271601 9247125714631766714453701)
            ·
              refine ⟨1733836071493456258960069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9247125714631766714453701 1733836071493456258960069)
              ·
                refine ⟨325094263405023048555013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733836071493456258960069 325094263405023048555013)
                ·
                  refine ⟨60955174388441821604065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325094263405023048555013 60955174388441821604065)
                  ·
                    rfl

theorem cell22_534194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_534194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534194 prefixEnd_534194 := by exact prefixLift 534194
  have htrace : WordTrace (prefixWord ++ tailWord_534194) baseStart_534194 baseEnd_534194 := by
    simpa [prefixWord, tailWord_534194, baseEnd_534194] using wordTrace_append hprefix tailTrace_534194
  have hstable : (prefixWord ++ tailWord_534194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534194).length < 2 ^ (prefixWord ++ tailWord_534194).sum := by decide
  have hdescent : baseEnd_534194 < baseStart_534194 := by decide
  rcases family_descends (prefixWord ++ tailWord_534194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534222 : List Nat := [4, 1, 1, 1, 3, 1, 3, 8]
def baseStart_534222 : Nat := 118140960795 + 534222 * 2 ^ 59
def prefixEnd_534222 : Nat := 4983230072969 + 3 ^ 40 * 534222 * 2
def baseEnd_534222 : Nat := 20319456459726969456901

theorem tailTrace_534222 : CollatzResearch.WordTrace tailWord_534222 prefixEnd_534222 20319456459726969456901 := by
  unfold tailWord_534222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435584633826550837361615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12989784713741604465928613 2435584633826550837361615)
  ·
    refine ⟨3653376950739826256042423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2435584633826550837361615 3653376950739826256042423)
    ·
      refine ⟨5480065426109739384063635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653376950739826256042423 5480065426109739384063635)
      ·
        refine ⟨8220098139164609076095453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5480065426109739384063635 8220098139164609076095453)
        ·
          refine ⟨3082536802186728403535795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8220098139164609076095453 3082536802186728403535795)
          ·
            refine ⟨4623805203280092605303693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082536802186728403535795 4623805203280092605303693)
            ·
              refine ⟨1733926951230034726988885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4623805203280092605303693 1733926951230034726988885)
              ·
                refine ⟨20319456459726969456901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1733926951230034726988885 20319456459726969456901)
                ·
                  rfl

theorem cell22_534222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_534222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534222 prefixEnd_534222 := by exact prefixLift 534222
  have htrace : WordTrace (prefixWord ++ tailWord_534222) baseStart_534222 baseEnd_534222 := by
    simpa [prefixWord, tailWord_534222, baseEnd_534222] using wordTrace_append hprefix tailTrace_534222
  have hstable : (prefixWord ++ tailWord_534222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534222).length < 2 ^ (prefixWord ++ tailWord_534222).sum := by decide
  have hdescent : baseEnd_534222 < baseStart_534222 := by decide
  rcases family_descends (prefixWord ++ tailWord_534222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534228 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 4]
def baseStart_534228 : Nat := 118140960795 + 534228 * 2 ^ 59
def prefixEnd_534228 : Nat := 4983230072969 + 3 ^ 40 * 534228 * 2
def baseEnd_534228 : Nat := 60959054020053569820697

theorem tailTrace_534228 : CollatzResearch.WordTrace tailWord_534228 prefixEnd_534228 60959054020053569820697 := by
  unfold tailWord_534228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742447954295334861805669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12989930605727113149074225 9742447954295334861805669)
  ·
    refine ⟨1826708991430375286588563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9742447954295334861805669 1826708991430375286588563)
    ·
      refine ⟨2740063487145562929882845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826708991430375286588563 2740063487145562929882845)
      ·
        refine ⟨1027523807679586098706067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2740063487145562929882845 1027523807679586098706067)
        ·
          refine ⟨1541285711519379148059101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027523807679586098706067 1541285711519379148059101)
          ·
            refine ⟨577982141819767180522163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1541285711519379148059101 577982141819767180522163)
            ·
              refine ⟨866973212729650770783245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577982141819767180522163 866973212729650770783245)
              ·
                refine ⟨325114954773619039043717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866973212729650770783245 325114954773619039043717)
                ·
                  refine ⟨60959054020053569820697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325114954773619039043717 60959054020053569820697)
                  ·
                    rfl

theorem cell22_534228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_534228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534228 prefixEnd_534228 := by exact prefixLift 534228
  have htrace : WordTrace (prefixWord ++ tailWord_534228) baseStart_534228 baseEnd_534228 := by
    simpa [prefixWord, tailWord_534228, baseEnd_534228] using wordTrace_append hprefix tailTrace_534228
  have hstable : (prefixWord ++ tailWord_534228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534228).length < 2 ^ (prefixWord ++ tailWord_534228).sum := by decide
  have hdescent : baseEnd_534228 < baseStart_534228 := by decide
  rcases family_descends (prefixWord ++ tailWord_534228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534260 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_534260 : Nat := 118140960795 + 534260 * 2 ^ 59
def prefixEnd_534260 : Nat := 4983230072969 + 3 ^ 40 * 534260 * 2
def baseEnd_534260 : Nat := 182888116314123292661993

theorem tailTrace_534260 : CollatzResearch.WordTrace tailWord_534260 prefixEnd_534260 182888116314123292661993 := by
  unfold tailWord_534260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743031522237369594388117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12990708696316492792517489 9743031522237369594388117)
  ·
    refine ⟨456704602604876699736943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9743031522237369594388117 456704602604876699736943)
    ·
      refine ⟨685056903907315049605415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456704602604876699736943 685056903907315049605415)
      ·
        refine ⟨1027585355860972574408123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685056903907315049605415 1027585355860972574408123)
        ·
          refine ⟨1541378033791458861612185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027585355860972574408123 1541378033791458861612185)
          ·
            refine ⟨1156033525343594146209139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541378033791458861612185 1156033525343594146209139)
            ·
              refine ⟨1734050288015391219313709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156033525343594146209139 1734050288015391219313709)
              ·
                refine ⟨650268858005771707242641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1734050288015391219313709 650268858005771707242641)
                ·
                  refine ⟨487701643504328780431981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650268858005771707242641 487701643504328780431981)
                  ·
                    refine ⟨182888116314123292661993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487701643504328780431981 182888116314123292661993)
                    ·
                      rfl

theorem cell22_534260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_534260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534260 prefixEnd_534260 := by exact prefixLift 534260
  have htrace : WordTrace (prefixWord ++ tailWord_534260) baseStart_534260 baseEnd_534260 := by
    simpa [prefixWord, tailWord_534260, baseEnd_534260] using wordTrace_append hprefix tailTrace_534260
  have hstable : (prefixWord ++ tailWord_534260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534260).length < 2 ^ (prefixWord ++ tailWord_534260).sum := by decide
  have hdescent : baseEnd_534260 < baseStart_534260 := by decide
  rcases family_descends (prefixWord ++ tailWord_534260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534305 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_534305 : Nat := 118140960795 + 534305 * 2 ^ 59
def prefixEnd_534305 : Nat := 4983230072969 + 3 ^ 40 * 534305 * 2
def baseEnd_534305 : Nat := 182903520733758175286855

theorem tailTrace_534305 : CollatzResearch.WordTrace tailWord_534305 prefixEnd_534305 182903520733758175286855 := by
  unfold tailWord_534305
  simp only [CollatzResearch.WordTrace]
  refine ⟨19487704329311711874164369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12991802886207807916109579 19487704329311711874164369)
  ·
    refine ⟨14615778246983783905623277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19487704329311711874164369 14615778246983783905623277)
    ·
      refine ⟨5480916842618918964608729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14615778246983783905623277 5480916842618918964608729)
      ·
        refine ⟨4110687631964189223456547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5480916842618918964608729 4110687631964189223456547)
        ·
          refine ⟨6166031447946283835184821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110687631964189223456547 6166031447946283835184821)
          ·
            refine ⟨578065448244964109548577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6166031447946283835184821 578065448244964109548577)
            ·
              refine ⟨433549086183723082161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578065448244964109548577 433549086183723082161433)
              ·
                refine ⟨325161814637792311621075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433549086183723082161433 325161814637792311621075)
                ·
                  refine ⟨487742721956688467431613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325161814637792311621075 487742721956688467431613)
                  ·
                    refine ⟨182903520733758175286855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487742721956688467431613 182903520733758175286855)
                    ·
                      rfl

theorem cell22_534305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_534305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534305 prefixEnd_534305 := by exact prefixLift 534305
  have htrace : WordTrace (prefixWord ++ tailWord_534305) baseStart_534305 baseEnd_534305 := by
    simpa [prefixWord, tailWord_534305, baseEnd_534305] using wordTrace_append hprefix tailTrace_534305
  have hstable : (prefixWord ++ tailWord_534305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534305).length < 2 ^ (prefixWord ++ tailWord_534305).sum := by decide
  have hdescent : baseEnd_534305 < baseStart_534305 := by decide
  rcases family_descends (prefixWord ++ tailWord_534305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534344 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_534344 : Nat := 118140960795 + 534344 * 2 ^ 59
def prefixEnd_534344 : Nat := 4983230072969 + 3 ^ 40 * 534344 * 2
def baseEnd_534344 : Nat := 182916871230775073561735

theorem tailTrace_534344 : CollatzResearch.WordTrace tailWord_534344 prefixEnd_534344 182916871230775073561735 := by
  unfold tailWord_534344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744563388085210767417043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12992751184113614356556057 9744563388085210767417043)
  ·
    refine ⟨14616845082127816151125565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9744563388085210767417043 14616845082127816151125565)
    ·
      refine ⟨5481316905797931056672087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14616845082127816151125565 5481316905797931056672087)
      ·
        refine ⟨8221975358696896585008131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481316905797931056672087 8221975358696896585008131)
        ·
          refine ⟨12332963038045344877512197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8221975358696896585008131 12332963038045344877512197)
          ·
            refine ⟨2312430569633502164533537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12332963038045344877512197 2312430569633502164533537)
            ·
              refine ⟨1734322927225126623400153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312430569633502164533537 1734322927225126623400153)
              ·
                refine ⟨1300742195418844967550115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1734322927225126623400153 1300742195418844967550115)
                ·
                  refine ⟨1951113293128267451325173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300742195418844967550115 1951113293128267451325173)
                  ·
                    refine ⟨182916871230775073561735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1951113293128267451325173 182916871230775073561735)
                    ·
                      rfl

theorem cell22_534344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_534344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534344 prefixEnd_534344 := by exact prefixLift 534344
  have htrace : WordTrace (prefixWord ++ tailWord_534344) baseStart_534344 baseEnd_534344 := by
    simpa [prefixWord, tailWord_534344, baseEnd_534344] using wordTrace_append hprefix tailTrace_534344
  have hstable : (prefixWord ++ tailWord_534344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534344).length < 2 ^ (prefixWord ++ tailWord_534344).sum := by decide
  have hdescent : baseEnd_534344 < baseStart_534344 := by decide
  rcases family_descends (prefixWord ++ tailWord_534344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534346 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_534346 : Nat := 118140960795 + 534346 * 2 ^ 59
def prefixEnd_534346 : Nat := 4983230072969 + 3 ^ 40 * 534346 * 2
def baseEnd_534346 : Nat := 60972518623882578337243

theorem tailTrace_534346 : CollatzResearch.WordTrace tailWord_534346 prefixEnd_534346 60972518623882578337243 := by
  unfold tailWord_534346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872299930540793969101723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12992799814775450584271261 4872299930540793969101723)
  ·
    refine ⟨7308449895811190953652585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872299930540793969101723 7308449895811190953652585)
    ·
      refine ⟨5481337421858393215239439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7308449895811190953652585 5481337421858393215239439)
      ·
        refine ⟨8222006132787589822859159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481337421858393215239439 8222006132787589822859159)
        ·
          refine ⟨12333009199181384734288739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8222006132787589822859159 12333009199181384734288739)
          ·
            refine ⟨18499513798772077101433109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12333009199181384734288739 18499513798772077101433109)
            ·
              refine ⟨867164709317441114129677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18499513798772077101433109 867164709317441114129677)
              ·
                refine ⟨325186765994040417798629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867164709317441114129677 325186765994040417798629)
                ·
                  refine ⟨60972518623882578337243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325186765994040417798629 60972518623882578337243)
                  ·
                    rfl

theorem cell22_534346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_534346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534346 prefixEnd_534346 := by exact prefixLift 534346
  have htrace : WordTrace (prefixWord ++ tailWord_534346) baseStart_534346 baseEnd_534346 := by
    simpa [prefixWord, tailWord_534346, baseEnd_534346] using wordTrace_append hprefix tailTrace_534346
  have hstable : (prefixWord ++ tailWord_534346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534346).length < 2 ^ (prefixWord ++ tailWord_534346).sum := by decide
  have hdescent : baseEnd_534346 < baseStart_534346 := by decide
  rcases family_descends (prefixWord ++ tailWord_534346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534389 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_534389 : Nat := 118140960795 + 534389 * 2 ^ 59
def prefixEnd_534389 : Nat := 4983230072969 + 3 ^ 40 * 534389 * 2
def baseEnd_534389 : Nat := 182932275650409956186597

theorem tailTrace_534389 : CollatzResearch.WordTrace tailWord_534389 prefixEnd_534389 182932275650409956186597 := by
  unfold tailWord_534389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19490768061007394220222221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12993845374004929480148147 19490768061007394220222221)
  ·
    refine ⟨7309038022877772832583333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19490768061007394220222221 7309038022877772832583333)
    ·
      refine ⟨1370444629289582406109375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7309038022877772832583333 1370444629289582406109375)
      ·
        refine ⟨2055666943934373609164063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370444629289582406109375 2055666943934373609164063)
        ·
          refine ⟨3083500415901560413746095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055666943934373609164063 3083500415901560413746095)
          ·
            refine ⟨4625250623852340620619143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3083500415901560413746095 4625250623852340620619143)
            ·
              refine ⟨6937875935778510930928715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4625250623852340620619143 6937875935778510930928715)
              ·
                refine ⟨10406813903667766396393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6937875935778510930928715 10406813903667766396393073)
                ·
                  refine ⟨7805110427750824797294805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10406813903667766396393073 7805110427750824797294805)
                  ·
                    refine ⟨182932275650409956186597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7805110427750824797294805 182932275650409956186597)
                    ·
                      rfl

theorem cell22_534389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_534389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534389 prefixEnd_534389 := by exact prefixLift 534389
  have htrace : WordTrace (prefixWord ++ tailWord_534389) baseStart_534389 baseEnd_534389 := by
    simpa [prefixWord, tailWord_534389, baseEnd_534389] using wordTrace_append hprefix tailTrace_534389
  have hstable : (prefixWord ++ tailWord_534389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534389).length < 2 ^ (prefixWord ++ tailWord_534389).sum := by decide
  have hdescent : baseEnd_534389 < baseStart_534389 := by decide
  rcases family_descends (prefixWord ++ tailWord_534389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534423 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 3, 3]
def baseStart_534423 : Nat := 118140960795 + 534423 * 2 ^ 59
def prefixEnd_534423 : Nat := 4983230072969 + 3 ^ 40 * 534423 * 2
def baseEnd_534423 : Nat := 182943914545245200836493

theorem tailTrace_534423 : CollatzResearch.WordTrace tailWord_534423 prefixEnd_534423 182943914545245200836493 := by
  unfold tailWord_534423
  simp only [CollatzResearch.WordTrace]
  refine ⟨19492008142884218026959923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12994672095256145351306615 19492008142884218026959923)
  ·
    refine ⟨29238012214326327040439885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19492008142884218026959923 29238012214326327040439885)
    ·
      refine ⟨10964254580372372640164957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29238012214326327040439885 10964254580372372640164957)
      ·
        refine ⟨4111595467639639740061859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10964254580372372640164957 4111595467639639740061859)
        ·
          refine ⟨6167393201459459610092789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111595467639639740061859 6167393201459459610092789)
          ·
            refine ⟨578193112636824338446199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6167393201459459610092789 578193112636824338446199)
            ·
              refine ⟨867289668955236507669299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578193112636824338446199 867289668955236507669299)
              ·
                refine ⟨1300934503432854761503949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867289668955236507669299 1300934503432854761503949)
                ·
                  refine ⟨487850438787320535563981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1300934503432854761503949 487850438787320535563981)
                  ·
                    refine ⟨182943914545245200836493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 487850438787320535563981 182943914545245200836493)
                    ·
                      rfl

theorem cell22_534423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_534423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534423 prefixEnd_534423 := by exact prefixLift 534423
  have htrace : WordTrace (prefixWord ++ tailWord_534423) baseStart_534423 baseEnd_534423 := by
    simpa [prefixWord, tailWord_534423, baseEnd_534423] using wordTrace_append hprefix tailTrace_534423
  have hstable : (prefixWord ++ tailWord_534423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534423).length < 2 ^ (prefixWord ++ tailWord_534423).sum := by decide
  have hdescent : baseEnd_534423 < baseStart_534423 := by decide
  rcases family_descends (prefixWord ++ tailWord_534423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534436 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_534436 : Nat := 118140960795 + 534436 * 2 ^ 59
def prefixEnd_534436 : Nat := 4983230072969 + 3 ^ 40 * 534436 * 2
def baseEnd_534436 : Nat := 60982788236972500087151

theorem tailTrace_534436 : CollatzResearch.WordTrace tailWord_534436 prefixEnd_534436 60982788236972500087151 := by
  unfold tailWord_534436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746241145918560623591581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12994988194558080831455441 9746241145918560623591581)
  ·
    refine ⟨3654840429719460233846843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9746241145918560623591581 3654840429719460233846843)
    ·
      refine ⟨5482260644579190350770265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3654840429719460233846843 5482260644579190350770265)
      ·
        refine ⟨4111695483434392763077699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5482260644579190350770265 4111695483434392763077699)
        ·
          refine ⟨6167543225151589144616549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4111695483434392763077699 6167543225151589144616549)
          ·
            refine ⟨1156414354715922964615603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6167543225151589144616549 1156414354715922964615603)
            ·
              refine ⟨1734621532073884446923405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156414354715922964615603 1734621532073884446923405)
              ·
                refine ⟨650483074527706667596277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1734621532073884446923405 650483074527706667596277)
                ·
                  refine ⟨60982788236972500087151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650483074527706667596277 60982788236972500087151)
                  ·
                    rfl

theorem cell22_534436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_534436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534436 prefixEnd_534436 := by exact prefixLift 534436
  have htrace : WordTrace (prefixWord ++ tailWord_534436) baseStart_534436 baseEnd_534436 := by
    simpa [prefixWord, tailWord_534436, baseEnd_534436] using wordTrace_append hprefix tailTrace_534436
  have hstable : (prefixWord ++ tailWord_534436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534436).length < 2 ^ (prefixWord ++ tailWord_534436).sum := by decide
  have hdescent : baseEnd_534436 < baseStart_534436 := by decide
  rcases family_descends (prefixWord ++ tailWord_534436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534479 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_534479 : Nat := 118140960795 + 534479 * 2 ^ 59
def prefixEnd_534479 : Nat := 4983230072969 + 3 ^ 40 * 534479 * 2
def baseEnd_534479 : Nat := 182963084489679721436321

theorem tailTrace_534479 : CollatzResearch.WordTrace tailWord_534479 prefixEnd_534479 182963084489679721436321 := by
  unfold tailWord_534479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19494050630681339590998491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12996033753787559727332327 19494050630681339590998491)
  ·
    refine ⟨29241075946022009386497737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19494050630681339590998491 29241075946022009386497737)
    ·
      refine ⟨21930806959516507039873303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29241075946022009386497737 21930806959516507039873303)
      ·
        refine ⟨32896210439274760559809955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21930806959516507039873303 32896210439274760559809955)
        ·
          refine ⟨49344315658912140839714933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32896210439274760559809955 49344315658912140839714933)
          ·
            refine ⟨4626029593023013203723275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49344315658912140839714933 4626029593023013203723275)
            ·
              refine ⟨6939044389534519805584913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4626029593023013203723275 6939044389534519805584913)
              ·
                refine ⟨5204283292150889854188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6939044389534519805584913 5204283292150889854188685)
                ·
                  refine ⟨1951606234556583695320757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5204283292150889854188685 1951606234556583695320757)
                  ·
                    refine ⟨182963084489679721436321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1951606234556583695320757 182963084489679721436321)
                    ·
                      rfl

theorem cell22_534479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_534479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534479 prefixEnd_534479 := by exact prefixLift 534479
  have htrace : WordTrace (prefixWord ++ tailWord_534479) baseStart_534479 baseEnd_534479 := by
    simpa [prefixWord, tailWord_534479, baseEnd_534479] using wordTrace_append hprefix tailTrace_534479
  have hstable : (prefixWord ++ tailWord_534479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534479).length < 2 ^ (prefixWord ++ tailWord_534479).sum := by decide
  have hdescent : baseEnd_534479 < baseStart_534479 := by decide
  rcases family_descends (prefixWord ++ tailWord_534479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534592 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_534592 : Nat := 118140960795 + 534592 * 2 ^ 59
def prefixEnd_534592 : Nat := 4983230072969 + 3 ^ 40 * 534592 * 2
def baseEnd_534592 : Nat := 183001766698985093360975

theorem tailTrace_534592 : CollatzResearch.WordTrace tailWord_534592 prefixEnd_534592 183001766698985093360975 := by
  unfold tailWord_534592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9749086039635979944931015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12998781386181306593241353 9749086039635979944931015)
  ·
    refine ⟨14623629059453969917396523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9749086039635979944931015 14623629059453969917396523)
    ·
      refine ⟨21935443589180954876094785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623629059453969917396523 21935443589180954876094785)
      ·
        refine ⟨16451582691885716157071089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21935443589180954876094785 16451582691885716157071089)
        ·
          refine ⟨12338687018914287117803317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16451582691885716157071089 12338687018914287117803317)
          ·
            refine ⟨1156751908023214417294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12338687018914287117803317 1156751908023214417294061)
            ·
              refine ⟨433781965508705406485273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1156751908023214417294061 433781965508705406485273)
              ·
                refine ⟨325336474131529054863955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433781965508705406485273 325336474131529054863955)
                ·
                  refine ⟨488004711197293582295933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325336474131529054863955 488004711197293582295933)
                  ·
                    refine ⟨183001766698985093360975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488004711197293582295933 183001766698985093360975)
                    ·
                      rfl

theorem cell22_534592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_534592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534592 prefixEnd_534592 := by exact prefixLift 534592
  have htrace : WordTrace (prefixWord ++ tailWord_534592) baseStart_534592 baseEnd_534592 := by
    simpa [prefixWord, tailWord_534592, baseEnd_534592] using wordTrace_append hprefix tailTrace_534592
  have hstable : (prefixWord ++ tailWord_534592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534592).length < 2 ^ (prefixWord ++ tailWord_534592).sum := by decide
  have hdescent : baseEnd_534592 < baseStart_534592 := by decide
  rcases family_descends (prefixWord ++ tailWord_534592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534601 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_534601 : Nat := 118140960795 + 534601 * 2 ^ 59
def prefixEnd_534601 : Nat := 4983230072969 + 3 ^ 40 * 534601 * 2
def baseEnd_534601 : Nat := 183004847582912069885947

theorem tailTrace_534601 : CollatzResearch.WordTrace tailWord_534601 prefixEnd_534601 183004847582912069885947 := by
  unfold tailWord_534601
  simp only [CollatzResearch.WordTrace]
  refine ⟨19498500336239354426939657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999000224159569617959771 19498500336239354426939657)
  ·
    refine ⟨14623875252179515820204743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19498500336239354426939657 14623875252179515820204743)
    ·
      refine ⟨21935812878269273730307115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14623875252179515820204743 21935812878269273730307115)
      ·
        refine ⟨32903719317403910595460673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21935812878269273730307115 32903719317403910595460673)
        ·
          refine ⟨24677789488052932946595505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32903719317403910595460673 24677789488052932946595505)
          ·
            refine ⟨18508342116039699709946629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24677789488052932946595505 18508342116039699709946629)
            ·
              refine ⟨3470314146757443695614993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18508342116039699709946629 3470314146757443695614993)
              ·
                refine ⟨2602735610068082771711245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3470314146757443695614993 2602735610068082771711245)
                ·
                  refine ⟨976025853775531039391717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2602735610068082771711245 976025853775531039391717)
                  ·
                    refine ⟨183004847582912069885947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976025853775531039391717 183004847582912069885947)
                    ·
                      rfl

theorem cell22_534601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_534601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534601 prefixEnd_534601 := by exact prefixLift 534601
  have htrace : WordTrace (prefixWord ++ tailWord_534601) baseStart_534601 baseEnd_534601 := by
    simpa [prefixWord, tailWord_534601, baseEnd_534601] using wordTrace_append hprefix tailTrace_534601
  have hstable : (prefixWord ++ tailWord_534601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534601).length < 2 ^ (prefixWord ++ tailWord_534601).sum := by decide
  have hdescent : baseEnd_534601 < baseStart_534601 := by decide
  rcases family_descends (prefixWord ++ tailWord_534601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534633 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 4]
def baseStart_534633 : Nat := 118140960795 + 534633 * 2 ^ 59
def prefixEnd_534633 : Nat := 4983230072969 + 3 ^ 40 * 534633 * 2
def baseEnd_534633 : Nat := 61005267278958217695283

theorem tailTrace_534633 : CollatzResearch.WordTrace tailWord_534633 prefixEnd_534633 61005267278958217695283 := by
  unfold tailWord_534633
  simp only [CollatzResearch.WordTrace]
  refine ⟨19499667472123423892104553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12999778314748949261403035 19499667472123423892104553)
  ·
    refine ⟨14624750604092567919078415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19499667472123423892104553 14624750604092567919078415)
    ·
      refine ⟨21937125906138851878617623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14624750604092567919078415 21937125906138851878617623)
      ·
        refine ⟨32905688859208277817926435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21937125906138851878617623 32905688859208277817926435)
        ·
          refine ⟨49358533288812416726889653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32905688859208277817926435 49358533288812416726889653)
          ·
            refine ⟨4627362495826164068145905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49358533288812416726889653 4627362495826164068145905)
            ·
              refine ⟨3470521871869623051109429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4627362495826164068145905 3470521871869623051109429)
              ·
                refine ⟨325361425487777161041509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3470521871869623051109429 325361425487777161041509)
                ·
                  refine ⟨61005267278958217695283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325361425487777161041509 61005267278958217695283)
                  ·
                    rfl

theorem cell22_534633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_534633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534633 prefixEnd_534633 := by exact prefixLift 534633
  have htrace : WordTrace (prefixWord ++ tailWord_534633) baseStart_534633 baseEnd_534633 := by
    simpa [prefixWord, tailWord_534633, baseEnd_534633] using wordTrace_append hprefix tailTrace_534633
  have hstable : (prefixWord ++ tailWord_534633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534633).length < 2 ^ (prefixWord ++ tailWord_534633).sum := by decide
  have hdescent : baseEnd_534633 < baseStart_534633 := by decide
  rcases family_descends (prefixWord ++ tailWord_534633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534686 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_534686 : Nat := 118140960795 + 534686 * 2 ^ 59
def prefixEnd_534686 : Nat := 4983230072969 + 3 ^ 40 * 534686 * 2
def baseEnd_534686 : Nat := 183033944820000181510687

theorem tailTrace_534686 : CollatzResearch.WordTrace tailWord_534686 prefixEnd_534686 183033944820000181510687 := by
  unfold tailWord_534686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437700067616426742972989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13001067027287609295855941 2437700067616426742972989)
  ·
    refine ⟨914137525356160028614871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2437700067616426742972989 914137525356160028614871)
    ·
      refine ⟨1371206288034240042922307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914137525356160028614871 1371206288034240042922307)
      ·
        refine ⟨2056809432051360064383461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371206288034240042922307 2056809432051360064383461)
        ·
          refine ⟨385651768509630012071899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2056809432051360064383461 385651768509630012071899)
          ·
            refine ⟨578477652764445018107849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385651768509630012071899 578477652764445018107849)
            ·
              refine ⟨433858239573333763580887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578477652764445018107849 433858239573333763580887)
              ·
                refine ⟨650787359360000645371331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433858239573333763580887 650787359360000645371331)
                ·
                  refine ⟨976181039040000968056997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650787359360000645371331 976181039040000968056997)
                  ·
                    refine ⟨183033944820000181510687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976181039040000968056997 183033944820000181510687)
                    ·
                      rfl

theorem cell22_534686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_534686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534686 prefixEnd_534686 := by exact prefixLift 534686
  have htrace : WordTrace (prefixWord ++ tailWord_534686) baseStart_534686 baseEnd_534686 := by
    simpa [prefixWord, tailWord_534686, baseEnd_534686] using wordTrace_append hprefix tailTrace_534686
  have hstable : (prefixWord ++ tailWord_534686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534686).length < 2 ^ (prefixWord ++ tailWord_534686).sum := by decide
  have hdescent : baseEnd_534686 < baseStart_534686 := by decide
  rcases family_descends (prefixWord ++ tailWord_534686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534693 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_534693 : Nat := 118140960795 + 534693 * 2 ^ 59
def prefixEnd_534693 : Nat := 4983230072969 + 3 ^ 40 * 534693 * 2
def baseEnd_534693 : Nat := 183036341063054496585665

theorem tailTrace_534693 : CollatzResearch.WordTrace tailWord_534693 prefixEnd_534693 183036341063054496585665 := by
  unfold tailWord_534693
  simp only [CollatzResearch.WordTrace]
  refine ⟨19501855851906054139288733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13001237234604036092859155 19501855851906054139288733)
  ·
    refine ⟨7313195944464770302233275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19501855851906054139288733 7313195944464770302233275)
    ·
      refine ⟨10969793916697155453349913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7313195944464770302233275 10969793916697155453349913)
      ·
        refine ⟨8227345437522866590012435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10969793916697155453349913 8227345437522866590012435)
        ·
          refine ⟨12341018156284299885018653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8227345437522866590012435 12341018156284299885018653)
          ·
            refine ⟨4627881808606612456881995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12341018156284299885018653 4627881808606612456881995)
            ·
              refine ⟨6941822712909918685322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4627881808606612456881995 6941822712909918685322993)
              ·
                refine ⟨5206367034682439013992245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6941822712909918685322993 5206367034682439013992245)
                ·
                  refine ⟨488096909501478657561773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5206367034682439013992245 488096909501478657561773)
                  ·
                    refine ⟨183036341063054496585665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488096909501478657561773 183036341063054496585665)
                    ·
                      rfl

theorem cell22_534693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_534693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534693 prefixEnd_534693 := by exact prefixLift 534693
  have htrace : WordTrace (prefixWord ++ tailWord_534693) baseStart_534693 baseEnd_534693 := by
    simpa [prefixWord, tailWord_534693, baseEnd_534693] using wordTrace_append hprefix tailTrace_534693
  have hstable : (prefixWord ++ tailWord_534693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534693).length < 2 ^ (prefixWord ++ tailWord_534693).sum := by decide
  have hdescent : baseEnd_534693 < baseStart_534693 := by decide
  rcases family_descends (prefixWord ++ tailWord_534693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534736 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_534736 : Nat := 118140960795 + 534736 * 2 ^ 59
def prefixEnd_534736 : Nat := 4983230072969 + 3 ^ 40 * 534736 * 2
def baseEnd_534736 : Nat := 183051060841816717760533

theorem tailTrace_534736 : CollatzResearch.WordTrace tailWord_534736 prefixEnd_534736 183051060841816717760533 := by
  unfold tailWord_534736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751712095375136241552031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13002282793833514988736041 9751712095375136241552031)
  ·
    refine ⟨14627568143062704362328047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751712095375136241552031 14627568143062704362328047)
    ·
      refine ⟨21941352214594056543492071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14627568143062704362328047 21941352214594056543492071)
      ·
        refine ⟨32912028321891084815238107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21941352214594056543492071 32912028321891084815238107)
        ·
          refine ⟨49368042482836627222857161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32912028321891084815238107 49368042482836627222857161)
          ·
            refine ⟨37026031862127470417142871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49368042482836627222857161 37026031862127470417142871)
            ·
              refine ⟨55539047793191205625714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37026031862127470417142871 55539047793191205625714307)
              ·
                refine ⟨83308571689786808438571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55539047793191205625714307 83308571689786808438571461)
                ·
                  refine ⟨15620357191835026582232149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83308571689786808438571461 15620357191835026582232149)
                  ·
                    refine ⟨183051060841816717760533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15620357191835026582232149 183051060841816717760533)
                    ·
                      rfl

theorem cell22_534736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_534736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534736 prefixEnd_534736 := by exact prefixLift 534736
  have htrace : WordTrace (prefixWord ++ tailWord_534736) baseStart_534736 baseEnd_534736 := by
    simpa [prefixWord, tailWord_534736, baseEnd_534736] using wordTrace_append hprefix tailTrace_534736
  have hstable : (prefixWord ++ tailWord_534736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534736).length < 2 ^ (prefixWord ++ tailWord_534736).sum := by decide
  have hdescent : baseEnd_534736 < baseStart_534736 := by decide
  rcases family_descends (prefixWord ++ tailWord_534736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534744 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_534744 : Nat := 118140960795 + 534744 * 2 ^ 59
def prefixEnd_534744 : Nat := 4983230072969 + 3 ^ 40 * 534744 * 2
def baseEnd_534744 : Nat := 183053799405307363560509

theorem tailTrace_534744 : CollatzResearch.WordTrace tailWord_534744 prefixEnd_534744 183053799405307363560509 := by
  unfold tailWord_534744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751857987360644924697643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13002477316480859899596857 9751857987360644924697643)
  ·
    refine ⟨14627786981040967387046465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9751857987360644924697643 14627786981040967387046465)
    ·
      refine ⟨10970840235780725540284849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14627786981040967387046465 10970840235780725540284849)
      ·
        refine ⟨8228130176835544155213637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10970840235780725540284849 8228130176835544155213637)
        ·
          refine ⟨1542774408156664529102557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8228130176835544155213637 1542774408156664529102557)
          ·
            refine ⟨578540403058749198413459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1542774408156664529102557 578540403058749198413459)
            ·
              refine ⟨867810604588123797620189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578540403058749198413459 867810604588123797620189)
              ·
                refine ⟨325428976720546424107571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867810604588123797620189 325428976720546424107571)
                ·
                  refine ⟨488143465080819636161357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325428976720546424107571 488143465080819636161357)
                  ·
                    refine ⟨183053799405307363560509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488143465080819636161357 183053799405307363560509)
                    ·
                      rfl

theorem cell22_534744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_534744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534744 prefixEnd_534744 := by exact prefixLift 534744
  have htrace : WordTrace (prefixWord ++ tailWord_534744) baseStart_534744 baseEnd_534744 := by
    simpa [prefixWord, tailWord_534744, baseEnd_534744] using wordTrace_append hprefix tailTrace_534744
  have hstable : (prefixWord ++ tailWord_534744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534744).length < 2 ^ (prefixWord ++ tailWord_534744).sum := by decide
  have hdescent : baseEnd_534744 < baseStart_534744 := by decide
  rcases family_descends (prefixWord ++ tailWord_534744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534783 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_534783 : Nat := 118140960795 + 534783 * 2 ^ 59
def prefixEnd_534783 : Nat := 4983230072969 + 3 ^ 40 * 534783 * 2
def baseEnd_534783 : Nat := 183067149902324261835389

theorem tailTrace_534783 : CollatzResearch.WordTrace tailWord_534783 prefixEnd_534783 183067149902324261835389 := by
  unfold tailWord_534783
  simp only [CollatzResearch.WordTrace]
  refine ⟨19505138421579999510065003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13003425614386666340043335 19505138421579999510065003)
  ·
    refine ⟨29257707632369999265097505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19505138421579999510065003 29257707632369999265097505)
    ·
      refine ⟨21943280724277499448823129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29257707632369999265097505 21943280724277499448823129)
      ·
        refine ⟨16457460543208124586617347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21943280724277499448823129 16457460543208124586617347)
        ·
          refine ⟨24686190814812186879926021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16457460543208124586617347 24686190814812186879926021)
          ·
            refine ⟨4628660777777285039986129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24686190814812186879926021 4628660777777285039986129)
            ·
              refine ⟨3471495583332963779989597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628660777777285039986129 3471495583332963779989597)
              ·
                refine ⟨1301810843749861417496099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471495583332963779989597 1301810843749861417496099)
                ·
                  refine ⟨1952716265624792126244149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1301810843749861417496099 1952716265624792126244149)
                  ·
                    refine ⟨183067149902324261835389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1952716265624792126244149 183067149902324261835389)
                    ·
                      rfl

theorem cell22_534783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_534783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534783 prefixEnd_534783 := by exact prefixLift 534783
  have htrace : WordTrace (prefixWord ++ tailWord_534783) baseStart_534783 baseEnd_534783 := by
    simpa [prefixWord, tailWord_534783, baseEnd_534783] using wordTrace_append hprefix tailTrace_534783
  have hstable : (prefixWord ++ tailWord_534783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534783).length < 2 ^ (prefixWord ++ tailWord_534783).sum := by decide
  have hdescent : baseEnd_534783 < baseStart_534783 := by decide
  rcases family_descends (prefixWord ++ tailWord_534783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534813 : List Nat := [1, 4, 2, 3, 12]
def baseStart_534813 : Nat := 118140960795 + 534813 * 2 ^ 59
def prefixEnd_534813 : Nat := 4983230072969 + 3 ^ 40 * 534813 * 2
def baseEnd_534813 : Nat := 753405018581951372779

theorem tailTrace_534813 : CollatzResearch.WordTrace tailWord_534813 prefixEnd_534813 753405018581951372779 := by
  unfold tailWord_534813
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506232611471314633657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13004155074314209755771395 19506232611471314633657093)
  ·
    refine ⟨3657418614650871493810705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19506232611471314633657093 3657418614650871493810705)
    ·
      refine ⟨2743063960988153620358029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3657418614650871493810705 2743063960988153620358029)
      ·
        refine ⟨1028648985370557607634261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2743063960988153620358029 1028648985370557607634261)
        ·
          refine ⟨753405018581951372779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1028648985370557607634261 753405018581951372779)
          ·
            rfl

theorem cell22_534813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 12].length) (baseStart_534813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534813 prefixEnd_534813 := by exact prefixLift 534813
  have htrace : WordTrace (prefixWord ++ tailWord_534813) baseStart_534813 baseEnd_534813 := by
    simpa [prefixWord, tailWord_534813, baseEnd_534813] using wordTrace_append hprefix tailTrace_534813
  have hstable : (prefixWord ++ tailWord_534813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534813).length < 2 ^ (prefixWord ++ tailWord_534813).sum := by decide
  have hdescent : baseEnd_534813 < baseStart_534813 := by decide
  rcases family_descends (prefixWord ++ tailWord_534813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534815 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_534815 : Nat := 118140960795 + 534815 * 2 ^ 59
def prefixEnd_534815 : Nat := 4983230072969 + 3 ^ 40 * 534815 * 2
def baseEnd_534815 : Nat := 183078104156286845035291

theorem tailTrace_534815 : CollatzResearch.WordTrace tailWord_534815 prefixEnd_534815 183078104156286845035291 := by
  unfold tailWord_534815
  simp only [CollatzResearch.WordTrace]
  refine ⟨19506305557464068975229899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13004203704976045983486599 19506305557464068975229899)
  ·
    refine ⟨29259458336196103462844849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19506305557464068975229899 29259458336196103462844849)
    ·
      refine ⟨21944593752147077597133637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29259458336196103462844849 21944593752147077597133637)
      ·
        refine ⟨4114611328527577049462557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21944593752147077597133637 4114611328527577049462557)
        ·
          refine ⟨1542979248197841393548459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4114611328527577049462557 1542979248197841393548459)
          ·
            refine ⟨2314468872296762090322689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542979248197841393548459 2314468872296762090322689)
            ·
              refine ⟨1735851654222571567742017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314468872296762090322689 1735851654222571567742017)
              ·
                refine ⟨1301888740666928675806513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1735851654222571567742017 1301888740666928675806513)
                ·
                  refine ⟨976416555500196506854885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301888740666928675806513 976416555500196506854885)
                  ·
                    refine ⟨183078104156286845035291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976416555500196506854885 183078104156286845035291)
                    ·
                      rfl

theorem cell22_534815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_534815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534815 prefixEnd_534815 := by exact prefixLift 534815
  have htrace : WordTrace (prefixWord ++ tailWord_534815) baseStart_534815 baseEnd_534815 := by
    simpa [prefixWord, tailWord_534815, baseEnd_534815] using wordTrace_append hprefix tailTrace_534815
  have hstable : (prefixWord ++ tailWord_534815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534815).length < 2 ^ (prefixWord ++ tailWord_534815).sum := by decide
  have hdescent : baseEnd_534815 < baseStart_534815 := by decide
  rcases family_descends (prefixWord ++ tailWord_534815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534849 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_534849 : Nat := 118140960795 + 534849 * 2 ^ 59
def prefixEnd_534849 : Nat := 4983230072969 + 3 ^ 40 * 534849 * 2
def baseEnd_534849 : Nat := 183089743051122089685187

theorem tailTrace_534849 : CollatzResearch.WordTrace tailWord_534849 prefixEnd_534849 183089743051122089685187 := by
  unfold tailWord_534849
  simp only [CollatzResearch.WordTrace]
  refine ⟨19507545639340892781967601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13005030426227261854645067 19507545639340892781967601)
  ·
    refine ⟨14630659229505669586475701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19507545639340892781967601 14630659229505669586475701)
    ·
      refine ⟨1371624302766156523732097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14630659229505669586475701 1371624302766156523732097)
      ·
        refine ⟨1028718227074617392799073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371624302766156523732097 1028718227074617392799073)
        ·
          refine ⟨771538670305963044599305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028718227074617392799073 771538670305963044599305)
          ·
            refine ⟨578654002729472283449479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771538670305963044599305 578654002729472283449479)
            ·
              refine ⟨867981004094208425174219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578654002729472283449479 867981004094208425174219)
              ·
                refine ⟨1301971506141312637761329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867981004094208425174219 1301971506141312637761329)
                ·
                  refine ⟨976478629605984478320997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1301971506141312637761329 976478629605984478320997)
                  ·
                    refine ⟨183089743051122089685187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976478629605984478320997 183089743051122089685187)
                    ·
                      rfl

theorem cell22_534849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_534849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534849 prefixEnd_534849 := by exact prefixLift 534849
  have htrace : WordTrace (prefixWord ++ tailWord_534849) baseStart_534849 baseEnd_534849 := by
    simpa [prefixWord, tailWord_534849, baseEnd_534849] using wordTrace_append hprefix tailTrace_534849
  have hstable : (prefixWord ++ tailWord_534849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534849).length < 2 ^ (prefixWord ++ tailWord_534849).sum := by decide
  have hdescent : baseEnd_534849 < baseStart_534849 := by decide
  rcases family_descends (prefixWord ++ tailWord_534849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534903 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 8]
def baseStart_534903 : Nat := 118140960795 + 534903 * 2 ^ 59
def prefixEnd_534903 : Nat := 4983230072969 + 3 ^ 40 * 534903 * 2
def baseEnd_534903 : Nat := 61036076118227982945007

theorem tailTrace_534903 : CollatzResearch.WordTrace tailWord_534903 prefixEnd_534903 61036076118227982945007 := by
  unfold tailWord_534903
  simp only [CollatzResearch.WordTrace]
  refine ⟨19509515181145260004433363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13006343454096840002955575 19509515181145260004433363)
  ·
    refine ⟨29264272771717890006650045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19509515181145260004433363 29264272771717890006650045)
    ·
      refine ⟨10974102289394208752493767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29264272771717890006650045 10974102289394208752493767)
      ·
        refine ⟨16461153434091313128740651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10974102289394208752493767 16461153434091313128740651)
        ·
          refine ⟨24691730151136969693110977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16461153434091313128740651 24691730151136969693110977)
          ·
            refine ⟨18518797613352727269833233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24691730151136969693110977 18518797613352727269833233)
            ·
              refine ⟨13889098210014545452374925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18518797613352727269833233 13889098210014545452374925)
              ·
                refine ⟨5208411828755454544640597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13889098210014545452374925 5208411828755454544640597)
                ·
                  refine ⟨61036076118227982945007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5208411828755454544640597 61036076118227982945007)
                  ·
                    rfl

theorem cell22_534903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_534903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534903 prefixEnd_534903 := by exact prefixLift 534903
  have htrace : WordTrace (prefixWord ++ tailWord_534903) baseStart_534903 baseEnd_534903 := by
    simpa [prefixWord, tailWord_534903, baseEnd_534903] using wordTrace_append hprefix tailTrace_534903
  have hstable : (prefixWord ++ tailWord_534903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534903).length < 2 ^ (prefixWord ++ tailWord_534903).sum := by decide
  have hdescent : baseEnd_534903 < baseStart_534903 := by decide
  rcases family_descends (prefixWord ++ tailWord_534903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534967 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_534967 : Nat := 118140960795 + 534967 * 2 ^ 59
def prefixEnd_534967 : Nat := 4983230072969 + 3 ^ 40 * 534967 * 2
def baseEnd_534967 : Nat := 183130136862609115234825

theorem tailTrace_534967 : CollatzResearch.WordTrace tailWord_534967 prefixEnd_534967 183130136862609115234825 := by
  unfold tailWord_534967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19511849452913398934763155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13007899635275599289842103 19511849452913398934763155)
  ·
    refine ⟨29267774179370098402144733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19511849452913398934763155 29267774179370098402144733)
    ·
      refine ⟨10975415317263786900804275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29267774179370098402144733 10975415317263786900804275)
      ·
        refine ⟨16463122975895680351206413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10975415317263786900804275 16463122975895680351206413)
        ·
          refine ⟨6173671115960880131702405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16463122975895680351206413 6173671115960880131702405)
          ·
            refine ⟨1157563334242665024694201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6173671115960880131702405 1157563334242665024694201)
            ·
              refine ⟨868172500681998768520651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157563334242665024694201 868172500681998768520651)
              ·
                refine ⟨1302258751022998152780977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868172500681998768520651 1302258751022998152780977)
                ·
                  refine ⟨976694063267248614585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302258751022998152780977 976694063267248614585733)
                  ·
                    refine ⟨183130136862609115234825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 976694063267248614585733 183130136862609115234825)
                    ·
                      rfl

theorem cell22_534967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_534967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534967 prefixEnd_534967 := by exact prefixLift 534967
  have htrace : WordTrace (prefixWord ++ tailWord_534967) baseStart_534967 baseEnd_534967 := by
    simpa [prefixWord, tailWord_534967, baseEnd_534967] using wordTrace_append hprefix tailTrace_534967
  have hstable : (prefixWord ++ tailWord_534967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534967).length < 2 ^ (prefixWord ++ tailWord_534967).sum := by decide
  have hdescent : baseEnd_534967 < baseStart_534967 := by decide
  rcases family_descends (prefixWord ++ tailWord_534967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_534988 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_534988 : Nat := 118140960795 + 534988 * 2 ^ 59
def prefixEnd_534988 : Nat := 4983230072969 + 3 ^ 40 * 534988 * 2
def baseEnd_534988 : Nat := 61045775197257353486587

theorem tailTrace_534988 : CollatzResearch.WordTrace tailWord_534988 prefixEnd_534988 61045775197257353486587 := by
  unfold tailWord_534988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756307692918659760638809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13008410257224879680851745 9756307692918659760638809)
  ·
    refine ⟨7317230769688994820479107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9756307692918659760638809 7317230769688994820479107)
    ·
      refine ⟨10975846154533492230718661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7317230769688994820479107 10975846154533492230718661)
      ·
        refine ⟨2057971153975029793259749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10975846154533492230718661 2057971153975029793259749)
        ·
          refine ⟨385869591370318086236203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2057971153975029793259749 385869591370318086236203)
          ·
            refine ⟨578804387055477129354305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385869591370318086236203 578804387055477129354305)
            ·
              refine ⟨434103290291607847015729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578804387055477129354305 434103290291607847015729)
              ·
                refine ⟨325577467718705885261797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434103290291607847015729 325577467718705885261797)
                ·
                  refine ⟨61045775197257353486587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325577467718705885261797 61045775197257353486587)
                  ·
                    rfl

theorem cell22_534988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_534988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_534988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_534988 prefixEnd_534988 := by exact prefixLift 534988
  have htrace : WordTrace (prefixWord ++ tailWord_534988) baseStart_534988 baseEnd_534988 := by
    simpa [prefixWord, tailWord_534988, baseEnd_534988] using wordTrace_append hprefix tailTrace_534988
  have hstable : (prefixWord ++ tailWord_534988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_534988).length < 2 ^ (prefixWord ++ tailWord_534988).sum := by decide
  have hdescent : baseEnd_534988 < baseStart_534988 := by decide
  rcases family_descends (prefixWord ++ tailWord_534988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535025 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_535025 : Nat := 118140960795 + 535025 * 2 ^ 59
def prefixEnd_535025 : Nat := 4983230072969 + 3 ^ 40 * 535025 * 2
def baseEnd_535025 : Nat := 183149991447916297284647

theorem tailTrace_535025 : CollatzResearch.WordTrace tailWord_535025 prefixEnd_535025 183149991447916297284647 := by
  unfold tailWord_535025
  simp only [CollatzResearch.WordTrace]
  refine ⟨19513964886703274840374529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13009309924468849893583019 19513964886703274840374529)
  ·
    refine ⟨14635473665027456130280897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19513964886703274840374529 14635473665027456130280897)
    ·
      refine ⟨10976605248770592097710673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14635473665027456130280897 10976605248770592097710673)
      ·
        refine ⟨8232453936577944073283005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10976605248770592097710673 8232453936577944073283005)
        ·
          refine ⟨3087170226216729027481127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8232453936577944073283005 3087170226216729027481127)
          ·
            refine ⟨4630755339325093541221691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087170226216729027481127 4630755339325093541221691)
            ·
              refine ⟨6946133008987640311832537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4630755339325093541221691 6946133008987640311832537)
              ·
                refine ⟨5209599756740730233874403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6946133008987640311832537 5209599756740730233874403)
                ·
                  refine ⟨7814399635111095350811605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5209599756740730233874403 7814399635111095350811605)
                  ·
                    refine ⟨183149991447916297284647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7814399635111095350811605 183149991447916297284647)
                    ·
                      rfl

theorem cell22_535025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_535025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535025 prefixEnd_535025 := by exact prefixLift 535025
  have htrace : WordTrace (prefixWord ++ tailWord_535025) baseStart_535025 baseEnd_535025 := by
    simpa [prefixWord, tailWord_535025, baseEnd_535025] using wordTrace_append hprefix tailTrace_535025
  have hstable : (prefixWord ++ tailWord_535025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535025).length < 2 ^ (prefixWord ++ tailWord_535025).sum := by decide
  have hdescent : baseEnd_535025 < baseStart_535025 := by decide
  rcases family_descends (prefixWord ++ tailWord_535025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535044 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 5]
def baseStart_535044 : Nat := 118140960795 + 535044 * 2 ^ 59
def prefixEnd_535044 : Nat := 4983230072969 + 3 ^ 40 * 535044 * 2
def baseEnd_535044 : Nat := 61052165178735527019863

theorem tailTrace_535044 : CollatzResearch.WordTrace tailWord_535044 prefixEnd_535044 61052165178735527019863 := by
  unfold tailWord_535044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757328936817220542658093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13009771915756294056877457 9757328936817220542658093)
  ·
    refine ⟨3658998351306457703496785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9757328936817220542658093 3658998351306457703496785)
    ·
      refine ⟨2744248763479843277622589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658998351306457703496785 2744248763479843277622589)
      ·
        refine ⟨1029093286304941229108471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2744248763479843277622589 1029093286304941229108471)
        ·
          refine ⟨1543639929457411843662707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029093286304941229108471 1543639929457411843662707)
          ·
            refine ⟨2315459894186117765494061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543639929457411843662707 2315459894186117765494061)
            ·
              refine ⟨868297460319794162060273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2315459894186117765494061 868297460319794162060273)
              ·
                refine ⟨651223095239845621545205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868297460319794162060273 651223095239845621545205)
                ·
                  refine ⟨61052165178735527019863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651223095239845621545205 61052165178735527019863)
                  ·
                    rfl

theorem cell22_535044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_535044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535044 prefixEnd_535044 := by exact prefixLift 535044
  have htrace : WordTrace (prefixWord ++ tailWord_535044) baseStart_535044 baseEnd_535044 := by
    simpa [prefixWord, tailWord_535044, baseEnd_535044] using wordTrace_append hprefix tailTrace_535044
  have hstable : (prefixWord ++ tailWord_535044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535044).length < 2 ^ (prefixWord ++ tailWord_535044).sum := by decide
  have hdescent : baseEnd_535044 < baseStart_535044 := by decide
  rcases family_descends (prefixWord ++ tailWord_535044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535055 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 6]
def baseStart_535055 : Nat := 118140960795 + 535055 * 2 ^ 59
def prefixEnd_535055 : Nat := 4983230072969 + 3 ^ 40 * 535055 * 2
def baseEnd_535055 : Nat := 61053420353668739678185

theorem tailTrace_535055 : CollatzResearch.WordTrace tailWord_535055 prefixEnd_535055 61053420353668739678185 := by
  unfold tailWord_535055
  simp only [CollatzResearch.WordTrace]
  refine ⟨19515059076594589963966619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13010039384396393309311079 19515059076594589963966619)
  ·
    refine ⟨29272588614891884945949929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19515059076594589963966619 29272588614891884945949929)
    ·
      refine ⟨21954441461168913709462447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29272588614891884945949929 21954441461168913709462447)
      ·
        refine ⟨32931662191753370564193671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21954441461168913709462447 32931662191753370564193671)
        ·
          refine ⟨49397493287630055846290507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32931662191753370564193671 49397493287630055846290507)
          ·
            refine ⟨74096239931445083769435761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49397493287630055846290507 74096239931445083769435761)
            ·
              refine ⟨55572179948583812827076821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74096239931445083769435761 55572179948583812827076821)
              ·
                refine ⟨1302472967544933113134613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55572179948583812827076821 1302472967544933113134613)
                ·
                  refine ⟨61053420353668739678185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302472967544933113134613 61053420353668739678185)
                  ·
                    rfl

theorem cell22_535055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_535055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535055 prefixEnd_535055 := by exact prefixLift 535055
  have htrace : WordTrace (prefixWord ++ tailWord_535055) baseStart_535055 baseEnd_535055 := by
    simpa [prefixWord, tailWord_535055, baseEnd_535055] using wordTrace_append hprefix tailTrace_535055
  have hstable : (prefixWord ++ tailWord_535055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535055).length < 2 ^ (prefixWord ++ tailWord_535055).sum := by decide
  have hdescent : baseEnd_535055 < baseStart_535055 := by decide
  rcases family_descends (prefixWord ++ tailWord_535055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535089 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 4]
def baseStart_535089 : Nat := 118140960795 + 535089 * 2 ^ 59
def prefixEnd_535089 : Nat := 4983230072969 + 3 ^ 40 * 535089 * 2
def baseEnd_535089 : Nat := 61057299985280487894817

theorem tailTrace_535089 : CollatzResearch.WordTrace tailWord_535089 prefixEnd_535089 61057299985280487894817 := by
  unfold tailWord_535089
  simp only [CollatzResearch.WordTrace]
  refine ⟨19516299158471413770704321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13010866105647609180469547 19516299158471413770704321)
  ·
    refine ⟨14637224368853560328028241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19516299158471413770704321 14637224368853560328028241)
    ·
      refine ⟨10977918276640170246021181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14637224368853560328028241 10977918276640170246021181)
      ·
        refine ⟨4116719353740063842257943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10977918276640170246021181 4116719353740063842257943)
        ·
          refine ⟨6175079030610095763386915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116719353740063842257943 6175079030610095763386915)
          ·
            refine ⟨9262618545915143645080373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6175079030610095763386915 9262618545915143645080373)
            ·
              refine ⟨868370488679544716726285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9262618545915143645080373 868370488679544716726285)
              ·
                refine ⟨325638933254829268772357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 868370488679544716726285 325638933254829268772357)
                ·
                  refine ⟨61057299985280487894817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325638933254829268772357 61057299985280487894817)
                  ·
                    rfl

theorem cell22_535089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_535089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535089 prefixEnd_535089 := by exact prefixLift 535089
  have htrace : WordTrace (prefixWord ++ tailWord_535089) baseStart_535089 baseEnd_535089 := by
    simpa [prefixWord, tailWord_535089, baseEnd_535089] using wordTrace_append hprefix tailTrace_535089
  have hstable : (prefixWord ++ tailWord_535089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535089).length < 2 ^ (prefixWord ++ tailWord_535089).sum := by decide
  have hdescent : baseEnd_535089 < baseStart_535089 := by decide
  rcases family_descends (prefixWord ++ tailWord_535089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535121 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_535121 : Nat := 118140960795 + 535121 * 2 ^ 59
def prefixEnd_535121 : Nat := 4983230072969 + 3 ^ 40 * 535121 * 2
def baseEnd_535121 : Nat := 183182854209804046884353

theorem tailTrace_535121 : CollatzResearch.WordTrace tailWord_535121 prefixEnd_535121 183182854209804046884353 := by
  unfold tailWord_535121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19517466294355483235869217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13011644196236988823912811 19517466294355483235869217)
  ·
    refine ⟨14638099720766612426901913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19517466294355483235869217 14638099720766612426901913)
    ·
      refine ⟨10978574790574959320176435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14638099720766612426901913 10978574790574959320176435)
      ·
        refine ⟨16467862185862438980264653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978574790574959320176435 16467862185862438980264653)
        ·
          refine ⟨6175448319698414617599245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16467862185862438980264653 6175448319698414617599245)
          ·
            refine ⟨2315793119886905481599717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6175448319698414617599245 2315793119886905481599717)
            ·
              refine ⟨434211209978794777799947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2315793119886905481599717 434211209978794777799947)
              ·
                refine ⟨651316814968192166699921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434211209978794777799947 651316814968192166699921)
                ·
                  refine ⟨488487611226144125024941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651316814968192166699921 488487611226144125024941)
                  ·
                    refine ⟨183182854209804046884353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488487611226144125024941 183182854209804046884353)
                    ·
                      rfl

theorem cell22_535121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_535121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535121 prefixEnd_535121 := by exact prefixLift 535121
  have htrace : WordTrace (prefixWord ++ tailWord_535121) baseStart_535121 baseEnd_535121 := by
    simpa [prefixWord, tailWord_535121, baseEnd_535121] using wordTrace_append hprefix tailTrace_535121
  have hstable : (prefixWord ++ tailWord_535121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535121).length < 2 ^ (prefixWord ++ tailWord_535121).sum := by decide
  have hdescent : baseEnd_535121 < baseStart_535121 := by decide
  rcases family_descends (prefixWord ++ tailWord_535121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535269 : List Nat := [1, 3, 1, 4, 1, 4, 8]
def baseStart_535269 : Nat := 118140960795 + 535269 * 2 ^ 59
def prefixEnd_535269 : Nat := 4983230072969 + 3 ^ 40 * 535269 * 2
def baseEnd_535269 : Nat := 6786426579051147932737

theorem tailTrace_535269 : CollatzResearch.WordTrace tailWord_535269 prefixEnd_535269 6786426579051147932737 := by
  unfold tailWord_535269
  simp only [CollatzResearch.WordTrace]
  refine ⟨19522864297819304512256861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13015242865212869674837907 19522864297819304512256861)
  ·
    refine ⟨7321074111682239192096323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19522864297819304512256861 7321074111682239192096323)
    ·
      refine ⟨10981611167523358788144485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321074111682239192096323 10981611167523358788144485)
      ·
        refine ⟨2059052093910629772777091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10981611167523358788144485 2059052093910629772777091)
        ·
          refine ⟨3088578140865944659165637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059052093910629772777091 3088578140865944659165637)
          ·
            refine ⟨579108401412364623593557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3088578140865944659165637 579108401412364623593557)
            ·
              refine ⟨6786426579051147932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 579108401412364623593557 6786426579051147932737)
              ·
                rfl

theorem cell22_535269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 8].length) (baseStart_535269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535269 prefixEnd_535269 := by exact prefixLift 535269
  have htrace : WordTrace (prefixWord ++ tailWord_535269) baseStart_535269 baseEnd_535269 := by
    simpa [prefixWord, tailWord_535269, baseEnd_535269] using wordTrace_append hprefix tailTrace_535269
  have hstable : (prefixWord ++ tailWord_535269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535269).length < 2 ^ (prefixWord ++ tailWord_535269).sum := by decide
  have hdescent : baseEnd_535269 < baseStart_535269 := by decide
  rcases family_descends (prefixWord ++ tailWord_535269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535329 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_535329 : Nat := 118140960795 + 535329 * 2 ^ 59
def prefixEnd_535329 : Nat := 4983230072969 + 3 ^ 40 * 535329 * 2
def baseEnd_535329 : Nat := 183254056860560837683715

theorem tailTrace_535329 : CollatzResearch.WordTrace tailWord_535329 prefixEnd_535329 183254056860560837683715 := by
  unfold tailWord_535329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19525052677601934759441041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13016701785067956506294027 19525052677601934759441041)
  ·
    refine ⟨14643789508201451069580781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19525052677601934759441041 14643789508201451069580781)
    ·
      refine ⟨5491421065575544151092793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14643789508201451069580781 5491421065575544151092793)
      ·
        refine ⟨4118565799181658113319595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491421065575544151092793 4118565799181658113319595)
        ·
          refine ⟨6177848698772487169979393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118565799181658113319595 6177848698772487169979393)
          ·
            refine ⟨4633386524079365377484545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6177848698772487169979393 4633386524079365377484545)
            ·
              refine ⟨3475039893059524033113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633386524079365377484545 3475039893059524033113409)
              ·
                refine ⟨2606279919794643024835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475039893059524033113409 2606279919794643024835057)
                ·
                  refine ⟨1954709939845982268626293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2606279919794643024835057 1954709939845982268626293)
                  ·
                    refine ⟨183254056860560837683715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1954709939845982268626293 183254056860560837683715)
                    ·
                      rfl

theorem cell22_535329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_535329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535329 prefixEnd_535329 := by exact prefixLift 535329
  have htrace : WordTrace (prefixWord ++ tailWord_535329) baseStart_535329 baseEnd_535329 := by
    simpa [prefixWord, tailWord_535329, baseEnd_535329] using wordTrace_append hprefix tailTrace_535329
  have hstable : (prefixWord ++ tailWord_535329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535329).length < 2 ^ (prefixWord ++ tailWord_535329).sum := by decide
  have hdescent : baseEnd_535329 < baseStart_535329 := by decide
  rcases family_descends (prefixWord ++ tailWord_535329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535359 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 8]
def baseStart_535359 : Nat := 118140960795 + 535359 * 2 ^ 59
def prefixEnd_535359 : Nat := 4983230072969 + 3 ^ 40 * 535359 * 2
def baseEnd_535359 : Nat := 61088108824550253144541

theorem tailTrace_535359 : CollatzResearch.WordTrace tailWord_535359 prefixEnd_535359 61088108824550253144541 := by
  unfold tailWord_535359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19526146867493249883033131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13017431244995499922022087 19526146867493249883033131)
  ·
    refine ⟨29289220301239874824549697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19526146867493249883033131 29289220301239874824549697)
    ·
      refine ⟨21966915225929906118412273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29289220301239874824549697 21966915225929906118412273)
      ·
        refine ⟨16475186419447429588809205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21966915225929906118412273 16475186419447429588809205)
        ·
          refine ⟨1544548726823196523950863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16475186419447429588809205 1544548726823196523950863)
          ·
            refine ⟨2316823090234794785926295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544548726823196523950863 2316823090234794785926295)
            ·
              refine ⟨3475234635352192178889443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316823090234794785926295 3475234635352192178889443)
              ·
                refine ⟨5212851953028288268334165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475234635352192178889443 5212851953028288268334165)
                ·
                  refine ⟨61088108824550253144541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5212851953028288268334165 61088108824550253144541)
                  ·
                    rfl

theorem cell22_535359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_535359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535359 prefixEnd_535359 := by exact prefixLift 535359
  have htrace : WordTrace (prefixWord ++ tailWord_535359) baseStart_535359 baseEnd_535359 := by
    simpa [prefixWord, tailWord_535359, baseEnd_535359] using wordTrace_append hprefix tailTrace_535359
  have hstable : (prefixWord ++ tailWord_535359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535359).length < 2 ^ (prefixWord ++ tailWord_535359).sum := by decide
  have hdescent : baseEnd_535359 < baseStart_535359 := by decide
  rcases family_descends (prefixWord ++ tailWord_535359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535376 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_535376 : Nat := 118140960795 + 535376 * 2 ^ 59
def prefixEnd_535376 : Nat := 4983230072969 + 3 ^ 40 * 535376 * 2
def baseEnd_535376 : Nat := 61090048640356127252857

theorem tailTrace_535376 : CollatzResearch.WordTrace tailWord_535376 prefixEnd_535376 61090048640356127252857 := by
  unfold tailWord_535376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9763383454215830893200991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13017844605621107857601321 9763383454215830893200991)
  ·
    refine ⟨14645075181323746339801487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9763383454215830893200991 14645075181323746339801487)
    ·
      refine ⟨21967612771985619509702231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14645075181323746339801487 21967612771985619509702231)
      ·
        refine ⟨32951419157978429264553347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21967612771985619509702231 32951419157978429264553347)
        ·
          refine ⟨49427128736967643896830021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32951419157978429264553347 49427128736967643896830021)
          ·
            refine ⟨9267586638181433230655629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49427128736967643896830021 9267586638181433230655629)
            ·
              refine ⟨3475344989318037461495861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9267586638181433230655629 3475344989318037461495861)
              ·
                refine ⟨325813592748566012015237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3475344989318037461495861 325813592748566012015237)
                ·
                  refine ⟨61090048640356127252857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325813592748566012015237 61090048640356127252857)
                  ·
                    rfl

theorem cell22_535376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_535376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535376 prefixEnd_535376 := by exact prefixLift 535376
  have htrace : WordTrace (prefixWord ++ tailWord_535376) baseStart_535376 baseEnd_535376 := by
    simpa [prefixWord, tailWord_535376, baseEnd_535376] using wordTrace_append hprefix tailTrace_535376
  have hstable : (prefixWord ++ tailWord_535376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535376).length < 2 ^ (prefixWord ++ tailWord_535376).sum := by decide
  have hdescent : baseEnd_535376 < baseStart_535376 := by decide
  rcases family_descends (prefixWord ++ tailWord_535376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535391 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 4, 3]
def baseStart_535391 : Nat := 118140960795 + 535391 * 2 ^ 59
def prefixEnd_535391 : Nat := 4983230072969 + 3 ^ 40 * 535391 * 2
def baseEnd_535391 : Nat := 183275280727613342633525

theorem tailTrace_535391 : CollatzResearch.WordTrace tailWord_535391 prefixEnd_535391 183275280727613342633525 := by
  unfold tailWord_535391
  simp only [CollatzResearch.WordTrace]
  refine ⟨19527314003377319348198027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018209335584879565465351 19527314003377319348198027)
  ·
    refine ⟨29290971005065979022297041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19527314003377319348198027 29290971005065979022297041)
    ·
      refine ⟨21968228253799484266722781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29290971005065979022297041 21968228253799484266722781)
      ·
        refine ⟨8238085595174806600021043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21968228253799484266722781 8238085595174806600021043)
        ·
          refine ⟨12357128392762209900031565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238085595174806600021043 12357128392762209900031565)
          ·
            refine ⟨4633923147285828712511837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12357128392762209900031565 4633923147285828712511837)
            ·
              refine ⟨1737721180232185767191939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4633923147285828712511837 1737721180232185767191939)
              ·
                refine ⟨2606581770348278650787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737721180232185767191939 2606581770348278650787909)
                ·
                  refine ⟨488734081940302247022733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2606581770348278650787909 488734081940302247022733)
                  ·
                    refine ⟨183275280727613342633525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488734081940302247022733 183275280727613342633525)
                    ·
                      rfl

theorem cell22_535391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_535391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535391 prefixEnd_535391 := by exact prefixLift 535391
  have htrace : WordTrace (prefixWord ++ tailWord_535391) baseStart_535391 baseEnd_535391 := by
    simpa [prefixWord, tailWord_535391, baseEnd_535391] using wordTrace_append hprefix tailTrace_535391
  have hstable : (prefixWord ++ tailWord_535391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535391).length < 2 ^ (prefixWord ++ tailWord_535391).sum := by decide
  have hdescent : baseEnd_535391 < baseStart_535391 := by decide
  rcases family_descends (prefixWord ++ tailWord_535391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535404 : List Nat := [2, 2, 1, 1, 4, 1, 2, 9]
def baseStart_535404 : Nat := 118140960795 + 535404 * 2 ^ 59
def prefixEnd_535404 : Nat := 4983230072969 + 3 ^ 40 * 535404 * 2
def baseEnd_535404 : Nat := 20364414543698404673165

theorem tailTrace_535404 : CollatzResearch.WordTrace tailWord_535404 prefixEnd_535404 20364414543698404673165 := by
  unfold tailWord_535404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9763894076165111284210633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13018525434886815045614177 9763894076165111284210633)
  ·
    refine ⟨7322920557123833463157975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9763894076165111284210633 7322920557123833463157975)
    ·
      refine ⟨10984380835685750194736963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7322920557123833463157975 10984380835685750194736963)
      ·
        refine ⟨16476571253528625292105445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10984380835685750194736963 16476571253528625292105445)
        ·
          refine ⟨3089357110036617242269771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16476571253528625292105445 3089357110036617242269771)
          ·
            refine ⟨4634035665054925863404657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089357110036617242269771 4634035665054925863404657)
            ·
              refine ⟨3475526748791194397553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634035665054925863404657 3475526748791194397553493)
              ·
                refine ⟨20364414543698404673165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3475526748791194397553493 20364414543698404673165)
                ·
                  rfl

theorem cell22_535404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 9].length) (baseStart_535404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535404 prefixEnd_535404 := by exact prefixLift 535404
  have htrace : WordTrace (prefixWord ++ tailWord_535404) baseStart_535404 baseEnd_535404 := by
    simpa [prefixWord, tailWord_535404, baseEnd_535404] using wordTrace_append hprefix tailTrace_535404
  have hstable : (prefixWord ++ tailWord_535404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535404).length < 2 ^ (prefixWord ++ tailWord_535404).sum := by decide
  have hdescent : baseEnd_535404 < baseStart_535404 := by decide
  rcases family_descends (prefixWord ++ tailWord_535404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535421 : List Nat := [1, 4, 1, 1, 2, 1, 6, 6]
def baseStart_535421 : Nat := 118140960795 + 535421 * 2 ^ 59
def prefixEnd_535421 : Nat := 4983230072969 + 3 ^ 40 * 535421 * 2
def baseEnd_535421 : Nat := 20365061148967029375937

theorem tailTrace_535421 : CollatzResearch.WordTrace tailWord_535421 prefixEnd_535421 20365061148967029375937 := by
  unfold tailWord_535421
  simp only [CollatzResearch.WordTrace]
  refine ⟨19528408193268634471790117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13018938795512422981193411 19528408193268634471790117)
  ·
    refine ⟨3661576536237868963460647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19528408193268634471790117 3661576536237868963460647)
    ·
      refine ⟨5492364804356803445190971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661576536237868963460647 5492364804356803445190971)
      ·
        refine ⟨8238547206535205167786457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5492364804356803445190971 8238547206535205167786457)
        ·
          refine ⟨6178910404901403875839843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8238547206535205167786457 6178910404901403875839843)
          ·
            refine ⟨9268365607352105813759765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178910404901403875839843 9268365607352105813759765)
            ·
              refine ⟨434454637844629960019989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9268365607352105813759765 434454637844629960019989)
              ·
                refine ⟨20365061148967029375937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 434454637844629960019989 20365061148967029375937)
                ·
                  rfl

theorem cell22_535421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 6].length) (baseStart_535421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535421 prefixEnd_535421 := by exact prefixLift 535421
  have htrace : WordTrace (prefixWord ++ tailWord_535421) baseStart_535421 baseEnd_535421 := by
    simpa [prefixWord, tailWord_535421, baseEnd_535421] using wordTrace_append hprefix tailTrace_535421
  have hstable : (prefixWord ++ tailWord_535421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535421).length < 2 ^ (prefixWord ++ tailWord_535421).sum := by decide
  have hdescent : baseEnd_535421 < baseStart_535421 := by decide
  rcases family_descends (prefixWord ++ tailWord_535421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535436 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_535436 : Nat := 118140960795 + 535436 * 2 ^ 59
def prefixEnd_535436 : Nat := 4983230072969 + 3 ^ 40 * 535436 * 2
def baseEnd_535436 : Nat := 183290685147248225258387

theorem tailTrace_535436 : CollatzResearch.WordTrace tailWord_535436 prefixEnd_535436 183290685147248225258387 := by
  unfold tailWord_535436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764477644107146016793081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13019303525476194689057441 9764477644107146016793081)
  ·
    refine ⟨7323358233080359512594811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9764477644107146016793081 7323358233080359512594811)
    ·
      refine ⟨10985037349620539268892217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7323358233080359512594811 10985037349620539268892217)
      ·
        refine ⟨8238778012215404451669163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10985037349620539268892217 8238778012215404451669163)
        ·
          refine ⟨12358167018323106677503745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238778012215404451669163 12358167018323106677503745)
          ·
            refine ⟨9268625263742330008127809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12358167018323106677503745 9268625263742330008127809)
            ·
              refine ⟨6951468947806747506095857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9268625263742330008127809 6951468947806747506095857)
              ·
                refine ⟨5213601710855060629571893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6951468947806747506095857 5213601710855060629571893)
                ·
                  refine ⟨488775160392661934022365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5213601710855060629571893 488775160392661934022365)
                  ·
                    refine ⟨183290685147248225258387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488775160392661934022365 183290685147248225258387)
                    ·
                      rfl

theorem cell22_535436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_535436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535436 prefixEnd_535436 := by exact prefixLift 535436
  have htrace : WordTrace (prefixWord ++ tailWord_535436) baseStart_535436 baseEnd_535436 := by
    simpa [prefixWord, tailWord_535436, baseEnd_535436] using wordTrace_append hprefix tailTrace_535436
  have hstable : (prefixWord ++ tailWord_535436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535436).length < 2 ^ (prefixWord ++ tailWord_535436).sum := by decide
  have hdescent : baseEnd_535436 < baseStart_535436 := by decide
  rcases family_descends (prefixWord ++ tailWord_535436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535560 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_535560 : Nat := 118140960795 + 535560 * 2 ^ 59
def prefixEnd_535560 : Nat := 4983230072969 + 3 ^ 40 * 535560 * 2
def baseEnd_535560 : Nat := 183333132881353235158007

theorem tailTrace_535560 : CollatzResearch.WordTrace tailWord_535560 prefixEnd_535560 183333132881353235158007 := by
  unfold tailWord_535560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9766738969882530605550067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13022318626510040807400089 9766738969882530605550067)
  ·
    refine ⟨14650108454823795908325101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9766738969882530605550067 14650108454823795908325101)
    ·
      refine ⟨5493790670558923465621913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14650108454823795908325101 5493790670558923465621913)
      ·
        refine ⟨4120343002919192599216435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493790670558923465621913 4120343002919192599216435)
        ·
          refine ⟨6180514504378788898824653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120343002919192599216435 6180514504378788898824653)
          ·
            refine ⟨2317692939142045837059245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6180514504378788898824653 2317692939142045837059245)
            ·
              refine ⟨869134852178267188897217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2317692939142045837059245 869134852178267188897217)
              ·
                refine ⟨651851139133700391672913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869134852178267188897217 651851139133700391672913)
                ·
                  refine ⟨488888354350275293754685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651851139133700391672913 488888354350275293754685)
                  ·
                    refine ⟨183333132881353235158007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488888354350275293754685 183333132881353235158007)
                    ·
                      rfl

theorem cell22_535560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_535560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535560 prefixEnd_535560 := by exact prefixLift 535560
  have htrace : WordTrace (prefixWord ++ tailWord_535560) baseStart_535560 baseEnd_535560 := by
    simpa [prefixWord, tailWord_535560, baseEnd_535560] using wordTrace_append hprefix tailTrace_535560
  have hstable : (prefixWord ++ tailWord_535560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535560).length < 2 ^ (prefixWord ++ tailWord_535560).sum := by decide
  have hdescent : baseEnd_535560 < baseStart_535560 := by decide
  rcases family_descends (prefixWord ++ tailWord_535560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535601 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 9]
def baseStart_535601 : Nat := 118140960795 + 535601 * 2 ^ 59
def prefixEnd_535601 : Nat := 4983230072969 + 3 ^ 40 * 535601 * 2
def baseEnd_535601 : Nat := 61115722673080931627627

theorem tailTrace_535601 : CollatzResearch.WordTrace tailWord_535601 prefixEnd_535601 61115722673080931627627 := by
  unfold tailWord_535601
  simp only [CollatzResearch.WordTrace]
  refine ⟨19534973332616525213342657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13023315555077683475561771 19534973332616525213342657)
  ·
    refine ⟨14651229999462393910006993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19534973332616525213342657 14651229999462393910006993)
    ·
      refine ⟨10988422499596795432505245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14651229999462393910006993 10988422499596795432505245)
      ·
        refine ⟨4120658437348798287189467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10988422499596795432505245 4120658437348798287189467)
        ·
          refine ⟨6180987656023197430784201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120658437348798287189467 6180987656023197430784201)
          ·
            refine ⟨4635740742017398073088151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6180987656023197430784201 4635740742017398073088151)
            ·
              refine ⟨6953611113026097109632227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635740742017398073088151 6953611113026097109632227)
              ·
                refine ⟨10430416669539145664448341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953611113026097109632227 10430416669539145664448341)
                ·
                  refine ⟨61115722673080931627627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10430416669539145664448341 61115722673080931627627)
                  ·
                    rfl

theorem cell22_535601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_535601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535601 prefixEnd_535601 := by exact prefixLift 535601
  have htrace : WordTrace (prefixWord ++ tailWord_535601) baseStart_535601 baseEnd_535601 := by
    simpa [prefixWord, tailWord_535601, baseEnd_535601] using wordTrace_append hprefix tailTrace_535601
  have hstable : (prefixWord ++ tailWord_535601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535601).length < 2 ^ (prefixWord ++ tailWord_535601).sum := by decide
  have hdescent : baseEnd_535601 < baseStart_535601 := by decide
  rcases family_descends (prefixWord ++ tailWord_535601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535648 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_535648 : Nat := 118140960795 + 535648 * 2 ^ 59
def prefixEnd_535648 : Nat := 4983230072969 + 3 ^ 40 * 535648 * 2
def baseEnd_535648 : Nat := 183363257079750338957737

theorem tailTrace_535648 : CollatzResearch.WordTrace tailWord_535648 prefixEnd_535648 183363257079750338957737 := by
  unfold tailWord_535648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9768343781723126120151799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13024458375630834826869065 9768343781723126120151799)
  ·
    refine ⟨14652515672584689180227699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9768343781723126120151799 14652515672584689180227699)
    ·
      refine ⟨21978773508877033770341549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14652515672584689180227699 21978773508877033770341549)
      ·
        refine ⟨8242040065828887663878081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21978773508877033770341549 8242040065828887663878081)
        ·
          refine ⟨6181530049371665747908561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8242040065828887663878081 6181530049371665747908561)
          ·
            refine ⟨4636147537028749310931421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181530049371665747908561 4636147537028749310931421)
            ·
              refine ⟨1738555326385780991599283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4636147537028749310931421 1738555326385780991599283)
              ·
                refine ⟨2607832989578671487398925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738555326385780991599283 2607832989578671487398925)
                ·
                  refine ⟨977937371092001807774597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2607832989578671487398925 977937371092001807774597)
                  ·
                    refine ⟨183363257079750338957737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 977937371092001807774597 183363257079750338957737)
                    ·
                      rfl

theorem cell22_535648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_535648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535648 prefixEnd_535648 := by exact prefixLift 535648
  have htrace : WordTrace (prefixWord ++ tailWord_535648) baseStart_535648 baseEnd_535648 := by
    simpa [prefixWord, tailWord_535648, baseEnd_535648] using wordTrace_append hprefix tailTrace_535648
  have hstable : (prefixWord ++ tailWord_535648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535648).length < 2 ^ (prefixWord ++ tailWord_535648).sum := by decide
  have hdescent : baseEnd_535648 < baseStart_535648 := by decide
  rcases family_descends (prefixWord ++ tailWord_535648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535714 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_535714 : Nat := 118140960795 + 535714 * 2 ^ 59
def prefixEnd_535714 : Nat := 4983230072969 + 3 ^ 40 * 535714 * 2
def baseEnd_535714 : Nat := 61128616742849388935845

theorem tailTrace_535714 : CollatzResearch.WordTrace tailWord_535714 prefixEnd_535714 61128616742849388935845 := by
  unfold tailWord_535714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884773695301786378051549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13026063187471430341470797 4884773695301786378051549)
  ·
    refine ⟨1831790135738169891769331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4884773695301786378051549 1831790135738169891769331)
    ·
      refine ⟨2747685203607254837653997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831790135738169891769331 2747685203607254837653997)
      ·
        refine ⟨1030381951352720564120249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2747685203607254837653997 1030381951352720564120249)
        ·
          refine ⟨772786463514540423090187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030381951352720564120249 772786463514540423090187)
          ·
            refine ⟨1159179695271810634635281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772786463514540423090187 1159179695271810634635281)
            ·
              refine ⟨869384771453857975976461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1159179695271810634635281 869384771453857975976461)
              ·
                refine ⟨326019289295196740991173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869384771453857975976461 326019289295196740991173)
                ·
                  refine ⟨61128616742849388935845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326019289295196740991173 61128616742849388935845)
                  ·
                    rfl

theorem cell22_535714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_535714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535714 prefixEnd_535714 := by exact prefixLift 535714
  have htrace : WordTrace (prefixWord ++ tailWord_535714) baseStart_535714 baseEnd_535714 := by
    simpa [prefixWord, tailWord_535714, baseEnd_535714] using wordTrace_append hprefix tailTrace_535714
  have hstable : (prefixWord ++ tailWord_535714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535714).length < 2 ^ (prefixWord ++ tailWord_535714).sum := by decide
  have hdescent : baseEnd_535714 < baseStart_535714 := by decide
  rcases family_descends (prefixWord ++ tailWord_535714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535725 : List Nat := [1, 5, 2, 1, 3, 1, 9]
def baseStart_535725 : Nat := 118140960795 + 535725 * 2 ^ 59
def prefixEnd_535725 : Nat := 4983230072969 + 3 ^ 40 * 535725 * 2
def baseEnd_535725 : Nat := 6792207990864733510463

theorem tailTrace_535725 : CollatzResearch.WordTrace tailWord_535725 prefixEnd_535725 6792207990864733510463 := by
  unfold tailWord_535725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539495984167294390856629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13026330656111529593904419 19539495984167294390856629)
  ·
    refine ⟨1831827748515683849142809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19539495984167294390856629 1831827748515683849142809)
    ·
      refine ⟨1373870811386762886857107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831827748515683849142809 1373870811386762886857107)
      ·
        refine ⟨2060806217080144330285661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1373870811386762886857107 2060806217080144330285661)
        ·
          refine ⟨772802331405054123857123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2060806217080144330285661 772802331405054123857123)
          ·
            refine ⟨1159203497107581185785685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772802331405054123857123 1159203497107581185785685)
            ·
              refine ⟨6792207990864733510463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1159203497107581185785685 6792207990864733510463)
              ·
                rfl

theorem cell22_535725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 9].length) (baseStart_535725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535725 prefixEnd_535725 := by exact prefixLift 535725
  have htrace : WordTrace (prefixWord ++ tailWord_535725) baseStart_535725 baseEnd_535725 := by
    simpa [prefixWord, tailWord_535725, baseEnd_535725] using wordTrace_append hprefix tailTrace_535725
  have hstable : (prefixWord ++ tailWord_535725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535725).length < 2 ^ (prefixWord ++ tailWord_535725).sum := by decide
  have hdescent : baseEnd_535725 < baseStart_535725 := by decide
  rcases family_descends (prefixWord ++ tailWord_535725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535729 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_535729 : Nat := 118140960795 + 535729 * 2 ^ 59
def prefixEnd_535729 : Nat := 4983230072969 + 3 ^ 40 * 535729 * 2
def baseEnd_535729 : Nat := 183390985035093127682489

theorem tailTrace_535729 : CollatzResearch.WordTrace tailWord_535729 prefixEnd_535729 183390985035093127682489 := by
  unfold tailWord_535729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539641876152803074002241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13026427917435202049334827 19539641876152803074002241)
  ·
    refine ⟨14654731407114602305501681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19539641876152803074002241 14654731407114602305501681)
    ·
      refine ⟨10991048555335951729126261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14654731407114602305501681 10991048555335951729126261)
      ·
        refine ⟨1030410802062745474605587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10991048555335951729126261 1030410802062745474605587)
        ·
          refine ⟨1545616203094118211908381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030410802062745474605587 1545616203094118211908381)
          ·
            refine ⟨579606076160294329465643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545616203094118211908381 579606076160294329465643)
            ·
              refine ⟨869409114240441494198465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579606076160294329465643 869409114240441494198465)
              ·
                refine ⟨652056835680331120648849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869409114240441494198465 652056835680331120648849)
                ·
                  refine ⟨489042626760248340486637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652056835680331120648849 489042626760248340486637)
                  ·
                    refine ⟨183390985035093127682489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489042626760248340486637 183390985035093127682489)
                    ·
                      rfl

theorem cell22_535729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_535729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535729 prefixEnd_535729 := by exact prefixLift 535729
  have htrace : WordTrace (prefixWord ++ tailWord_535729) baseStart_535729 baseEnd_535729 := by
    simpa [prefixWord, tailWord_535729, baseEnd_535729] using wordTrace_append hprefix tailTrace_535729
  have hstable : (prefixWord ++ tailWord_535729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535729).length < 2 ^ (prefixWord ++ tailWord_535729).sum := by decide
  have hdescent : baseEnd_535729 < baseStart_535729 := by decide
  rcases family_descends (prefixWord ++ tailWord_535729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535746 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_535746 : Nat := 118140960795 + 535746 * 2 ^ 59
def prefixEnd_535746 : Nat := 4983230072969 + 3 ^ 40 * 535746 * 2
def baseEnd_535746 : Nat := 183396804482510750007437

theorem tailTrace_535746 : CollatzResearch.WordTrace tailWord_535746 prefixEnd_535746 183396804482510750007437 := by
  unfold tailWord_535746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885065479272803744342773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13026841278060809984914061 4885065479272803744342773)
  ·
    refine ⟨457974888681825351032135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4885065479272803744342773 457974888681825351032135)
    ·
      refine ⟨686962333022738026548203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457974888681825351032135 686962333022738026548203)
      ·
        refine ⟨1030443499534107039822305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686962333022738026548203 1030443499534107039822305)
        ·
          refine ⟨772832624650580279866729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030443499534107039822305 772832624650580279866729)
          ·
            refine ⟨579624468487935209900047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772832624650580279866729 579624468487935209900047)
            ·
              refine ⟨869436702731902814850071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579624468487935209900047 869436702731902814850071)
              ·
                refine ⟨1304155054097854222275107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869436702731902814850071 1304155054097854222275107)
                ·
                  refine ⟨1956232581146781333412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304155054097854222275107 1956232581146781333412661)
                  ·
                    refine ⟨183396804482510750007437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1956232581146781333412661 183396804482510750007437)
                    ·
                      rfl

theorem cell22_535746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_535746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535746 prefixEnd_535746 := by exact prefixLift 535746
  have htrace : WordTrace (prefixWord ++ tailWord_535746) baseStart_535746 baseEnd_535746 := by
    simpa [prefixWord, tailWord_535746, baseEnd_535746] using wordTrace_append hprefix tailTrace_535746
  have hstable : (prefixWord ++ tailWord_535746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535746).length < 2 ^ (prefixWord ++ tailWord_535746).sum := by decide
  have hdescent : baseEnd_535746 < baseStart_535746 := by decide
  rcases family_descends (prefixWord ++ tailWord_535746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535791 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 1, 3]
def baseStart_535791 : Nat := 118140960795 + 535791 * 2 ^ 59
def prefixEnd_535791 : Nat := 4983230072969 + 3 ^ 40 * 535791 * 2
def baseEnd_535791 : Nat := 183412208902145632632299

theorem tailTrace_535791 : CollatzResearch.WordTrace tailWord_535791 prefixEnd_535791 183412208902145632632299 := by
  unfold tailWord_535791
  simp only [CollatzResearch.WordTrace]
  refine ⟨19541903201928187662759227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13027935467952125108506151 19541903201928187662759227)
  ·
    refine ⟨29312854802892281494138841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19541903201928187662759227 29312854802892281494138841)
    ·
      refine ⟨21984641102169211120604131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29312854802892281494138841 21984641102169211120604131)
      ·
        refine ⟨32976961653253816680906197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21984641102169211120604131 32976961653253816680906197)
        ·
          refine ⟨772897538748136328458739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32976961653253816680906197 772897538748136328458739)
          ·
            refine ⟨1159346308122204492688109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772897538748136328458739 1159346308122204492688109)
            ·
              refine ⟨434754865545826684758041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1159346308122204492688109 434754865545826684758041)
              ·
                refine ⟨326066149159370013568531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434754865545826684758041 326066149159370013568531)
                ·
                  refine ⟨489099223739055020352797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326066149159370013568531 489099223739055020352797)
                  ·
                    refine ⟨183412208902145632632299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489099223739055020352797 183412208902145632632299)
                    ·
                      rfl

theorem cell22_535791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 3].length) (baseStart_535791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535791 prefixEnd_535791 := by exact prefixLift 535791
  have htrace : WordTrace (prefixWord ++ tailWord_535791) baseStart_535791 baseEnd_535791 := by
    simpa [prefixWord, tailWord_535791, baseEnd_535791] using wordTrace_append hprefix tailTrace_535791
  have hstable : (prefixWord ++ tailWord_535791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535791).length < 2 ^ (prefixWord ++ tailWord_535791).sum := by decide
  have hdescent : baseEnd_535791 < baseStart_535791 := by decide
  rcases family_descends (prefixWord ++ tailWord_535791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535804 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_535804 : Nat := 118140960795 + 535804 * 2 ^ 59
def prefixEnd_535804 : Nat := 4983230072969 + 3 ^ 40 * 535804 * 2
def baseEnd_535804 : Nat := 61138886355939310685753

theorem tailTrace_535804 : CollatzResearch.WordTrace tailWord_535804 prefixEnd_535804 61138886355939310685753 := by
  unfold tailWord_535804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771188675440545441491233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13028251567254060588654977 9771188675440545441491233)
  ·
    refine ⟨7328391506580409081118425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9771188675440545441491233 7328391506580409081118425)
    ·
      refine ⟨5496293629935306810838819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7328391506580409081118425 5496293629935306810838819)
      ·
        refine ⟨8244440444902960216258229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5496293629935306810838819 8244440444902960216258229)
        ·
          refine ⟨772916291709652520274209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8244440444902960216258229 772916291709652520274209)
          ·
            refine ⟨579687218782239390205657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772916291709652520274209 579687218782239390205657)
            ·
              refine ⟨434765414086679542654243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579687218782239390205657 434765414086679542654243)
              ·
                refine ⟨652148121130019313981365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434765414086679542654243 652148121130019313981365)
                ·
                  refine ⟨61138886355939310685753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652148121130019313981365 61138886355939310685753)
                  ·
                    rfl

theorem cell22_535804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_535804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535804 prefixEnd_535804 := by exact prefixLift 535804
  have htrace : WordTrace (prefixWord ++ tailWord_535804) baseStart_535804 baseEnd_535804 := by
    simpa [prefixWord, tailWord_535804, baseEnd_535804] using wordTrace_append hprefix tailTrace_535804
  have hstable : (prefixWord ++ tailWord_535804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535804).length < 2 ^ (prefixWord ++ tailWord_535804).sum := by decide
  have hdescent : baseEnd_535804 < baseStart_535804 := by decide
  rcases family_descends (prefixWord ++ tailWord_535804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535834 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_535834 : Nat := 118140960795 + 535834 * 2 ^ 59
def prefixEnd_535834 : Nat := 4983230072969 + 3 ^ 40 * 535834 * 2
def baseEnd_535834 : Nat := 183426928680907853807167

theorem tailTrace_535834 : CollatzResearch.WordTrace tailWord_535834 prefixEnd_535834 183426928680907853807167 := by
  unfold tailWord_535834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885867885193101501643639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13028981027181604004383037 4885867885193101501643639)
  ·
    refine ⟨7328801827789652252465459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4885867885193101501643639 7328801827789652252465459)
    ·
      refine ⟨10993202741684478378698189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7328801827789652252465459 10993202741684478378698189)
      ·
        refine ⟨4122451028131679392011821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10993202741684478378698189 4122451028131679392011821)
        ·
          refine ⟨1545919135549379772004433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4122451028131679392011821 1545919135549379772004433)
          ·
            refine ⟨1159439351662034829003325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1545919135549379772004433 1159439351662034829003325)
            ·
              refine ⟨434789756873263060876247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1159439351662034829003325 434789756873263060876247)
              ·
                refine ⟨652184635309894591314371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434789756873263060876247 652184635309894591314371)
                ·
                  refine ⟨978276952964841886971557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652184635309894591314371 978276952964841886971557)
                  ·
                    refine ⟨183426928680907853807167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978276952964841886971557 183426928680907853807167)
                    ·
                      rfl

theorem cell22_535834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_535834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535834 prefixEnd_535834 := by exact prefixLift 535834
  have htrace : WordTrace (prefixWord ++ tailWord_535834) baseStart_535834 baseEnd_535834 := by
    simpa [prefixWord, tailWord_535834, baseEnd_535834] using wordTrace_append hprefix tailTrace_535834
  have hstable : (prefixWord ++ tailWord_535834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535834).length < 2 ^ (prefixWord ++ tailWord_535834).sum := by decide
  have hdescent : baseEnd_535834 < baseStart_535834 := by decide
  rcases family_descends (prefixWord ++ tailWord_535834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535843 : List Nat := [1, 1, 1, 4, 2, 13]
def baseStart_535843 : Nat := 118140960795 + 535843 * 2 ^ 59
def prefixEnd_535843 : Nat := 4983230072969 + 3 ^ 40 * 535843 * 2
def baseEnd_535843 : Nat := 2264568019318948522619

theorem tailTrace_535843 : CollatzResearch.WordTrace tailWord_535843 prefixEnd_535843 2264568019318948522619 := by
  unfold tailWord_535843
  simp only [CollatzResearch.WordTrace]
  refine ⟨19543799797739800543652183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13029199865159867029101455 19543799797739800543652183)
  ·
    refine ⟨29315699696609700815478275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19543799797739800543652183 29315699696609700815478275)
    ·
      refine ⟨43973549544914551223217413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29315699696609700815478275 43973549544914551223217413)
      ·
        refine ⟨8245040539671478354353265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43973549544914551223217413 8245040539671478354353265)
        ·
          refine ⟨6183780404753608765764949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8245040539671478354353265 6183780404753608765764949)
          ·
            refine ⟨2264568019318948522619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6183780404753608765764949 2264568019318948522619)
            ·
              rfl

theorem cell22_535843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 13].length) (baseStart_535843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535843 prefixEnd_535843 := by exact prefixLift 535843
  have htrace : WordTrace (prefixWord ++ tailWord_535843) baseStart_535843 baseEnd_535843 := by
    simpa [prefixWord, tailWord_535843, baseEnd_535843] using wordTrace_append hprefix tailTrace_535843
  have hstable : (prefixWord ++ tailWord_535843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535843).length < 2 ^ (prefixWord ++ tailWord_535843).sum := by decide
  have hdescent : baseEnd_535843 < baseStart_535843 := by decide
  rcases family_descends (prefixWord ++ tailWord_535843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535885 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_535885 : Nat := 118140960795 + 535885 * 2 ^ 59
def prefixEnd_535885 : Nat := 4983230072969 + 3 ^ 40 * 535885 * 2
def baseEnd_535885 : Nat := 183444387023160720782011

theorem tailTrace_535885 : CollatzResearch.WordTrace tailWord_535885 prefixEnd_535885 183444387023160720782011 := by
  unfold tailWord_535885
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545331663587641716681109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13030221109058427811120739 19545331663587641716681109)
  ·
    refine ⟨916187421730670705469427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19545331663587641716681109 916187421730670705469427)
    ·
      refine ⟨1374281132596006058204141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916187421730670705469427 1374281132596006058204141)
      ·
        refine ⟨515355424723502271826553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1374281132596006058204141 515355424723502271826553)
        ·
          refine ⟨386516568542626703869915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515355424723502271826553 386516568542626703869915)
          ·
            refine ⟨579774852813940055804873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386516568542626703869915 579774852813940055804873)
            ·
              refine ⟨434831139610455041853655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579774852813940055804873 434831139610455041853655)
              ·
                refine ⟨652246709415682562780483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434831139610455041853655 652246709415682562780483)
                ·
                  refine ⟨978370064123523844170725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652246709415682562780483 978370064123523844170725)
                  ·
                    refine ⟨183444387023160720782011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978370064123523844170725 183444387023160720782011)
                    ·
                      rfl

theorem cell22_535885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_535885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535885 prefixEnd_535885 := by exact prefixLift 535885
  have htrace : WordTrace (prefixWord ++ tailWord_535885) baseStart_535885 baseEnd_535885 := by
    simpa [prefixWord, tailWord_535885, baseEnd_535885] using wordTrace_append hprefix tailTrace_535885
  have hstable : (prefixWord ++ tailWord_535885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535885).length < 2 ^ (prefixWord ++ tailWord_535885).sum := by decide
  have hdescent : baseEnd_535885 < baseStart_535885 := by decide
  rcases family_descends (prefixWord ++ tailWord_535885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535892 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_535892 : Nat := 118140960795 + 535892 * 2 ^ 59
def prefixEnd_535892 : Nat := 4983230072969 + 3 ^ 40 * 535892 * 2
def baseEnd_535892 : Nat := 183446783266215035856989

theorem tailTrace_535892 : CollatzResearch.WordTrace tailWord_535892 prefixEnd_535892 183446783266215035856989 := by
  unfold tailWord_535892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9772793487281140956092965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13030391316374854608123953 9772793487281140956092965)
  ·
    refine ⟨1832398778865213929267431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9772793487281140956092965 1832398778865213929267431)
    ·
      refine ⟨2748598168297820893901147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832398778865213929267431 2748598168297820893901147)
      ·
        refine ⟨4122897252446731340851721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748598168297820893901147 4122897252446731340851721)
        ·
          refine ⟨3092172939335048505638791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4122897252446731340851721 3092172939335048505638791)
          ·
            refine ⟨4638259409002572758458187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092172939335048505638791 4638259409002572758458187)
            ·
              refine ⟨6957389113503859137687281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638259409002572758458187 6957389113503859137687281)
              ·
                refine ⟨5218041835127894353265461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6957389113503859137687281 5218041835127894353265461)
                ·
                  refine ⟨489191422043240095618637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5218041835127894353265461 489191422043240095618637)
                  ·
                    refine ⟨183446783266215035856989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489191422043240095618637 183446783266215035856989)
                    ·
                      rfl

theorem cell22_535892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_535892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535892 prefixEnd_535892 := by exact prefixLift 535892
  have htrace : WordTrace (prefixWord ++ tailWord_535892) baseStart_535892 baseEnd_535892 := by
    simpa [prefixWord, tailWord_535892, baseEnd_535892] using wordTrace_append hprefix tailTrace_535892
  have hstable : (prefixWord ++ tailWord_535892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535892).length < 2 ^ (prefixWord ++ tailWord_535892).sum := by decide
  have hdescent : baseEnd_535892 < baseStart_535892 := by decide
  rcases family_descends (prefixWord ++ tailWord_535892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535909 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_535909 : Nat := 118140960795 + 535909 * 2 ^ 59
def prefixEnd_535909 : Nat := 4983230072969 + 3 ^ 40 * 535909 * 2
def baseEnd_535909 : Nat := 183452602713632658181937

theorem tailTrace_535909 : CollatzResearch.WordTrace tailWord_535909 prefixEnd_535909 183452602713632658181937 := by
  unfold tailWord_535909
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546207015500693815554781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13030804677000462543703187 19546207015500693815554781)
  ·
    refine ⟨7329827630812760180833043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19546207015500693815554781 7329827630812760180833043)
    ·
      refine ⟨10994741446219140271249565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329827630812760180833043 10994741446219140271249565)
      ·
        refine ⟨4123028042332177601718587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10994741446219140271249565 4123028042332177601718587)
        ·
          refine ⟨6184542063498266402577881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4123028042332177601718587 6184542063498266402577881)
          ·
            refine ⟨4638406547623699801933411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184542063498266402577881 4638406547623699801933411)
            ·
              refine ⟨6957609821435549702900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638406547623699801933411 6957609821435549702900117)
              ·
                refine ⟨326137960379791392323443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6957609821435549702900117 326137960379791392323443)
                ·
                  refine ⟨489206940569687088485165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326137960379791392323443 489206940569687088485165)
                  ·
                    refine ⟨183452602713632658181937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489206940569687088485165 183452602713632658181937)
                    ·
                      rfl

theorem cell22_535909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_535909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535909 prefixEnd_535909 := by exact prefixLift 535909
  have htrace : WordTrace (prefixWord ++ tailWord_535909) baseStart_535909 baseEnd_535909 := by
    simpa [prefixWord, tailWord_535909, baseEnd_535909] using wordTrace_append hprefix tailTrace_535909
  have hstable : (prefixWord ++ tailWord_535909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535909).length < 2 ^ (prefixWord ++ tailWord_535909).sum := by decide
  have hdescent : baseEnd_535909 < baseStart_535909 := by decide
  rcases family_descends (prefixWord ++ tailWord_535909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535920 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_535920 : Nat := 118140960795 + 535920 * 2 ^ 59
def prefixEnd_535920 : Nat := 4983230072969 + 3 ^ 40 * 535920 * 2
def baseEnd_535920 : Nat := 183456368238432296156903

theorem tailTrace_535920 : CollatzResearch.WordTrace tailWord_535920 prefixEnd_535920 183456368238432296156903 := by
  unfold tailWord_535920
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773304109230421347102607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13031072145640561796136809 9773304109230421347102607)
  ·
    refine ⟨14659956163845632020653911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773304109230421347102607 14659956163845632020653911)
    ·
      refine ⟨21989934245768448030980867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14659956163845632020653911 21989934245768448030980867)
      ·
        refine ⟨32984901368652672046471301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21989934245768448030980867 32984901368652672046471301)
        ·
          refine ⟨6184669006622376008713369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32984901368652672046471301 6184669006622376008713369)
          ·
            refine ⟨4638501754966782006535027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6184669006622376008713369 4638501754966782006535027)
            ·
              refine ⟨6957752632450173009802541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638501754966782006535027 6957752632450173009802541)
              ·
                refine ⟨2609157237168814878675953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6957752632450173009802541 2609157237168814878675953)
                ·
                  refine ⟨1956867927876611159006965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609157237168814878675953 1956867927876611159006965)
                  ·
                    refine ⟨183456368238432296156903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1956867927876611159006965 183456368238432296156903)
                    ·
                      rfl

theorem cell22_535920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_535920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535920 prefixEnd_535920 := by exact prefixLift 535920
  have htrace : WordTrace (prefixWord ++ tailWord_535920) baseStart_535920 baseEnd_535920 := by
    simpa [prefixWord, tailWord_535920, baseEnd_535920] using wordTrace_append hprefix tailTrace_535920
  have hstable : (prefixWord ++ tailWord_535920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535920).length < 2 ^ (prefixWord ++ tailWord_535920).sum := by decide
  have hdescent : baseEnd_535920 < baseStart_535920 := by decide
  rcases family_descends (prefixWord ++ tailWord_535920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535967 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 6]
def baseStart_535967 : Nat := 118140960795 + 535967 * 2 ^ 59
def prefixEnd_535967 : Nat := 4983230072969 + 3 ^ 40 * 535967 * 2
def baseEnd_535967 : Nat := 61157485766313280077253

theorem tailTrace_535967 : CollatzResearch.WordTrace tailWord_535967 prefixEnd_535967 61157485766313280077253 := by
  unfold tailWord_535967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19548322449290569721166155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13032214966193713147444103 19548322449290569721166155)
  ·
    refine ⟨29322483673935854581749233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19548322449290569721166155 29322483673935854581749233)
    ·
      refine ⟨21991862755451890936311925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29322483673935854581749233 21991862755451890936311925)
      ·
        refine ⟨2061737133323614775279243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21991862755451890936311925 2061737133323614775279243)
        ·
          refine ⟨3092605699985422162918865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061737133323614775279243 3092605699985422162918865)
          ·
            refine ⟨2319454274989066622189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3092605699985422162918865 2319454274989066622189149)
            ·
              refine ⟨869795353120899983320931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319454274989066622189149 869795353120899983320931)
              ·
                refine ⟨1304693029681349974981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869795353120899983320931 1304693029681349974981397)
                ·
                  refine ⟨61157485766313280077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1304693029681349974981397 61157485766313280077253)
                  ·
                    rfl

theorem cell22_535967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_535967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535967 prefixEnd_535967 := by exact prefixLift 535967
  have htrace : WordTrace (prefixWord ++ tailWord_535967) baseStart_535967 baseEnd_535967 := by
    simpa [prefixWord, tailWord_535967, baseEnd_535967] using wordTrace_append hprefix tailTrace_535967
  have hstable : (prefixWord ++ tailWord_535967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535967).length < 2 ^ (prefixWord ++ tailWord_535967).sum := by decide
  have hdescent : baseEnd_535967 < baseStart_535967 := by decide
  rcases family_descends (prefixWord ++ tailWord_535967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535980 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_535980 : Nat := 118140960795 + 535980 * 2 ^ 59
def prefixEnd_535980 : Nat := 4983230072969 + 3 ^ 40 * 535980 * 2
def baseEnd_535980 : Nat := 183476907464612139656719

theorem tailTrace_535980 : CollatzResearch.WordTrace tailWord_535980 prefixEnd_535980 183476907464612139656719 := by
  unfold tailWord_535980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9774398299121736470694697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13032531065495648627592929 9774398299121736470694697)
  ·
    refine ⟨7330798724341302353021023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9774398299121736470694697 7330798724341302353021023)
    ·
      refine ⟨10996198086511953529531535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330798724341302353021023 10996198086511953529531535)
      ·
        refine ⟨16494297129767930294297303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10996198086511953529531535 16494297129767930294297303)
        ·
          refine ⟨24741445694651895441445955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16494297129767930294297303 24741445694651895441445955)
          ·
            refine ⟨37112168541977843162168933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24741445694651895441445955 37112168541977843162168933)
            ·
              refine ⟨6958531601620845592906675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37112168541977843162168933 6958531601620845592906675)
              ·
                refine ⟨10437797402431268389360013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6958531601620845592906675 10437797402431268389360013)
                ·
                  refine ⟨3914174025911725646010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10437797402431268389360013 3914174025911725646010005)
                  ·
                    refine ⟨183476907464612139656719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3914174025911725646010005 183476907464612139656719)
                    ·
                      rfl

theorem cell22_535980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_535980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_535980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_535980 prefixEnd_535980 := by exact prefixLift 535980
  have htrace : WordTrace (prefixWord ++ tailWord_535980) baseStart_535980 baseEnd_535980 := by
    simpa [prefixWord, tailWord_535980, baseEnd_535980] using wordTrace_append hprefix tailTrace_535980
  have hstable : (prefixWord ++ tailWord_535980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535980).length < 2 ^ (prefixWord ++ tailWord_535980).sum := by decide
  have hdescent : baseEnd_535980 < baseStart_535980 := by decide
  rcases family_descends (prefixWord ++ tailWord_535980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536029 : List Nat := [1, 4, 3, 1, 1, 4, 1, 7]
def baseStart_536029 : Nat := 118140960795 + 536029 * 2 ^ 59
def prefixEnd_536029 : Nat := 4983230072969 + 3 ^ 40 * 536029 * 2
def baseEnd_536029 : Nat := 20388186796221371686841

theorem tailTrace_536029 : CollatzResearch.WordTrace tailWord_536029 prefixEnd_536029 20388186796221371686841 := by
  unfold tailWord_536029
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550583775065954309923141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13033722516710636206615427 19550583775065954309923141)
  ·
    refine ⟨3665734457824866433110589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19550583775065954309923141 3665734457824866433110589)
    ·
      refine ⟨1374650421684324912416471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3665734457824866433110589 1374650421684324912416471)
      ·
        refine ⟨2061975632526487368624707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374650421684324912416471 2061975632526487368624707)
        ·
          refine ⟨3092963448789731052937061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061975632526487368624707 3092963448789731052937061)
          ·
            refine ⟨579930646648074572425699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3092963448789731052937061 579930646648074572425699)
            ·
              refine ⟨869895969972111858638549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579930646648074572425699 869895969972111858638549)
              ·
                refine ⟨20388186796221371686841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 869895969972111858638549 20388186796221371686841)
                ·
                  rfl

theorem cell22_536029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 7].length) (baseStart_536029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536029 prefixEnd_536029 := by exact prefixLift 536029
  have htrace : WordTrace (prefixWord ++ tailWord_536029) baseStart_536029 baseEnd_536029 := by
    simpa [prefixWord, tailWord_536029, baseEnd_536029] using wordTrace_append hprefix tailTrace_536029
  have hstable : (prefixWord ++ tailWord_536029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536029).length < 2 ^ (prefixWord ++ tailWord_536029).sum := by decide
  have hdescent : baseEnd_536029 < baseStart_536029 := by decide
  rcases family_descends (prefixWord ++ tailWord_536029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536061 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_536061 : Nat := 118140960795 + 536061 * 2 ^ 59
def prefixEnd_536061 : Nat := 4983230072969 + 3 ^ 40 * 536061 * 2
def baseEnd_536061 : Nat := 183504635419954928381471

theorem tailTrace_536061 : CollatzResearch.WordTrace tailWord_536061 prefixEnd_536061 183504635419954928381471 := by
  unfold tailWord_536061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19551750910950023775088037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13034500607300015850058691 19551750910950023775088037)
  ·
    refine ⟨3665953295803129457829007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19551750910950023775088037 3665953295803129457829007)
    ·
      refine ⟨5498929943704694186743511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665953295803129457829007 5498929943704694186743511)
      ·
        refine ⟨8248394915557041280115267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498929943704694186743511 8248394915557041280115267)
        ·
          refine ⟨12372592373335561920172901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248394915557041280115267 12372592373335561920172901)
          ·
            refine ⟨2319861070000417860032419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12372592373335561920172901 2319861070000417860032419)
            ·
              refine ⟨3479791605000626790048629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319861070000417860032419 3479791605000626790048629)
              ·
                refine ⟨326230462968808761567059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3479791605000626790048629 326230462968808761567059)
                ·
                  refine ⟨489345694453213142350589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326230462968808761567059 489345694453213142350589)
                  ·
                    refine ⟨183504635419954928381471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489345694453213142350589 183504635419954928381471)
                    ·
                      rfl

theorem cell22_536061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_536061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536061 prefixEnd_536061 := by exact prefixLift 536061
  have htrace : WordTrace (prefixWord ++ tailWord_536061) baseStart_536061 baseEnd_536061 := by
    simpa [prefixWord, tailWord_536061, baseEnd_536061] using wordTrace_append hprefix tailTrace_536061
  have hstable : (prefixWord ++ tailWord_536061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536061).length < 2 ^ (prefixWord ++ tailWord_536061).sum := by decide
  have hdescent : baseEnd_536061 < baseStart_536061 := by decide
  rcases family_descends (prefixWord ++ tailWord_536061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536072 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_536072 : Nat := 118140960795 + 536072 * 2 ^ 59
def prefixEnd_536072 : Nat := 4983230072969 + 3 ^ 40 * 536072 * 2
def baseEnd_536072 : Nat := 183508400944754566356437

theorem tailTrace_536072 : CollatzResearch.WordTrace tailWord_536072 prefixEnd_536072 183508400944754566356437 := by
  unfold tailWord_536072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776076056955086326869235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13034768075940115102492313 9776076056955086326869235)
  ·
    refine ⟨14664114085432629490303853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776076056955086326869235 14664114085432629490303853)
    ·
      refine ⟨5499042782037236058863945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14664114085432629490303853 5499042782037236058863945)
      ·
        refine ⟨4124282086527927044147959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5499042782037236058863945 4124282086527927044147959)
        ·
          refine ⟨6186423129791890566221939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124282086527927044147959 6186423129791890566221939)
          ·
            refine ⟨9279634694687835849332909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186423129791890566221939 9279634694687835849332909)
            ·
              refine ⟨3479863010507938443499841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9279634694687835849332909 3479863010507938443499841)
              ·
                refine ⟨2609897257880953832624881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3479863010507938443499841 2609897257880953832624881)
                ·
                  refine ⟨1957422943410715374468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609897257880953832624881 1957422943410715374468661)
                  ·
                    refine ⟨183508400944754566356437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1957422943410715374468661 183508400944754566356437)
                    ·
                      rfl

theorem cell22_536072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_536072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536072 prefixEnd_536072 := by exact prefixLift 536072
  have htrace : WordTrace (prefixWord ++ tailWord_536072) baseStart_536072 baseEnd_536072 := by
    simpa [prefixWord, tailWord_536072, baseEnd_536072] using wordTrace_append hprefix tailTrace_536072
  have hstable : (prefixWord ++ tailWord_536072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536072).length < 2 ^ (prefixWord ++ tailWord_536072).sum := by decide
  have hdescent : baseEnd_536072 < baseStart_536072 := by decide
  rcases family_descends (prefixWord ++ tailWord_536072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536074 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_536074 : Nat := 118140960795 + 536074 * 2 ^ 59
def prefixEnd_536074 : Nat := 4983230072969 + 3 ^ 40 * 536074 * 2
def baseEnd_536074 : Nat := 61169695195209075935477

theorem tailTrace_536074 : CollatzResearch.WordTrace tailWord_536074 prefixEnd_536074 61169695195209075935477 := by
  unfold tailWord_536074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888056264975731748827819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13034816706601951330207517 4888056264975731748827819)
  ·
    refine ⟨7332084397463597623241729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4888056264975731748827819 7332084397463597623241729)
    ·
      refine ⟨5499063298097698217431297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7332084397463597623241729 5499063298097698217431297)
      ·
        refine ⟨4124297473573273663073473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5499063298097698217431297 4124297473573273663073473)
        ·
          refine ⟨3093223105179955247305105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4124297473573273663073473 3093223105179955247305105)
          ·
            refine ⟨2319917328884966435478829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3093223105179955247305105 2319917328884966435478829)
            ·
              refine ⟨869968998331862413304561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319917328884966435478829 869968998331862413304561)
              ·
                refine ⟨652476748748896809978421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 869968998331862413304561 652476748748896809978421)
                ·
                  refine ⟨61169695195209075935477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652476748748896809978421 61169695195209075935477)
                  ·
                    rfl

theorem cell22_536074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_536074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536074 prefixEnd_536074 := by exact prefixLift 536074
  have htrace : WordTrace (prefixWord ++ tailWord_536074) baseStart_536074 baseEnd_536074 := by
    simpa [prefixWord, tailWord_536074, baseEnd_536074] using wordTrace_append hprefix tailTrace_536074
  have hstable : (prefixWord ++ tailWord_536074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536074).length < 2 ^ (prefixWord ++ tailWord_536074).sum := by decide
  have hdescent : baseEnd_536074 < baseStart_536074 := by decide
  rcases family_descends (prefixWord ++ tailWord_536074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536151 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 2, 3]
def baseStart_536151 : Nat := 118140960795 + 536151 * 2 ^ 59
def prefixEnd_536151 : Nat := 4983230072969 + 3 ^ 40 * 536151 * 2
def baseEnd_536151 : Nat := 183535444259224693631195

theorem tailTrace_536151 : CollatzResearch.WordTrace tailWord_536151 prefixEnd_536151 183535444259224693631195 := by
  unfold tailWord_536151
  simp only [CollatzResearch.WordTrace]
  refine ⟨19555033480623969145864307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13036688987082646097242871 19555033480623969145864307)
  ·
    refine ⟨29332550220935953718796461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19555033480623969145864307 29332550220935953718796461)
    ·
      refine ⟨10999706332850982644548673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29332550220935953718796461 10999706332850982644548673)
      ·
        refine ⟨8249779749638236983411505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10999706332850982644548673 8249779749638236983411505)
        ·
          refine ⟨6187334812228677737558629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8249779749638236983411505 6187334812228677737558629)
          ·
            refine ⟨1160125277292877075792243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6187334812228677737558629 1160125277292877075792243)
            ·
              refine ⟨1740187915939315613688365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160125277292877075792243 1740187915939315613688365)
              ·
                refine ⟨652570468477243355133137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1740187915939315613688365 652570468477243355133137)
                ·
                  refine ⟨489427851357932516349853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652570468477243355133137 489427851357932516349853)
                  ·
                    refine ⟨183535444259224693631195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489427851357932516349853 183535444259224693631195)
                    ·
                      rfl

theorem cell22_536151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_536151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536151 prefixEnd_536151 := by exact prefixLift 536151
  have htrace : WordTrace (prefixWord ++ tailWord_536151) baseStart_536151 baseEnd_536151 := by
    simpa [prefixWord, tailWord_536151, baseEnd_536151] using wordTrace_append hprefix tailTrace_536151
  have hstable : (prefixWord ++ tailWord_536151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536151).length < 2 ^ (prefixWord ++ tailWord_536151).sum := by decide
  have hdescent : baseEnd_536151 < baseStart_536151 := by decide
  rcases family_descends (prefixWord ++ tailWord_536151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536177 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_536177 : Nat := 118140960795 + 536177 * 2 ^ 59
def prefixEnd_536177 : Nat := 4983230072969 + 3 ^ 40 * 536177 * 2
def baseEnd_536177 : Nat := 183544344590569292481115

theorem tailTrace_536177 : CollatzResearch.WordTrace tailWord_536177 prefixEnd_536177 183544344590569292481115 := by
  unfold tailWord_536177
  simp only [CollatzResearch.WordTrace]
  refine ⟨19555981778529775586310785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13037321185686517057540523 19555981778529775586310785)
  ·
    refine ⟨14666986333897331689733089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19555981778529775586310785 14666986333897331689733089)
    ·
      refine ⟨11000239750422998767299817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14666986333897331689733089 11000239750422998767299817)
      ·
        refine ⟨8250179812817249075474863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11000239750422998767299817 8250179812817249075474863)
        ·
          refine ⟨12375269719225873613212295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250179812817249075474863 12375269719225873613212295)
          ·
            refine ⟨18562904578838810419818443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12375269719225873613212295 18562904578838810419818443)
            ·
              refine ⟨27844356868258215629727665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18562904578838810419818443 27844356868258215629727665)
              ·
                refine ⟨20883267651193661722295749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27844356868258215629727665 20883267651193661722295749)
                ·
                  refine ⟨3915612684598811572930453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20883267651193661722295749 3915612684598811572930453)
                  ·
                    refine ⟨183544344590569292481115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3915612684598811572930453 183544344590569292481115)
                    ·
                      rfl

theorem cell22_536177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_536177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536177 prefixEnd_536177 := by exact prefixLift 536177
  have htrace : WordTrace (prefixWord ++ tailWord_536177) baseStart_536177 baseEnd_536177 := by
    simpa [prefixWord, tailWord_536177, baseEnd_536177] using wordTrace_append hprefix tailTrace_536177
  have hstable : (prefixWord ++ tailWord_536177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536177).length < 2 ^ (prefixWord ++ tailWord_536177).sum := by decide
  have hdescent : baseEnd_536177 < baseStart_536177 := by decide
  rcases family_descends (prefixWord ++ tailWord_536177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536301 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_536301 : Nat := 118140960795 + 536301 * 2 ^ 59
def prefixEnd_536301 : Nat := 4983230072969 + 3 ^ 40 * 536301 * 2
def baseEnd_536301 : Nat := 183586792324674302380735

theorem tailTrace_536301 : CollatzResearch.WordTrace tailWord_536301 prefixEnd_536301 183586792324674302380735 := by
  unfold tailWord_536301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560504430080544763824757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13040336286720363175883171 19560504430080544763824757)
  ·
    refine ⟨1833797290320051071608571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19560504430080544763824757 1833797290320051071608571)
    ·
      refine ⟨2750695935480076607412857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833797290320051071608571 2750695935480076607412857)
      ·
        refine ⟨2063021951610057455559643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750695935480076607412857 2063021951610057455559643)
        ·
          refine ⟨3094532927415086183339465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063021951610057455559643 3094532927415086183339465)
          ·
            refine ⟨2320899695561314637504599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3094532927415086183339465 2320899695561314637504599)
            ·
              refine ⟨3481349543341971956256899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320899695561314637504599 3481349543341971956256899)
              ·
                refine ⟨5222024315012957934385349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481349543341971956256899 5222024315012957934385349)
                ·
                  refine ⟨979129559064929612697253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5222024315012957934385349 979129559064929612697253)
                  ·
                    refine ⟨183586792324674302380735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 979129559064929612697253 183586792324674302380735)
                    ·
                      rfl

theorem cell22_536301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_536301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536301 prefixEnd_536301 := by exact prefixLift 536301
  have htrace : WordTrace (prefixWord ++ tailWord_536301) baseStart_536301 baseEnd_536301 := by
    simpa [prefixWord, tailWord_536301, baseEnd_536301] using wordTrace_append hprefix tailTrace_536301
  have hstable : (prefixWord ++ tailWord_536301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536301).length < 2 ^ (prefixWord ++ tailWord_536301).sum := by decide
  have hdescent : baseEnd_536301 < baseStart_536301 := by decide
  rcases family_descends (prefixWord ++ tailWord_536301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536331 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 3, 3]
def baseStart_536331 : Nat := 118140960795 + 536331 * 2 ^ 59
def prefixEnd_536331 : Nat := 4983230072969 + 3 ^ 40 * 536331 * 2
def baseEnd_536331 : Nat := 183597061937764224130643

theorem tailTrace_536331 : CollatzResearch.WordTrace tailWord_536331 prefixEnd_536331 183597061937764224130643 := by
  unfold tailWord_536331
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561598619971859887416847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13041065746647906591611231 19561598619971859887416847)
  ·
    refine ⟨29342397929957789831125271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19561598619971859887416847 29342397929957789831125271)
    ·
      refine ⟨44013596894936684746687907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29342397929957789831125271 44013596894936684746687907)
      ·
        refine ⟨66020395342405027120031861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44013596894936684746687907 66020395342405027120031861)
        ·
          refine ⟨6189412063350471292502987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66020395342405027120031861 6189412063350471292502987)
          ·
            refine ⟨9284118095025706938754481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189412063350471292502987 9284118095025706938754481)
            ·
              refine ⟨6963088571269280204065861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9284118095025706938754481 6963088571269280204065861)
              ·
                refine ⟨1305579107112990038262349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6963088571269280204065861 1305579107112990038262349)
                ·
                  refine ⟨489592165167371264348381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1305579107112990038262349 489592165167371264348381)
                  ·
                    refine ⟨183597061937764224130643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489592165167371264348381 183597061937764224130643)
                    ·
                      rfl

theorem cell22_536331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].length) (baseStart_536331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536331 prefixEnd_536331 := by exact prefixLift 536331
  have htrace : WordTrace (prefixWord ++ tailWord_536331) baseStart_536331 baseEnd_536331 := by
    simpa [prefixWord, tailWord_536331, baseEnd_536331] using wordTrace_append hprefix tailTrace_536331
  have hstable : (prefixWord ++ tailWord_536331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536331).length < 2 ^ (prefixWord ++ tailWord_536331).sum := by decide
  have hdescent : baseEnd_536331 < baseStart_536331 := by decide
  rcases family_descends (prefixWord ++ tailWord_536331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536344 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_536344 : Nat := 118140960795 + 536344 * 2 ^ 59
def prefixEnd_536344 : Nat := 4983230072969 + 3 ^ 40 * 536344 * 2
def baseEnd_536344 : Nat := 61200504034478841185201

theorem tailTrace_536344 : CollatzResearch.WordTrace tailWord_536344 prefixEnd_536344 61200504034478841185201 := by
  unfold tailWord_536344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781036384462381553820043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13041381845949842071760057 9781036384462381553820043)
  ·
    refine ⟨14671554576693572330730065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9781036384462381553820043 14671554576693572330730065)
    ·
      refine ⟨11003665932520179248047549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14671554576693572330730065 11003665932520179248047549)
      ·
        refine ⟨4126374724695067218017831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11003665932520179248047549 4126374724695067218017831)
        ·
          refine ⟨6189562087042600827026747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126374724695067218017831 6189562087042600827026747)
          ·
            refine ⟨9284343130563901240540121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189562087042600827026747 9284343130563901240540121)
            ·
              refine ⟨6963257347922925930405091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9284343130563901240540121 6963257347922925930405091)
              ·
                refine ⟨10444886021884388895607637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6963257347922925930405091 10444886021884388895607637)
                ·
                  refine ⟨61200504034478841185201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10444886021884388895607637 61200504034478841185201)
                  ·
                    rfl

theorem cell22_536344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_536344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536344 prefixEnd_536344 := by exact prefixLift 536344
  have htrace : WordTrace (prefixWord ++ tailWord_536344) baseStart_536344 baseEnd_536344 := by
    simpa [prefixWord, tailWord_536344, baseEnd_536344] using wordTrace_append hprefix tailTrace_536344
  have hstable : (prefixWord ++ tailWord_536344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536344).length < 2 ^ (prefixWord ++ tailWord_536344).sum := by decide
  have hdescent : baseEnd_536344 < baseStart_536344 := by decide
  rcases family_descends (prefixWord ++ tailWord_536344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536350 : List Nat := [4, 3, 2, 2, 2, 9]
def baseStart_536350 : Nat := 118140960795 + 536350 * 2 ^ 59
def prefixEnd_536350 : Nat := 4983230072969 + 3 ^ 40 * 536350 * 2
def baseEnd_536350 : Nat := 2266710691679685282785

theorem tailTrace_536350 : CollatzResearch.WordTrace tailWord_536350 prefixEnd_536350 2266710691679685282785 := by
  unfold tailWord_536350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445286450862878266544813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13041527737935350754905669 2445286450862878266544813)
  ·
    refine ⟨916982419073579349954305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2445286450862878266544813 916982419073579349954305)
    ·
      refine ⟨687736814305184512465729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 916982419073579349954305 687736814305184512465729)
      ·
        refine ⟨515802610728888384349297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687736814305184512465729 515802610728888384349297)
        ·
          refine ⟨386851958046666288261973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515802610728888384349297 386851958046666288261973)
          ·
            refine ⟨2266710691679685282785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 386851958046666288261973 2266710691679685282785)
            ·
              rfl

theorem cell22_536350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 9].length) (baseStart_536350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536350 prefixEnd_536350 := by exact prefixLift 536350
  have htrace : WordTrace (prefixWord ++ tailWord_536350) baseStart_536350 baseEnd_536350 := by
    simpa [prefixWord, tailWord_536350, baseEnd_536350] using wordTrace_append hprefix tailTrace_536350
  have hstable : (prefixWord ++ tailWord_536350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536350).length < 2 ^ (prefixWord ++ tailWord_536350).sum := by decide
  have hdescent : baseEnd_536350 < baseStart_536350 := by decide
  rcases family_descends (prefixWord ++ tailWord_536350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536376 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_536376 : Nat := 118140960795 + 536376 * 2 ^ 59
def prefixEnd_536376 : Nat := 4983230072969 + 3 ^ 40 * 536376 * 2
def baseEnd_536376 : Nat := 183612466357399106755505

theorem tailTrace_536376 : CollatzResearch.WordTrace tailWord_536376 prefixEnd_536376 183612466357399106755505 := by
  unfold tailWord_536376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781619952404416286402491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13042159936539221715203321 9781619952404416286402491)
  ·
    refine ⟨14672429928606624429603737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9781619952404416286402491 14672429928606624429603737)
    ·
      refine ⟨11004322446454968322202803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14672429928606624429603737 11004322446454968322202803)
      ·
        refine ⟨16506483669682452483304205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11004322446454968322202803 16506483669682452483304205)
        ·
          refine ⟨6189931376130919681239077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16506483669682452483304205 6189931376130919681239077)
          ·
            refine ⟨1160612133024547440232327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6189931376130919681239077 1160612133024547440232327)
            ·
              refine ⟨1740918199536821160348491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160612133024547440232327 1740918199536821160348491)
              ·
                refine ⟨2611377299305231740522737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740918199536821160348491 2611377299305231740522737)
                ·
                  refine ⟨1958532974478923805392053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2611377299305231740522737 1958532974478923805392053)
                  ·
                    refine ⟨183612466357399106755505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1958532974478923805392053 183612466357399106755505)
                    ·
                      rfl

theorem cell22_536376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_536376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536376 prefixEnd_536376 := by exact prefixLift 536376
  have htrace : WordTrace (prefixWord ++ tailWord_536376) baseStart_536376 baseEnd_536376 := by
    simpa [prefixWord, tailWord_536376, baseEnd_536376] using wordTrace_append hprefix tailTrace_536376
  have hstable : (prefixWord ++ tailWord_536376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536376).length < 2 ^ (prefixWord ++ tailWord_536376).sum := by decide
  have hdescent : baseEnd_536376 < baseStart_536376 := by decide
  rcases family_descends (prefixWord ++ tailWord_536376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536391 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_536391 : Nat := 118140960795 + 536391 * 2 ^ 59
def prefixEnd_536391 : Nat := 4983230072969 + 3 ^ 40 * 536391 * 2
def baseEnd_536391 : Nat := 183617601163944067630459

theorem tailTrace_536391 : CollatzResearch.WordTrace tailWord_536391 prefixEnd_536391 183617601163944067630459 := by
  unfold tailWord_536391
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563786999754490134601027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13042524666502993423067351 19563786999754490134601027)
  ·
    refine ⟨29345680499631735201901541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19563786999754490134601027 29345680499631735201901541)
    ·
      refine ⟨5502315093680950350356539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29345680499631735201901541 5502315093680950350356539)
      ·
        refine ⟨8253472640521425525534809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502315093680950350356539 8253472640521425525534809)
        ·
          refine ⟨6190104480391069144151107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8253472640521425525534809 6190104480391069144151107)
          ·
            refine ⟨9285156720586603716226661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190104480391069144151107 9285156720586603716226661)
            ·
              refine ⟨1740966885109988196792499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9285156720586603716226661 1740966885109988196792499)
              ·
                refine ⟨2611450327664982295188749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740966885109988196792499 2611450327664982295188749)
                ·
                  refine ⟨979293872874368360695781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2611450327664982295188749 979293872874368360695781)
                  ·
                    refine ⟨183617601163944067630459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 979293872874368360695781 183617601163944067630459)
                    ·
                      rfl

theorem cell22_536391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_536391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536391 prefixEnd_536391 := by exact prefixLift 536391
  have htrace : WordTrace (prefixWord ++ tailWord_536391) baseStart_536391 baseEnd_536391 := by
    simpa [prefixWord, tailWord_536391, baseEnd_536391] using wordTrace_append hprefix tailTrace_536391
  have hstable : (prefixWord ++ tailWord_536391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536391).length < 2 ^ (prefixWord ++ tailWord_536391).sum := by decide
  have hdescent : baseEnd_536391 < baseStart_536391 := by decide
  rcases family_descends (prefixWord ++ tailWord_536391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536412 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_536412 : Nat := 118140960795 + 536412 * 2 ^ 59
def prefixEnd_536412 : Nat := 4983230072969 + 3 ^ 40 * 536412 * 2
def baseEnd_536412 : Nat := 61208263297702337618465

theorem tailTrace_536412 : CollatzResearch.WordTrace tailWord_536412 prefixEnd_536412 61208263297702337618465 := by
  unfold tailWord_536412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9782276466339205360557745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13043035288452273814076993 9782276466339205360557745)
  ·
    refine ⟨7336707349754404020418309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9782276466339205360557745 7336707349754404020418309)
    ·
      refine ⟨1375632628078950753828433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7336707349754404020418309 1375632628078950753828433)
      ·
        refine ⟨1031724471059213065371325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1375632628078950753828433 1031724471059213065371325)
        ·
          refine ⟨386896676647204899514247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031724471059213065371325 386896676647204899514247)
          ·
            refine ⟨580345014970807349271371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386896676647204899514247 580345014970807349271371)
            ·
              refine ⟨870517522456211023907057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580345014970807349271371 870517522456211023907057)
              ·
                refine ⟨652888141842158267930293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870517522456211023907057 652888141842158267930293)
                ·
                  refine ⟨61208263297702337618465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652888141842158267930293 61208263297702337618465)
                  ·
                    rfl

theorem cell22_536412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_536412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536412 prefixEnd_536412 := by exact prefixLift 536412
  have htrace : WordTrace (prefixWord ++ tailWord_536412) baseStart_536412 baseEnd_536412 := by
    simpa [prefixWord, tailWord_536412, baseEnd_536412] using wordTrace_append hprefix tailTrace_536412
  have hstable : (prefixWord ++ tailWord_536412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536412).length < 2 ^ (prefixWord ++ tailWord_536412).sum := by decide
  have hdescent : baseEnd_536412 < baseStart_536412 := by decide
  rcases family_descends (prefixWord ++ tailWord_536412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536423 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 4]
def baseStart_536423 : Nat := 118140960795 + 536423 * 2 ^ 59
def prefixEnd_536423 : Nat := 4983230072969 + 3 ^ 40 * 536423 * 2
def baseEnd_536423 : Nat := 61209518472635550276787

theorem tailTrace_536423 : CollatzResearch.WordTrace tailWord_536423 prefixEnd_536423 61209518472635550276787 := by
  unfold tailWord_536423
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564954135638559599765923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13043302757092373066510615 19564954135638559599765923)
  ·
    refine ⟨29347431203457839399648885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19564954135638559599765923 29347431203457839399648885)
    ·
      refine ⟨2751321675324172443717083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29347431203457839399648885 2751321675324172443717083)
      ·
        refine ⟨4126982512986258665575625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751321675324172443717083 4126982512986258665575625)
        ·
          refine ⟨3095236884739693999181719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4126982512986258665575625 3095236884739693999181719)
          ·
            refine ⟨4642855327109540998772579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095236884739693999181719 4642855327109540998772579)
            ·
              refine ⟨6964282990664311498158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642855327109540998772579 6964282990664311498158869)
              ·
                refine ⟨326450765187389601476197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6964282990664311498158869 326450765187389601476197)
                ·
                  refine ⟨61209518472635550276787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326450765187389601476197 61209518472635550276787)
                  ·
                    rfl

theorem cell22_536423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 4].length) (baseStart_536423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536423 prefixEnd_536423 := by exact prefixLift 536423
  have htrace : WordTrace (prefixWord ++ tailWord_536423) baseStart_536423 baseEnd_536423 := by
    simpa [prefixWord, tailWord_536423, baseEnd_536423] using wordTrace_append hprefix tailTrace_536423
  have hstable : (prefixWord ++ tailWord_536423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536423).length < 2 ^ (prefixWord ++ tailWord_536423).sum := by decide
  have hdescent : baseEnd_536423 < baseStart_536423 := by decide
  rcases family_descends (prefixWord ++ tailWord_536423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536451 : List Nat := [1, 1, 1, 3, 4, 3, 1, 8]
def baseStart_536451 : Nat := 118140960795 + 536451 * 2 ^ 59
def prefixEnd_536451 : Nat := 4983230072969 + 3 ^ 40 * 536451 * 2
def baseEnd_536451 : Nat := 20404237821124879014475

theorem tailTrace_536451 : CollatzResearch.WordTrace tailWord_536451 prefixEnd_536451 20404237821124879014475 := by
  unfold tailWord_536451
  simp only [CollatzResearch.WordTrace]
  refine ⟨19565975379537120381785207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13043983586358080254523471 19565975379537120381785207)
  ·
    refine ⟨29348963069305680572677811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19565975379537120381785207 29348963069305680572677811)
    ·
      refine ⟨44023444603958520859016717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29348963069305680572677811 44023444603958520859016717)
      ·
        refine ⟨16508791726484445322131269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44023444603958520859016717 16508791726484445322131269)
        ·
          refine ⟨3095398448715833497899613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16508791726484445322131269 3095398448715833497899613)
          ·
            refine ⟨1160774418268437561712355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3095398448715833497899613 1160774418268437561712355)
            ·
              refine ⟨1741161627402656342568533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160774418268437561712355 1741161627402656342568533)
              ·
                refine ⟨20404237821124879014475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1741161627402656342568533 20404237821124879014475)
                ·
                  rfl

theorem cell22_536451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_536451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536451 prefixEnd_536451 := by exact prefixLift 536451
  have htrace : WordTrace (prefixWord ++ tailWord_536451) baseStart_536451 baseEnd_536451 := by
    simpa [prefixWord, tailWord_536451, baseEnd_536451] using wordTrace_append hprefix tailTrace_536451
  have hstable : (prefixWord ++ tailWord_536451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536451).length < 2 ^ (prefixWord ++ tailWord_536451).sum := by decide
  have hdescent : baseEnd_536451 < baseStart_536451 := by decide
  rcases family_descends (prefixWord ++ tailWord_536451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536468 : List Nat := [2, 4, 2, 1, 1, 4, 8]
def baseStart_536468 : Nat := 118140960795 + 536468 * 2 ^ 59
def prefixEnd_536468 : Nat := 4983230072969 + 3 ^ 40 * 536468 * 2
def baseEnd_536468 : Nat := 6801628142131167905749

theorem tailTrace_536468 : CollatzResearch.WordTrace tailWord_536468 prefixEnd_536468 6801628142131167905749 := by
  unfold tailWord_536468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783297710237766142577029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13044396946983688190102705 9783297710237766142577029)
  ·
    refine ⟨1834368320669581151733193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9783297710237766142577029 1834368320669581151733193)
    ·
      refine ⟨1375776240502185863799895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834368320669581151733193 1375776240502185863799895)
      ·
        refine ⟨2063664360753278795699843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375776240502185863799895 2063664360753278795699843)
        ·
          refine ⟨3095496541129918193549765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063664360753278795699843 3095496541129918193549765)
          ·
            refine ⟨580405601461859661290581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3095496541129918193549765 580405601461859661290581)
            ·
              refine ⟨6801628142131167905749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 580405601461859661290581 6801628142131167905749)
              ·
                rfl

theorem cell22_536468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 8].length) (baseStart_536468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536468 prefixEnd_536468 := by exact prefixLift 536468
  have htrace : WordTrace (prefixWord ++ tailWord_536468) baseStart_536468 baseEnd_536468 := by
    simpa [prefixWord, tailWord_536468, baseEnd_536468] using wordTrace_append hprefix tailTrace_536468
  have hstable : (prefixWord ++ tailWord_536468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536468).length < 2 ^ (prefixWord ++ tailWord_536468).sum := by decide
  have hdescent : baseEnd_536468 < baseStart_536468 := by decide
  rcases family_descends (prefixWord ++ tailWord_536468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536543 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_536543 : Nat := 118140960795 + 536543 * 2 ^ 59
def prefixEnd_536543 : Nat := 4983230072969 + 3 ^ 40 * 536543 * 2
def baseEnd_536543 : Nat := 183669633870266337829993

theorem tailTrace_536543 : CollatzResearch.WordTrace tailWord_536543 prefixEnd_536543 183669633870266337829993 := by
  unfold tailWord_536543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19569330895203820094134283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13046220596802546729422855 19569330895203820094134283)
  ·
    refine ⟨29353996342805730141201425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19569330895203820094134283 29353996342805730141201425)
    ·
      refine ⟨22015497257104297605901069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29353996342805730141201425 22015497257104297605901069)
      ·
        refine ⟨8255811471414111602212901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22015497257104297605901069 8255811471414111602212901)
        ·
          refine ⟨1547964650890145925414919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8255811471414111602212901 1547964650890145925414919)
          ·
            refine ⟨2321946976335218888122379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547964650890145925414919 2321946976335218888122379)
            ·
              refine ⟨3482920464502828332183569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321946976335218888122379 3482920464502828332183569)
              ·
                refine ⟨2612190348377121249137677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482920464502828332183569 2612190348377121249137677)
                ·
                  refine ⟨979571380641420468426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2612190348377121249137677 979571380641420468426629)
                  ·
                    refine ⟨183669633870266337829993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 979571380641420468426629 183669633870266337829993)
                    ·
                      rfl

theorem cell22_536543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_536543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536543 prefixEnd_536543 := by exact prefixLift 536543
  have htrace : WordTrace (prefixWord ++ tailWord_536543) baseStart_536543 baseEnd_536543 := by
    simpa [prefixWord, tailWord_536543, baseEnd_536543] using wordTrace_append hprefix tailTrace_536543
  have hstable : (prefixWord ++ tailWord_536543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536543).length < 2 ^ (prefixWord ++ tailWord_536543).sum := by decide
  have hdescent : baseEnd_536543 < baseStart_536543 := by decide
  rcases family_descends (prefixWord ++ tailWord_536543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536558 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_536558 : Nat := 118140960795 + 536558 * 2 ^ 59
def prefixEnd_536558 : Nat := 4983230072969 + 3 ^ 40 * 536558 * 2
def baseEnd_536558 : Nat := 61224922892270432901649

theorem tailTrace_536558 : CollatzResearch.WordTrace tailWord_536558 prefixEnd_536558 61224922892270432901649 := by
  unfold tailWord_536558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446234748768684706991291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13046585326766318437286885 2446234748768684706991291)
  ·
    refine ⟨3669352123153027060486937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2446234748768684706991291 3669352123153027060486937)
    ·
      refine ⟨2752014092364770295365203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3669352123153027060486937 2752014092364770295365203)
      ·
        refine ⟨4128021138547155443047805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752014092364770295365203 4128021138547155443047805)
        ·
          refine ⟨1548007926955183291142927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4128021138547155443047805 1548007926955183291142927)
          ·
            refine ⟨2322011890432774936714391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548007926955183291142927 2322011890432774936714391)
            ·
              refine ⟨3483017835649162405071587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322011890432774936714391 3483017835649162405071587)
              ·
                refine ⟨5224526753473743607607381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483017835649162405071587 5224526753473743607607381)
                ·
                  refine ⟨61224922892270432901649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5224526753473743607607381 61224922892270432901649)
                  ·
                    rfl

theorem cell22_536558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_536558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536558 prefixEnd_536558 := by exact prefixLift 536558
  have htrace : WordTrace (prefixWord ++ tailWord_536558) baseStart_536558 baseEnd_536558 := by
    simpa [prefixWord, tailWord_536558, baseEnd_536558] using wordTrace_append hprefix tailTrace_536558
  have hstable : (prefixWord ++ tailWord_536558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536558).length < 2 ^ (prefixWord ++ tailWord_536558).sum := by decide
  have hdescent : baseEnd_536558 < baseStart_536558 := by decide
  rcases family_descends (prefixWord ++ tailWord_536558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536573 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_536573 : Nat := 118140960795 + 536573 * 2 ^ 59
def prefixEnd_536573 : Nat := 4983230072969 + 3 ^ 40 * 536573 * 2
def baseEnd_536573 : Nat := 183679903483356259579901

theorem tailTrace_536573 : CollatzResearch.WordTrace tailWord_536573 prefixEnd_536573 183679903483356259579901 := by
  unfold tailWord_536573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19570425085095135217726373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13046950056730090145150915 19570425085095135217726373)
  ·
    refine ⟨3669454703455337853323695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19570425085095135217726373 3669454703455337853323695)
    ·
      refine ⟨5504182055183006779985543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669454703455337853323695 5504182055183006779985543)
      ·
        refine ⟨8256273082774510169978315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5504182055183006779985543 8256273082774510169978315)
        ·
          refine ⟨12384409624161765254967473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8256273082774510169978315 12384409624161765254967473)
          ·
            refine ⟨9288307218121323941225605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12384409624161765254967473 9288307218121323941225605)
            ·
              refine ⟨1741557603397748238979801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9288307218121323941225605 1741557603397748238979801)
              ·
                refine ⟨1306168202548311179234851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741557603397748238979801 1306168202548311179234851)
                ·
                  refine ⟨1959252303822466768852277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306168202548311179234851 1959252303822466768852277)
                  ·
                    refine ⟨183679903483356259579901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959252303822466768852277 183679903483356259579901)
                    ·
                      rfl

theorem cell22_536573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_536573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536573 prefixEnd_536573 := by exact prefixLift 536573
  have htrace : WordTrace (prefixWord ++ tailWord_536573) baseStart_536573 baseEnd_536573 := by
    simpa [prefixWord, tailWord_536573, baseEnd_536573] using wordTrace_append hprefix tailTrace_536573
  have hstable : (prefixWord ++ tailWord_536573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536573).length < 2 ^ (prefixWord ++ tailWord_536573).sum := by decide
  have hdescent : baseEnd_536573 < baseStart_536573 := by decide
  rcases family_descends (prefixWord ++ tailWord_536573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536588 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_536588 : Nat := 118140960795 + 536588 * 2 ^ 59
def prefixEnd_536588 : Nat := 4983230072969 + 3 ^ 40 * 536588 * 2
def baseEnd_536588 : Nat := 183685038289901220454855

theorem tailTrace_536588 : CollatzResearch.WordTrace tailWord_536588 prefixEnd_536588 183685038289901220454855 := by
  unfold tailWord_536588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785486090020396389761209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13047314786693861853014945 9785486090020396389761209)
  ·
    refine ⟨7339114567515297292320907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9785486090020396389761209 7339114567515297292320907)
    ·
      refine ⟨11008671851272945938481361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339114567515297292320907 11008671851272945938481361)
      ·
        refine ⟨8256503888454709453861021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11008671851272945938481361 8256503888454709453861021)
        ·
          refine ⟨3096188958170516045197883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8256503888454709453861021 3096188958170516045197883)
          ·
            refine ⟨4644283437255774067796825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096188958170516045197883 4644283437255774067796825)
            ·
              refine ⟨3483212577941830550847619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4644283437255774067796825 3483212577941830550847619)
              ·
                refine ⟨5224818866912745826271429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483212577941830550847619 5224818866912745826271429)
                ·
                  refine ⟨979653537546139842425893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5224818866912745826271429 979653537546139842425893)
                  ·
                    refine ⟨183685038289901220454855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 979653537546139842425893 183685038289901220454855)
                    ·
                      rfl

theorem cell22_536588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_536588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536588 prefixEnd_536588 := by exact prefixLift 536588
  have htrace : WordTrace (prefixWord ++ tailWord_536588) baseStart_536588 baseEnd_536588 := by
    simpa [prefixWord, tailWord_536588, baseEnd_536588] using wordTrace_append hprefix tailTrace_536588
  have hstable : (prefixWord ++ tailWord_536588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536588).length < 2 ^ (prefixWord ++ tailWord_536588).sum := by decide
  have hdescent : baseEnd_536588 < baseStart_536588 := by decide
  rcases family_descends (prefixWord ++ tailWord_536588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536590 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_536590 : Nat := 118140960795 + 536590 * 2 ^ 59
def prefixEnd_536590 : Nat := 4983230072969 + 3 ^ 40 * 536590 * 2
def baseEnd_536590 : Nat := 183685722930773881904849

theorem tailTrace_536590 : CollatzResearch.WordTrace tailWord_536590 prefixEnd_536590 183685722930773881904849 := by
  unfold tailWord_536590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446380640754193390136903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13047363417355698080730149 2446380640754193390136903)
  ·
    refine ⟨3669570961131290085205355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2446380640754193390136903 3669570961131290085205355)
    ·
      refine ⟨5504356441696935127808033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669570961131290085205355 5504356441696935127808033)
      ·
        refine ⟨4128267331272701345856025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5504356441696935127808033 4128267331272701345856025)
        ·
          refine ⟨3096200498454526009392019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4128267331272701345856025 3096200498454526009392019)
          ·
            refine ⟨4644300747681789014088029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096200498454526009392019 4644300747681789014088029)
            ·
              refine ⟨1741612780380670880283011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4644300747681789014088029 1741612780380670880283011)
              ·
                refine ⟨2612419170571006320424517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741612780380670880283011 2612419170571006320424517)
                ·
                  refine ⟨489828594482063685079597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2612419170571006320424517 489828594482063685079597)
                  ·
                    refine ⟨183685722930773881904849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489828594482063685079597 183685722930773881904849)
                    ·
                      rfl

theorem cell22_536590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_536590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536590 prefixEnd_536590 := by exact prefixLift 536590
  have htrace : WordTrace (prefixWord ++ tailWord_536590) baseStart_536590 baseEnd_536590 := by
    simpa [prefixWord, tailWord_536590, baseEnd_536590] using wordTrace_append hprefix tailTrace_536590
  have hstable : (prefixWord ++ tailWord_536590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536590).length < 2 ^ (prefixWord ++ tailWord_536590).sum := by decide
  have hdescent : baseEnd_536590 < baseStart_536590 := by decide
  rcases family_descends (prefixWord ++ tailWord_536590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536607 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 2, 3]
def baseStart_536607 : Nat := 118140960795 + 536607 * 2 ^ 59
def prefixEnd_536607 : Nat := 4983230072969 + 3 ^ 40 * 536607 * 2
def baseEnd_536607 : Nat := 183691542378191504229797

theorem tailTrace_536607 : CollatzResearch.WordTrace tailWord_536607 prefixEnd_536607 183691542378191504229797 := by
  unfold tailWord_536607
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571665166971959024464075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13047776777981306016309383 19571665166971959024464075)
  ·
    refine ⟨29357497750457938536696113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19571665166971959024464075 29357497750457938536696113)
    ·
      refine ⟨22018123312843453902522085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29357497750457938536696113 22018123312843453902522085)
      ·
        refine ⟨4128398121158147606722891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22018123312843453902522085 4128398121158147606722891)
        ·
          refine ⟨6192597181737221410084337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128398121158147606722891 6192597181737221410084337)
          ·
            refine ⟨4644447886302916057563253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192597181737221410084337 4644447886302916057563253)
            ·
              refine ⟨435416989340898380396555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4644447886302916057563253 435416989340898380396555)
              ·
                refine ⟨653125484011347570594833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435416989340898380396555 653125484011347570594833)
                ·
                  refine ⟨489844113008510677946125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653125484011347570594833 489844113008510677946125)
                  ·
                    refine ⟨183691542378191504229797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489844113008510677946125 183691542378191504229797)
                    ·
                      rfl

theorem cell22_536607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_536607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536607 prefixEnd_536607 := by exact prefixLift 536607
  have htrace : WordTrace (prefixWord ++ tailWord_536607) baseStart_536607 baseEnd_536607 := by
    simpa [prefixWord, tailWord_536607, baseEnd_536607] using wordTrace_append hprefix tailTrace_536607
  have hstable : (prefixWord ++ tailWord_536607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536607).length < 2 ^ (prefixWord ++ tailWord_536607).sum := by decide
  have hdescent : baseEnd_536607 < baseStart_536607 := by decide
  rcases family_descends (prefixWord ++ tailWord_536607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536652 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_536652 : Nat := 118140960795 + 536652 * 2 ^ 59
def prefixEnd_536652 : Nat := 4983230072969 + 3 ^ 40 * 536652 * 2
def baseEnd_536652 : Nat := 183706946797826386854659

theorem tailTrace_536652 : CollatzResearch.WordTrace tailWord_536652 prefixEnd_536652 183706946797826386854659 := by
  unfold tailWord_536652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9786653225904465854926105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13048870967872621139901473 9786653225904465854926105)
  ·
    refine ⟨7339989919428349391194579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9786653225904465854926105 7339989919428349391194579)
    ·
      refine ⟨11009984879142524086791869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339989919428349391194579 11009984879142524086791869)
      ·
        refine ⟨4128744329678446532546951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11009984879142524086791869 4128744329678446532546951)
        ·
          refine ⟨6193116494517669798820427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128744329678446532546951 6193116494517669798820427)
          ·
            refine ⟨9289674741776504698230641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193116494517669798820427 9289674741776504698230641)
            ·
              refine ⟨6967256056332378523672981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9289674741776504698230641 6967256056332378523672981)
              ·
                refine ⟨326590127640580243297171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6967256056332378523672981 326590127640580243297171)
                ·
                  refine ⟨489885191460870364945757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326590127640580243297171 489885191460870364945757)
                  ·
                    refine ⟨183706946797826386854659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489885191460870364945757 183706946797826386854659)
                    ·
                      rfl

theorem cell22_536652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_536652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536652 prefixEnd_536652 := by exact prefixLift 536652
  have htrace : WordTrace (prefixWord ++ tailWord_536652) baseStart_536652 baseEnd_536652 := by
    simpa [prefixWord, tailWord_536652, baseEnd_536652] using wordTrace_append hprefix tailTrace_536652
  have hstable : (prefixWord ++ tailWord_536652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536652).length < 2 ^ (prefixWord ++ tailWord_536652).sum := by decide
  have hdescent : baseEnd_536652 < baseStart_536652 := by decide
  rcases family_descends (prefixWord ++ tailWord_536652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536663 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_536663 : Nat := 118140960795 + 536663 * 2 ^ 59
def prefixEnd_536663 : Nat := 4983230072969 + 3 ^ 40 * 536663 * 2
def baseEnd_536663 : Nat := 183710712322626024829625

theorem tailTrace_536663 : CollatzResearch.WordTrace tailWord_536663 prefixEnd_536663 183710712322626024829625 := by
  unfold tailWord_536663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19573707654769080588502643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13049138436512720392335095 19573707654769080588502643)
  ·
    refine ⟨29360561482153620882753965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19573707654769080588502643 29360561482153620882753965)
    ·
      refine ⟨11010210555807607831032737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29360561482153620882753965 11010210555807607831032737)
      ·
        refine ⟨8257657916855705873274553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11010210555807607831032737 8257657916855705873274553)
        ·
          refine ⟨6193243437641779404955915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8257657916855705873274553 6193243437641779404955915)
          ·
            refine ⟨9289865156462669107433873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193243437641779404955915 9289865156462669107433873)
            ·
              refine ⟨6967398867347001830575405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9289865156462669107433873 6967398867347001830575405)
              ·
                refine ⟨2612774575255125686465777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6967398867347001830575405 2612774575255125686465777)
                ·
                  refine ⟨1959580931441344264849333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612774575255125686465777 1959580931441344264849333)
                  ·
                    refine ⟨183710712322626024829625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959580931441344264849333 183710712322626024829625)
                    ·
                      rfl

theorem cell22_536663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_536663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536663 prefixEnd_536663 := by exact prefixLift 536663
  have htrace : WordTrace (prefixWord ++ tailWord_536663) baseStart_536663 baseEnd_536663 := by
    simpa [prefixWord, tailWord_536663, baseEnd_536663] using wordTrace_append hprefix tailTrace_536663
  have hstable : (prefixWord ++ tailWord_536663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536663).length < 2 ^ (prefixWord ++ tailWord_536663).sum := by decide
  have hdescent : baseEnd_536663 < baseStart_536663 := by decide
  rcases family_descends (prefixWord ++ tailWord_536663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536723 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_536723 : Nat := 118140960795 + 536723 * 2 ^ 59
def prefixEnd_536723 : Nat := 4983230072969 + 3 ^ 40 * 536723 * 2
def baseEnd_536723 : Nat := 183731251548805868329441

theorem tailTrace_536723 : CollatzResearch.WordTrace tailWord_536723 prefixEnd_536723 183731251548805868329441 := by
  unfold tailWord_536723
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575896034551710835686823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13050597356367807223791215 19575896034551710835686823)
  ·
    refine ⟨29363844051827566253530235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19575896034551710835686823 29363844051827566253530235)
    ·
      refine ⟨44045766077741349380295353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29363844051827566253530235 44045766077741349380295353)
      ·
        refine ⟨33034324558306012035221515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44045766077741349380295353 33034324558306012035221515)
        ·
          refine ⟨49551486837459018052832273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33034324558306012035221515 49551486837459018052832273)
          ·
            refine ⟨37163615128094263539624205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49551486837459018052832273 37163615128094263539624205)
            ·
              refine ⟨13936355673035348827359077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37163615128094263539624205 13936355673035348827359077)
              ·
                refine ⟨2613066688694127905129827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13936355673035348827359077 2613066688694127905129827)
                ·
                  refine ⟨3919600033041191857694741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613066688694127905129827 3919600033041191857694741)
                  ·
                    refine ⟨183731251548805868329441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3919600033041191857694741 183731251548805868329441)
                    ·
                      rfl

theorem cell22_536723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_536723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536723 prefixEnd_536723 := by exact prefixLift 536723
  have htrace : WordTrace (prefixWord ++ tailWord_536723) baseStart_536723 baseEnd_536723 := by
    simpa [prefixWord, tailWord_536723, baseEnd_536723] using wordTrace_append hprefix tailTrace_536723
  have hstable : (prefixWord ++ tailWord_536723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536723).length < 2 ^ (prefixWord ++ tailWord_536723).sum := by decide
  have hdescent : baseEnd_536723 < baseStart_536723 := by decide
  rcases family_descends (prefixWord ++ tailWord_536723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536725 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_536725 : Nat := 118140960795 + 536725 * 2 ^ 59
def prefixEnd_536725 : Nat := 4983230072969 + 3 ^ 40 * 536725 * 2
def baseEnd_536725 : Nat := 183731936189678529779435

theorem tailTrace_536725 : CollatzResearch.WordTrace tailWord_536725 prefixEnd_536725 183731936189678529779435 := by
  unfold tailWord_536725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575968980544465177259629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13050645987029643451506419 19575968980544465177259629)
  ·
    refine ⟨7340988367704174441472361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19575968980544465177259629 7340988367704174441472361)
    ·
      refine ⟨5505741275778130831104271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7340988367704174441472361 5505741275778130831104271)
      ·
        refine ⟨8258611913667196246656407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505741275778130831104271 8258611913667196246656407)
        ·
          refine ⟨12387917870500794369984611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8258611913667196246656407 12387917870500794369984611)
          ·
            refine ⟨18581876805751191554976917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12387917870500794369984611 18581876805751191554976917)
            ·
              refine ⟨871025475269587104139543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18581876805751191554976917 871025475269587104139543)
              ·
                refine ⟨1306538212904380656209315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871025475269587104139543 1306538212904380656209315)
                ·
                  refine ⟨1959807319356570984313973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306538212904380656209315 1959807319356570984313973)
                  ·
                    refine ⟨183731936189678529779435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1959807319356570984313973 183731936189678529779435)
                    ·
                      rfl

theorem cell22_536725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_536725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536725 prefixEnd_536725 := by exact prefixLift 536725
  have htrace : WordTrace (prefixWord ++ tailWord_536725) baseStart_536725 baseEnd_536725 := by
    simpa [prefixWord, tailWord_536725, baseEnd_536725] using wordTrace_append hprefix tailTrace_536725
  have hstable : (prefixWord ++ tailWord_536725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536725).length < 2 ^ (prefixWord ++ tailWord_536725).sum := by decide
  have hdescent : baseEnd_536725 < baseStart_536725 := by decide
  rcases family_descends (prefixWord ++ tailWord_536725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536759 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 2, 3]
def baseStart_536759 : Nat := 118140960795 + 536759 * 2 ^ 59
def prefixEnd_536759 : Nat := 4983230072969 + 3 ^ 40 * 536759 * 2
def baseEnd_536759 : Nat := 183743575084513774429331

theorem tailTrace_536759 : CollatzResearch.WordTrace tailWord_536759 prefixEnd_536759 183743575084513774429331 := by
  unfold tailWord_536759
  simp only [CollatzResearch.WordTrace]
  refine ⟨19577209062421288983997331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13051472708280859322664887 19577209062421288983997331)
  ·
    refine ⟨29365813593631933475995997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19577209062421288983997331 29365813593631933475995997)
    ·
      refine ⟨11012180097611975053498499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29365813593631933475995997 11012180097611975053498499)
      ·
        refine ⟨16518270146417962580247749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11012180097611975053498499 16518270146417962580247749)
        ·
          refine ⟨3097175652453367983796453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16518270146417962580247749 3097175652453367983796453)
          ·
            refine ⟨580720434835006496961835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3097175652453367983796453 580720434835006496961835)
            ·
              refine ⟨871080652252509745442753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580720434835006496961835 871080652252509745442753)
              ·
                refine ⟨653310489189382309082065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871080652252509745442753 653310489189382309082065)
                ·
                  refine ⟨489982866892036731811549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653310489189382309082065 489982866892036731811549)
                  ·
                    refine ⟨183743575084513774429331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 489982866892036731811549 183743575084513774429331)
                    ·
                      rfl

theorem cell22_536759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_536759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536759 prefixEnd_536759 := by exact prefixLift 536759
  have htrace : WordTrace (prefixWord ++ tailWord_536759) baseStart_536759 baseEnd_536759 := by
    simpa [prefixWord, tailWord_536759, baseEnd_536759] using wordTrace_append hprefix tailTrace_536759
  have hstable : (prefixWord ++ tailWord_536759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536759).length < 2 ^ (prefixWord ++ tailWord_536759).sum := by decide
  have hdescent : baseEnd_536759 < baseStart_536759 := by decide
  rcases family_descends (prefixWord ++ tailWord_536759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536789 : List Nat := [1, 3, 2, 4, 2, 2, 2, 6]
def baseStart_536789 : Nat := 118140960795 + 536789 * 2 ^ 59
def prefixEnd_536789 : Nat := 4983230072969 + 3 ^ 40 * 536789 * 2
def baseEnd_536789 : Nat := 20417093855289299575471

theorem tailTrace_536789 : CollatzResearch.WordTrace tailWord_536789 prefixEnd_536789 20417093855289299575471 := by
  unfold tailWord_536789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19578303252312604107589421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052202168208402738392947 19578303252312604107589421)
  ·
    refine ⟨7341863719617226540346033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19578303252312604107589421 7341863719617226540346033)
    ·
      refine ⟨5506397789712919905259525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7341863719617226540346033 5506397789712919905259525)
      ·
        refine ⟨1032449585571172482236161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5506397789712919905259525 1032449585571172482236161)
        ·
          refine ⟨774337189178379361677121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032449585571172482236161 774337189178379361677121)
          ·
            refine ⟨580752891883784521257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774337189178379361677121 580752891883784521257841)
            ·
              refine ⟨435564668912838390943381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580752891883784521257841 435564668912838390943381)
              ·
                refine ⟨20417093855289299575471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 435564668912838390943381 20417093855289299575471)
                ·
                  rfl

theorem cell22_536789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 6].length) (baseStart_536789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536789 prefixEnd_536789 := by exact prefixLift 536789
  have htrace : WordTrace (prefixWord ++ tailWord_536789) baseStart_536789 baseEnd_536789 := by
    simpa [prefixWord, tailWord_536789, baseEnd_536789] using wordTrace_append hprefix tailTrace_536789
  have hstable : (prefixWord ++ tailWord_536789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536789).length < 2 ^ (prefixWord ++ tailWord_536789).sum := by decide
  have hdescent : baseEnd_536789 < baseStart_536789 := by decide
  rcases family_descends (prefixWord ++ tailWord_536789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536834 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_536834 : Nat := 118140960795 + 536834 * 2 ^ 59
def prefixEnd_536834 : Nat := 4983230072969 + 3 ^ 40 * 536834 * 2
def baseEnd_536834 : Nat := 61256416372412859601367

theorem tailTrace_536834 : CollatzResearch.WordTrace tailWord_536834 prefixEnd_536834 61256416372412859601367 := by
  unfold tailWord_536834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894986134287394198244389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13053296358099717861985037 4894986134287394198244389)
  ·
    refine ⟨917809900178886412170823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4894986134287394198244389 917809900178886412170823)
    ·
      refine ⟨1376714850268329618256235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917809900178886412170823 1376714850268329618256235)
      ·
        refine ⟨2065072275402494427384353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376714850268329618256235 2065072275402494427384353)
        ·
          refine ⟨1548804206551870820538265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2065072275402494427384353 1548804206551870820538265)
          ·
            refine ⟨1161603154913903115403699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548804206551870820538265 1161603154913903115403699)
            ·
              refine ⟨1742404732370854673105549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161603154913903115403699 1742404732370854673105549)
              ·
                refine ⟨653401774639070502414581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742404732370854673105549 653401774639070502414581)
                ·
                  refine ⟨61256416372412859601367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 653401774639070502414581 61256416372412859601367)
                  ·
                    rfl

theorem cell22_536834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_536834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536834 prefixEnd_536834 := by exact prefixLift 536834
  have htrace : WordTrace (prefixWord ++ tailWord_536834) baseStart_536834 baseEnd_536834 := by
    simpa [prefixWord, tailWord_536834, baseEnd_536834] using wordTrace_append hprefix tailTrace_536834
  have hstable : (prefixWord ++ tailWord_536834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536834).length < 2 ^ (prefixWord ++ tailWord_536834).sum := by decide
  have hdescent : baseEnd_536834 < baseStart_536834 := by decide
  rcases family_descends (prefixWord ++ tailWord_536834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536879 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 4]
def baseStart_536879 : Nat := 118140960795 + 536879 * 2 ^ 59
def prefixEnd_536879 : Nat := 4983230072969 + 3 ^ 40 * 536879 * 2
def baseEnd_536879 : Nat := 61261551178957820476321

theorem tailTrace_536879 : CollatzResearch.WordTrace tailWord_536879 prefixEnd_536879 61261551178957820476321 := by
  unfold tailWord_536879
  simp only [CollatzResearch.WordTrace]
  refine ⟨19581585821986549478365691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13054390547991032985577127 19581585821986549478365691)
  ·
    refine ⟨29372378732979824217548537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19581585821986549478365691 29372378732979824217548537)
    ·
      refine ⟨22029284049734868163161403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29372378732979824217548537 22029284049734868163161403)
      ·
        refine ⟨33043926074602302244742105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22029284049734868163161403 33043926074602302244742105)
        ·
          refine ⟨24782944555951726683556579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33043926074602302244742105 24782944555951726683556579)
          ·
            refine ⟨37174416833927590025334869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24782944555951726683556579 37174416833927590025334869)
            ·
              refine ⟨435637697272588945609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 37174416833927590025334869 435637697272588945609393)
              ·
                refine ⟨326728272954441709207045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435637697272588945609393 326728272954441709207045)
                ·
                  refine ⟨61261551178957820476321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326728272954441709207045 61261551178957820476321)
                  ·
                    rfl

theorem cell22_536879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 4].length) (baseStart_536879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536879 prefixEnd_536879 := by exact prefixLift 536879
  have htrace : WordTrace (prefixWord ++ tailWord_536879) baseStart_536879 baseEnd_536879 := by
    simpa [prefixWord, tailWord_536879, baseEnd_536879] using wordTrace_append hprefix tailTrace_536879
  have hstable : (prefixWord ++ tailWord_536879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536879).length < 2 ^ (prefixWord ++ tailWord_536879).sum := by decide
  have hdescent : baseEnd_536879 < baseStart_536879 := by decide
  rcases family_descends (prefixWord ++ tailWord_536879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536894 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_536894 : Nat := 118140960795 + 536894 * 2 ^ 59
def prefixEnd_536894 : Nat := 4983230072969 + 3 ^ 40 * 536894 * 2
def baseEnd_536894 : Nat := 183789788343418422303917

theorem tailTrace_536894 : CollatzResearch.WordTrace tailWord_536894 prefixEnd_536894 183789788343418422303917 := by
  unfold tailWord_536894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447766614616525880020217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13054755277954804693441157 2447766614616525880020217)
  ·
    refine ⟨1835824960962394410015163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2447766614616525880020217 1835824960962394410015163)
    ·
      refine ⟨2753737441443591615022745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835824960962394410015163 2753737441443591615022745)
      ·
        refine ⟨2065303081082693711267059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2753737441443591615022745 2065303081082693711267059)
        ·
          refine ⟨3097954621624040566900589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065303081082693711267059 3097954621624040566900589)
          ·
            refine ⟨1161732983109015212587721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3097954621624040566900589 1161732983109015212587721)
            ·
              refine ⟨871299737331761409440791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161732983109015212587721 871299737331761409440791)
              ·
                refine ⟨1306949605997642114161187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871299737331761409440791 1306949605997642114161187)
                ·
                  refine ⟨1960424408996463171241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306949605997642114161187 1960424408996463171241781)
                  ·
                    refine ⟨183789788343418422303917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1960424408996463171241781 183789788343418422303917)
                    ·
                      rfl

theorem cell22_536894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_536894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536894 prefixEnd_536894 := by exact prefixLift 536894
  have htrace : WordTrace (prefixWord ++ tailWord_536894) baseStart_536894 baseEnd_536894 := by
    simpa [prefixWord, tailWord_536894, baseEnd_536894] using wordTrace_append hprefix tailTrace_536894
  have hstable : (prefixWord ++ tailWord_536894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536894).length < 2 ^ (prefixWord ++ tailWord_536894).sum := by decide
  have hdescent : baseEnd_536894 < baseStart_536894 := by decide
  rcases family_descends (prefixWord ++ tailWord_536894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536920 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_536920 : Nat := 118140960795 + 536920 * 2 ^ 59
def prefixEnd_536920 : Nat := 4983230072969 + 3 ^ 40 * 536920 * 2
def baseEnd_536920 : Nat := 183798688674763021153837

theorem tailTrace_536920 : CollatzResearch.WordTrace tailWord_536920 prefixEnd_536920 183798688674763021153837 := by
  unfold tailWord_536920
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791540607419006740304107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13055387476558675653738809 9791540607419006740304107)
  ·
    refine ⟨14687310911128510110456161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9791540607419006740304107 14687310911128510110456161)
    ·
      refine ⟨11015483183346382582842121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14687310911128510110456161 11015483183346382582842121)
      ·
        refine ⟨8261612387509786937131591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11015483183346382582842121 8261612387509786937131591)
        ·
          refine ⟨12392418581264680405697387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261612387509786937131591 12392418581264680405697387)
          ·
            refine ⟨18588627871897020608546081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12392418581264680405697387 18588627871897020608546081)
            ·
              refine ⟨13941470903922765456409561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18588627871897020608546081 13941470903922765456409561)
              ·
                refine ⟨10456103177942074092307171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13941470903922765456409561 10456103177942074092307171)
                ·
                  refine ⟨15684154766913111138460757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10456103177942074092307171 15684154766913111138460757)
                  ·
                    refine ⟨183798688674763021153837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15684154766913111138460757 183798688674763021153837)
                    ·
                      rfl

theorem cell22_536920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_536920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536920 prefixEnd_536920 := by exact prefixLift 536920
  have htrace : WordTrace (prefixWord ++ tailWord_536920) baseStart_536920 baseEnd_536920 := by
    simpa [prefixWord, tailWord_536920, baseEnd_536920] using wordTrace_append hprefix tailTrace_536920
  have hstable : (prefixWord ++ tailWord_536920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536920).length < 2 ^ (prefixWord ++ tailWord_536920).sum := by decide
  have hdescent : baseEnd_536920 < baseStart_536920 := by decide
  rcases family_descends (prefixWord ++ tailWord_536920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536922 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_536922 : Nat := 118140960795 + 536922 * 2 ^ 59
def prefixEnd_536922 : Nat := 4983230072969 + 3 ^ 40 * 536922 * 2
def baseEnd_536922 : Nat := 183799373315635682603831

theorem tailTrace_536922 : CollatzResearch.WordTrace tailWord_536922 prefixEnd_536922 183799373315635682603831 := by
  unfold tailWord_536922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895788540207691955545255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13055436107220511881454013 4895788540207691955545255)
  ·
    refine ⟨7343682810311537933317883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895788540207691955545255 7343682810311537933317883)
    ·
      refine ⟨11015524215467306899976825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343682810311537933317883 11015524215467306899976825)
      ·
        refine ⟨8261643161600480174982619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11015524215467306899976825 8261643161600480174982619)
        ·
          refine ⟨12392464742400720262473929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261643161600480174982619 12392464742400720262473929)
          ·
            refine ⟨9294348556800540196855447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12392464742400720262473929 9294348556800540196855447)
            ·
              refine ⟨13941522835200810295283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9294348556800540196855447 13941522835200810295283171)
              ·
                refine ⟨20912284252801215442924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13941522835200810295283171 20912284252801215442924757)
                ·
                  refine ⟨490131662175028486943549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20912284252801215442924757 490131662175028486943549)
                  ·
                    refine ⟨183799373315635682603831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490131662175028486943549 183799373315635682603831)
                    ·
                      rfl

theorem cell22_536922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_536922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536922 prefixEnd_536922 := by exact prefixLift 536922
  have htrace : WordTrace (prefixWord ++ tailWord_536922) baseStart_536922 baseEnd_536922 := by
    simpa [prefixWord, tailWord_536922, baseEnd_536922] using wordTrace_append hprefix tailTrace_536922
  have hstable : (prefixWord ++ tailWord_536922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536922).length < 2 ^ (prefixWord ++ tailWord_536922).sum := by decide
  have hdescent : baseEnd_536922 < baseStart_536922 := by decide
  rcases family_descends (prefixWord ++ tailWord_536922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536924 : List Nat := [2, 2, 4, 3, 1, 1, 9]
def baseStart_536924 : Nat := 118140960795 + 536924 * 2 ^ 59
def prefixEnd_536924 : Nat := 4983230072969 + 3 ^ 40 * 536924 * 2
def baseEnd_536924 : Nat := 6807409553944753483475

theorem tailTrace_536924 : CollatzResearch.WordTrace tailWord_536924 prefixEnd_536924 6807409553944753483475 := by
  unfold tailWord_536924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791613553411761081876913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13055484737882348109169217 9791613553411761081876913)
  ·
    refine ⟨7343710165058820811407685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9791613553411761081876913 7343710165058820811407685)
    ·
      refine ⟨1376945655948528902138941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7343710165058820811407685 1376945655948528902138941)
      ·
        refine ⟨516354620980698338302103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1376945655948528902138941 516354620980698338302103)
        ·
          refine ⟨774531931471047507453155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516354620980698338302103 774531931471047507453155)
          ·
            refine ⟨1161797897206571261179733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774531931471047507453155 1161797897206571261179733)
            ·
              refine ⟨6807409553944753483475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1161797897206571261179733 6807409553944753483475)
              ·
                rfl

theorem cell22_536924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 9].length) (baseStart_536924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536924 prefixEnd_536924 := by exact prefixLift 536924
  have htrace : WordTrace (prefixWord ++ tailWord_536924) baseStart_536924 baseEnd_536924 := by
    simpa [prefixWord, tailWord_536924, baseEnd_536924] using wordTrace_append hprefix tailTrace_536924
  have hstable : (prefixWord ++ tailWord_536924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536924).length < 2 ^ (prefixWord ++ tailWord_536924).sum := by decide
  have hdescent : baseEnd_536924 < baseStart_536924 := by decide
  rcases family_descends (prefixWord ++ tailWord_536924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536928 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_536928 : Nat := 118140960795 + 536928 * 2 ^ 59
def prefixEnd_536928 : Nat := 4983230072969 + 3 ^ 40 * 536928 * 2
def baseEnd_536928 : Nat := 183801427238253666953813

theorem tailTrace_536928 : CollatzResearch.WordTrace tailWord_536928 prefixEnd_536928 183801427238253666953813 := by
  unfold tailWord_536928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791686499404515423449719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13055581999206020564599625 9791686499404515423449719)
  ·
    refine ⟨14687529749106773135174579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9791686499404515423449719 14687529749106773135174579)
    ·
      refine ⟨22031294623660159702761869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14687529749106773135174579 22031294623660159702761869)
      ·
        refine ⟨8261735483872559888535701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22031294623660159702761869 8261735483872559888535701)
        ·
          refine ⟨387268850806526244775111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8261735483872559888535701 387268850806526244775111)
          ·
            refine ⟨580903276209789367162667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387268850806526244775111 580903276209789367162667)
            ·
              refine ⟨871354914314684050744001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580903276209789367162667 871354914314684050744001)
              ·
                refine ⟨653516185736013038058001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871354914314684050744001 653516185736013038058001)
                ·
                  refine ⟨490137139302009778543501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653516185736013038058001 490137139302009778543501)
                  ·
                    refine ⟨183801427238253666953813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490137139302009778543501 183801427238253666953813)
                    ·
                      rfl

theorem cell22_536928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_536928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_536928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_536928 prefixEnd_536928 := by exact prefixLift 536928
  have htrace : WordTrace (prefixWord ++ tailWord_536928) baseStart_536928 baseEnd_536928 := by
    simpa [prefixWord, tailWord_536928, baseEnd_536928] using wordTrace_append hprefix tailTrace_536928
  have hstable : (prefixWord ++ tailWord_536928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536928).length < 2 ^ (prefixWord ++ tailWord_536928).sum := by decide
  have hdescent : baseEnd_536928 < baseStart_536928 := by decide
  rcases family_descends (prefixWord ++ tailWord_536928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537072 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_537072 : Nat := 118140960795 + 537072 * 2 ^ 59
def prefixEnd_537072 : Nat := 4983230072969 + 3 ^ 40 * 537072 * 2
def baseEnd_537072 : Nat := 183850721381085291353371

theorem tailTrace_537072 : CollatzResearch.WordTrace tailWord_537072 prefixEnd_537072 183850721381085291353371 := by
  unfold tailWord_537072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794312555143671720070735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13059083406858228960094313 9794312555143671720070735)
  ·
    refine ⟨14691468832715507580106103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794312555143671720070735 14691468832715507580106103)
    ·
      refine ⟨22037203249073261370159155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14691468832715507580106103 22037203249073261370159155)
      ·
        refine ⟨33055804873609892055238733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22037203249073261370159155 33055804873609892055238733)
        ·
          refine ⟨12395926827603709520714525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33055804873609892055238733 12395926827603709520714525)
          ·
            refine ⟨4648472560351391070267947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12395926827603709520714525 4648472560351391070267947)
            ·
              refine ⟨6972708840527086605401921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648472560351391070267947 6972708840527086605401921)
              ·
                refine ⟨5229531630395314954051441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6972708840527086605401921 5229531630395314954051441)
                ·
                  refine ⟨3922148722796486215538581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5229531630395314954051441 3922148722796486215538581)
                  ·
                    refine ⟨183850721381085291353371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3922148722796486215538581 183850721381085291353371)
                    ·
                      rfl

theorem cell22_537072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_537072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537072 prefixEnd_537072 := by exact prefixLift 537072
  have htrace : WordTrace (prefixWord ++ tailWord_537072) baseStart_537072 baseEnd_537072 := by
    simpa [prefixWord, tailWord_537072, baseEnd_537072] using wordTrace_append hprefix tailTrace_537072
  have hstable : (prefixWord ++ tailWord_537072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537072).length < 2 ^ (prefixWord ++ tailWord_537072).sum := by decide
  have hdescent : baseEnd_537072 < baseStart_537072 := by decide
  rcases family_descends (prefixWord ++ tailWord_537072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537087 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 7]
def baseStart_537087 : Nat := 118140960795 + 537087 * 2 ^ 59
def prefixEnd_537087 : Nat := 4983230072969 + 3 ^ 40 * 537087 * 2
def baseEnd_537087 : Nat := 61285285395876750742775

theorem tailTrace_537087 : CollatzResearch.WordTrace tailWord_537087 prefixEnd_537087 61285285395876750742775 := by
  unfold tailWord_537087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589172205233001001937515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13059448136822000667958343 19589172205233001001937515)
  ·
    refine ⟨29383758307849501502906273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19589172205233001001937515 29383758307849501502906273)
    ·
      refine ⟨22037818730887126127179705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29383758307849501502906273 22037818730887126127179705)
      ·
        refine ⟨16528364048165344595384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22037818730887126127179705 16528364048165344595384779)
        ·
          refine ⟨24792546072248016893077169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16528364048165344595384779 24792546072248016893077169)
          ·
            refine ⟨18594409554186012669807877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24792546072248016893077169 18594409554186012669807877)
            ·
              refine ⟨3486451791409877375588977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18594409554186012669807877 3486451791409877375588977)
              ·
                refine ⟨2614838843557408031691733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3486451791409877375588977 2614838843557408031691733)
                ·
                  refine ⟨61285285395876750742775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2614838843557408031691733 61285285395876750742775)
                  ·
                    rfl

theorem cell22_537087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_537087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537087 prefixEnd_537087 := by exact prefixLift 537087
  have htrace : WordTrace (prefixWord ++ tailWord_537087) baseStart_537087 baseEnd_537087 := by
    simpa [prefixWord, tailWord_537087, baseEnd_537087] using wordTrace_append hprefix tailTrace_537087
  have hstable : (prefixWord ++ tailWord_537087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537087).length < 2 ^ (prefixWord ++ tailWord_537087).sum := by decide
  have hdescent : baseEnd_537087 < baseStart_537087 := by decide
  rcases family_descends (prefixWord ++ tailWord_537087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537108 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_537108 : Nat := 118140960795 + 537108 * 2 ^ 59
def prefixEnd_537108 : Nat := 4983230072969 + 3 ^ 40 * 537108 * 2
def baseEnd_537108 : Nat := 183863044916793197453261

theorem tailTrace_537108 : CollatzResearch.WordTrace tailWord_537108 prefixEnd_537108 183863044916793197453261 := by
  unfold tailWord_537108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794969069078460794225989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13059958758771281058967985 9794969069078460794225989)
  ·
    refine ⟨1836556700452211398917373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9794969069078460794225989 1836556700452211398917373)
    ·
      refine ⟨688708762669579274594015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1836556700452211398917373 688708762669579274594015)
      ·
        refine ⟨1033063144004368911891023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688708762669579274594015 1033063144004368911891023)
        ·
          refine ⟨1549594716006553367836535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033063144004368911891023 1549594716006553367836535)
          ·
            refine ⟨2324392074009830051754803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549594716006553367836535 2324392074009830051754803)
            ·
              refine ⟨3486588111014745077632205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324392074009830051754803 3486588111014745077632205)
              ·
                refine ⟨1307470541630529404112077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3486588111014745077632205 1307470541630529404112077)
                ·
                  refine ⟨490301453111448526542029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1307470541630529404112077 490301453111448526542029)
                  ·
                    refine ⟨183863044916793197453261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490301453111448526542029 183863044916793197453261)
                    ·
                      rfl

theorem cell22_537108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_537108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537108 prefixEnd_537108 := by exact prefixLift 537108
  have htrace : WordTrace (prefixWord ++ tailWord_537108) baseStart_537108 baseEnd_537108 := by
    simpa [prefixWord, tailWord_537108, baseEnd_537108] using wordTrace_append hprefix tailTrace_537108
  have hstable : (prefixWord ++ tailWord_537108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537108).length < 2 ^ (prefixWord ++ tailWord_537108).sum := by decide
  have hdescent : baseEnd_537108 < baseStart_537108 := by decide
  rcases family_descends (prefixWord ++ tailWord_537108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537121 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 5]
def baseStart_537121 : Nat := 118140960795 + 537121 * 2 ^ 59
def prefixEnd_537121 : Nat := 4983230072969 + 3 ^ 40 * 537121 * 2
def baseEnd_537121 : Nat := 61289165027488498959407

theorem tailTrace_537121 : CollatzResearch.WordTrace tailWord_537121 prefixEnd_537121 61289165027488498959407 := by
  unfold tailWord_537121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590412287109824808675217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13060274858073216539116811 19590412287109824808675217)
  ·
    refine ⟨14692809215332368606506413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19590412287109824808675217 14692809215332368606506413)
    ·
      refine ⟨5509803455749638227439905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14692809215332368606506413 5509803455749638227439905)
      ·
        refine ⟨4132352591812228670579929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5509803455749638227439905 4132352591812228670579929)
        ·
          refine ⟨3099264443859171502934947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4132352591812228670579929 3099264443859171502934947)
          ·
            refine ⟨4648896665788757254402421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099264443859171502934947 4648896665788757254402421)
            ·
              refine ⟨435834062417695992600227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4648896665788757254402421 435834062417695992600227)
              ·
                refine ⟨653751093626543988900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435834062417695992600227 653751093626543988900341)
                ·
                  refine ⟨61289165027488498959407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 653751093626543988900341 61289165027488498959407)
                  ·
                    rfl

theorem cell22_537121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_537121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537121 prefixEnd_537121 := by exact prefixLift 537121
  have htrace : WordTrace (prefixWord ++ tailWord_537121) baseStart_537121 baseEnd_537121 := by
    simpa [prefixWord, tailWord_537121, baseEnd_537121] using wordTrace_append hprefix tailTrace_537121
  have hstable : (prefixWord ++ tailWord_537121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537121).length < 2 ^ (prefixWord ++ tailWord_537121).sum := by decide
  have hdescent : baseEnd_537121 < baseStart_537121 := by decide
  rcases family_descends (prefixWord ++ tailWord_537121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537142 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_537142 : Nat := 118140960795 + 537142 * 2 ^ 59
def prefixEnd_537142 : Nat := 4983230072969 + 3 ^ 40 * 537142 * 2
def baseEnd_537142 : Nat := 183874683811628442103157

theorem tailTrace_537142 : CollatzResearch.WordTrace tailWord_537142 prefixEnd_537142 183874683811628442103157 := by
  unfold tailWord_537142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224448638752109087199355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13060785480022496930126453 1224448638752109087199355)
  ·
    refine ⟨1836672958128163630799033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1224448638752109087199355 1836672958128163630799033)
    ·
      refine ⟨1377504718596122723099275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1836672958128163630799033 1377504718596122723099275)
      ·
        refine ⟨2066257077894184084648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377504718596122723099275 2066257077894184084648913)
        ·
          refine ⟨1549692808420638063486685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066257077894184084648913 1549692808420638063486685)
          ·
            refine ⟨581134803157739273807507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1549692808420638063486685 581134803157739273807507)
            ·
              refine ⟨871702204736608910711261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581134803157739273807507 871702204736608910711261)
              ·
                refine ⟨326888326776228341516723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871702204736608910711261 326888326776228341516723)
                ·
                  refine ⟨490332490164342512275085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326888326776228341516723 490332490164342512275085)
                  ·
                    refine ⟨183874683811628442103157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490332490164342512275085 183874683811628442103157)
                    ·
                      rfl

theorem cell22_537142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_537142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537142 prefixEnd_537142 := by exact prefixLift 537142
  have htrace : WordTrace (prefixWord ++ tailWord_537142) baseStart_537142 baseEnd_537142 := by
    simpa [prefixWord, tailWord_537142, baseEnd_537142] using wordTrace_append hprefix tailTrace_537142
  have hstable : (prefixWord ++ tailWord_537142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537142).length < 2 ^ (prefixWord ++ tailWord_537142).sum := by decide
  have hdescent : baseEnd_537142 < baseStart_537142 := by decide
  rcases family_descends (prefixWord ++ tailWord_537142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537166 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_537166 : Nat := 118140960795 + 537166 * 2 ^ 59
def prefixEnd_537166 : Nat := 4983230072969 + 3 ^ 40 * 537166 * 2
def baseEnd_537166 : Nat := 61294299834033459834361

theorem tailTrace_537166 : CollatzResearch.WordTrace tailWord_537166 prefixEnd_537166 61294299834033459834361 := by
  unfold tailWord_537166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2449006696493349686757919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13061369047964531662708901 2449006696493349686757919)
  ·
    refine ⟨3673510044740024530136879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2449006696493349686757919 3673510044740024530136879)
    ·
      refine ⟨5510265067110036795205319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673510044740024530136879 5510265067110036795205319)
      ·
        refine ⟨8265397600665055192807979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510265067110036795205319 8265397600665055192807979)
        ·
          refine ⟨12398096400997582789211969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8265397600665055192807979 12398096400997582789211969)
          ·
            refine ⟨9298572300748187091908977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12398096400997582789211969 9298572300748187091908977)
            ·
              refine ⟨6973929225561140318931733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9298572300748187091908977 6973929225561140318931733)
              ·
                refine ⟨326902932448178452449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6973929225561140318931733 326902932448178452449925)
                ·
                  refine ⟨61294299834033459834361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326902932448178452449925 61294299834033459834361)
                  ·
                    rfl

theorem cell22_537166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_537166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537166 prefixEnd_537166 := by exact prefixLift 537166
  have htrace : WordTrace (prefixWord ++ tailWord_537166) baseStart_537166 baseEnd_537166 := by
    simpa [prefixWord, tailWord_537166, baseEnd_537166] using wordTrace_append hprefix tailTrace_537166
  have hstable : (prefixWord ++ tailWord_537166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537166).length < 2 ^ (prefixWord ++ tailWord_537166).sum := by decide
  have hdescent : baseEnd_537166 < baseStart_537166 := by decide
  rcases family_descends (prefixWord ++ tailWord_537166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537194 : List Nat := [3, 1, 3, 2, 1, 1, 1, 10]
def baseStart_537194 : Nat := 118140960795 + 537194 * 2 ^ 59
def prefixEnd_537194 : Nat := 4983230072969 + 3 ^ 40 * 537194 * 2
def baseEnd_537194 : Nat := 20432498274924182200333

theorem tailTrace_537194 : CollatzResearch.WordTrace tailWord_537194 prefixEnd_537194 20432498274924182200333 := by
  unfold tailWord_537194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898268703961339569020659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13062049877230238850721757 4898268703961339569020659)
  ·
    refine ⟨7347403055942009353530989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4898268703961339569020659 7347403055942009353530989)
    ·
      refine ⟨2755276145978253507574121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7347403055942009353530989 2755276145978253507574121)
      ·
        refine ⟨2066457109483690130680591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2755276145978253507574121 2066457109483690130680591)
        ·
          refine ⟨3099685664225535196020887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2066457109483690130680591 3099685664225535196020887)
          ·
            refine ⟨4649528496338302794031331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099685664225535196020887 4649528496338302794031331)
            ·
              refine ⟨6974292744507454191046997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649528496338302794031331 6974292744507454191046997)
              ·
                refine ⟨20432498274924182200333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6974292744507454191046997 20432498274924182200333)
                ·
                  rfl

theorem cell22_537194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_537194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537194 prefixEnd_537194 := by exact prefixLift 537194
  have htrace : WordTrace (prefixWord ++ tailWord_537194) baseStart_537194 baseEnd_537194 := by
    simpa [prefixWord, tailWord_537194, baseEnd_537194] using wordTrace_append hprefix tailTrace_537194
  have hstable : (prefixWord ++ tailWord_537194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537194).length < 2 ^ (prefixWord ++ tailWord_537194).sum := by decide
  have hdescent : baseEnd_537194 < baseStart_537194 := by decide
  rcases family_descends (prefixWord ++ tailWord_537194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537303 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 1, 4]
def baseStart_537303 : Nat := 118140960795 + 537303 * 2 ^ 59
def prefixEnd_537303 : Nat := 4983230072969 + 3 ^ 40 * 537303 * 2
def baseEnd_537303 : Nat := 183929797401877688827663

theorem tailTrace_537303 : CollatzResearch.WordTrace tailWord_537303 prefixEnd_537303 183929797401877688827663 := by
  unfold tailWord_537303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19597050372450469891800563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13064700248300313261200375 19597050372450469891800563)
  ·
    refine ⟨29395575558675704837700845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19597050372450469891800563 29395575558675704837700845)
    ·
      refine ⟨11023340834503389314137817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29395575558675704837700845 11023340834503389314137817)
      ·
        refine ⟨8267505625877541985603363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11023340834503389314137817 8267505625877541985603363)
        ·
          refine ⟨12401258438816312978405045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267505625877541985603363 12401258438816312978405045)
          ·
            refine ⟨1162617978639029341725473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12401258438816312978405045 1162617978639029341725473)
            ·
              refine ⟨871963483979272006294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162617978639029341725473 871963483979272006294105)
              ·
                refine ⟨653972612984454004720579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871963483979272006294105 653972612984454004720579)
                ·
                  refine ⟨980958919476681007080869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653972612984454004720579 980958919476681007080869)
                  ·
                    refine ⟨183929797401877688827663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 980958919476681007080869 183929797401877688827663)
                    ·
                      rfl

theorem cell22_537303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_537303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537303 prefixEnd_537303 := by exact prefixLift 537303
  have htrace : WordTrace (prefixWord ++ tailWord_537303) baseStart_537303 baseEnd_537303 := by
    simpa [prefixWord, tailWord_537303, baseEnd_537303] using wordTrace_append hprefix tailTrace_537303
  have hstable : (prefixWord ++ tailWord_537303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537303).length < 2 ^ (prefixWord ++ tailWord_537303).sum := by decide
  have hdescent : baseEnd_537303 < baseStart_537303 := by decide
  rcases family_descends (prefixWord ++ tailWord_537303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537386 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_537386 : Nat := 118140960795 + 537386 * 2 ^ 59
def prefixEnd_537386 : Nat := 4983230072969 + 3 ^ 40 * 537386 * 2
def baseEnd_537386 : Nat := 61319403332697713000803

theorem tailTrace_537386 : CollatzResearch.WordTrace tailWord_537386 prefixEnd_537386 61319403332697713000803 := by
  unfold tailWord_537386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900019407787443766768003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13066718420766516711381341 4900019407787443766768003)
  ·
    refine ⟨7350029111681165650152005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900019407787443766768003 7350029111681165650152005)
    ·
      refine ⟨1378130458440218559403501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7350029111681165650152005 1378130458440218559403501)
      ·
        refine ⟨516798921915081959776313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1378130458440218559403501 516798921915081959776313)
        ·
          refine ⟨387599191436311469832235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516798921915081959776313 387599191436311469832235)
          ·
            refine ⟨581398787154467204748353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387599191436311469832235 581398787154467204748353)
            ·
              refine ⟨436049090365850403561265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581398787154467204748353 436049090365850403561265)
              ·
                refine ⟨327036817774387802670949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436049090365850403561265 327036817774387802670949)
                ·
                  refine ⟨61319403332697713000803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327036817774387802670949 61319403332697713000803)
                  ·
                    rfl

theorem cell22_537386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_537386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537386 prefixEnd_537386 := by exact prefixLift 537386
  have htrace : WordTrace (prefixWord ++ tailWord_537386) baseStart_537386 baseEnd_537386 := by
    simpa [prefixWord, tailWord_537386, baseEnd_537386] using wordTrace_append hprefix tailTrace_537386
  have hstable : (prefixWord ++ tailWord_537386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537386).length < 2 ^ (prefixWord ++ tailWord_537386).sum := by decide
  have hdescent : baseEnd_537386 < baseStart_537386 := by decide
  rcases family_descends (prefixWord ++ tailWord_537386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537442 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_537442 : Nat := 118140960795 + 537442 * 2 ^ 59
def prefixEnd_537442 : Nat := 4983230072969 + 3 ^ 40 * 537442 * 2
def baseEnd_537442 : Nat := 61325793314175886534079

theorem tailTrace_537442 : CollatzResearch.WordTrace tailWord_537442 prefixEnd_537442 61325793314175886534079 := by
  unfold tailWord_537442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900530029736724157777645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13068080079297931087407053 4900530029736724157777645)
  ·
    refine ⟨1837698761151271559166617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4900530029736724157777645 1837698761151271559166617)
    ·
      refine ⟨1378274070863453669374963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1837698761151271559166617 1378274070863453669374963)
      ·
        refine ⟨2067411106295180504062445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378274070863453669374963 2067411106295180504062445)
        ·
          refine ⟨775279164860692689023417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2067411106295180504062445 775279164860692689023417)
          ·
            refine ⟨581459373645519516767563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775279164860692689023417 581459373645519516767563)
            ·
              refine ⟨872189060468279275151345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581459373645519516767563 872189060468279275151345)
              ·
                refine ⟨654141795351209456363509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872189060468279275151345 654141795351209456363509)
                ·
                  refine ⟨61325793314175886534079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 654141795351209456363509 61325793314175886534079)
                  ·
                    rfl

theorem cell22_537442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_537442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537442 prefixEnd_537442 := by exact prefixLift 537442
  have htrace : WordTrace (prefixWord ++ tailWord_537442) baseStart_537442 baseEnd_537442 := by
    simpa [prefixWord, tailWord_537442, baseEnd_537442] using wordTrace_append hprefix tailTrace_537442
  have hstable : (prefixWord ++ tailWord_537442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537442).length < 2 ^ (prefixWord ++ tailWord_537442).sum := by decide
  have hdescent : baseEnd_537442 < baseStart_537442 := by decide
  rcases family_descends (prefixWord ++ tailWord_537442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537451 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_537451 : Nat := 118140960795 + 537451 * 2 ^ 59
def prefixEnd_537451 : Nat := 4983230072969 + 3 ^ 40 * 537451 * 2
def baseEnd_537451 : Nat := 183980460826454636127209

theorem tailTrace_537451 : CollatzResearch.WordTrace tailWord_537451 prefixEnd_537451 183980460826454636127209 := by
  unfold tailWord_537451
  simp only [CollatzResearch.WordTrace]
  refine ⟨19602448375914291168188207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13068298917276194112125471 19602448375914291168188207)
  ·
    refine ⟨29403672563871436752282311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19602448375914291168188207 29403672563871436752282311)
    ·
      refine ⟨44105508845807155128423467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29403672563871436752282311 44105508845807155128423467)
      ·
        refine ⟨66158263268710732692635201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44105508845807155128423467 66158263268710732692635201)
        ·
          refine ⟨49618697451533049519476401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66158263268710732692635201 49618697451533049519476401)
          ·
            refine ⟨37214023088649787139607301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49618697451533049519476401 37214023088649787139607301)
            ·
              refine ⟨6977629329121835088676369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37214023088649787139607301 6977629329121835088676369)
              ·
                refine ⟨5233221996841376316507277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6977629329121835088676369 5233221996841376316507277)
                ·
                  refine ⟨1962458248815516118690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5233221996841376316507277 1962458248815516118690229)
                  ·
                    refine ⟨183980460826454636127209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1962458248815516118690229 183980460826454636127209)
                    ·
                      rfl

theorem cell22_537451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_537451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537451 prefixEnd_537451 := by exact prefixLift 537451
  have htrace : WordTrace (prefixWord ++ tailWord_537451) baseStart_537451 baseEnd_537451 := by
    simpa [prefixWord, tailWord_537451, baseEnd_537451] using wordTrace_append hprefix tailTrace_537451
  have hstable : (prefixWord ++ tailWord_537451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537451).length < 2 ^ (prefixWord ++ tailWord_537451).sum := by decide
  have hdescent : baseEnd_537451 < baseStart_537451 := by decide
  rcases family_descends (prefixWord ++ tailWord_537451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537549 : List Nat := [1, 6, 3, 1, 2, 9]
def baseStart_537549 : Nat := 118140960795 + 537549 * 2 ^ 59
def prefixEnd_537549 : Nat := 4983230072969 + 3 ^ 40 * 537549 * 2
def baseEnd_537549 : Nat := 2271777879373025273789

theorem tailTrace_537549 : CollatzResearch.WordTrace tailWord_537549 prefixEnd_537549 2271777879373025273789 := by
  unfold tailWord_537549
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606022729559253905255701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13070681819706169270170467 19606022729559253905255701)
  ·
    refine ⟨919032315448090026808861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19606022729559253905255701 919032315448090026808861)
    ·
      refine ⟨344637118293033760053323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 919032315448090026808861 344637118293033760053323)
      ·
        refine ⟨516955677439550640079985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344637118293033760053323 516955677439550640079985)
        ·
          refine ⟨387716758079662980059989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516955677439550640079985 387716758079662980059989)
          ·
            refine ⟨2271777879373025273789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 387716758079662980059989 2271777879373025273789)
            ·
              rfl

theorem cell22_537549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 9].length) (baseStart_537549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537549 prefixEnd_537549 := by exact prefixLift 537549
  have htrace : WordTrace (prefixWord ++ tailWord_537549) baseStart_537549 baseEnd_537549 := by
    simpa [prefixWord, tailWord_537549, baseEnd_537549] using wordTrace_append hprefix tailTrace_537549
  have hstable : (prefixWord ++ tailWord_537549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537549).length < 2 ^ (prefixWord ++ tailWord_537549).sum := by decide
  have hdescent : baseEnd_537549 < baseStart_537549 := by decide
  rcases family_descends (prefixWord ++ tailWord_537549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537560 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_537560 : Nat := 118140960795 + 537560 * 2 ^ 59
def prefixEnd_537560 : Nat := 4983230072969 + 3 ^ 40 * 537560 * 2
def baseEnd_537560 : Nat := 61339257918004895050625

theorem tailTrace_537560 : CollatzResearch.WordTrace tailWord_537560 prefixEnd_537560 61339257918004895050625 := by
  unfold tailWord_537560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803211966259701391953067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13070949288346268522604089 9803211966259701391953067)
  ·
    refine ⟨14704817949389552087929601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9803211966259701391953067 14704817949389552087929601)
    ·
      refine ⟨11028613462042164065947201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14704817949389552087929601 11028613462042164065947201)
      ·
        refine ⟨8271460096531623049460401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11028613462042164065947201 8271460096531623049460401)
        ·
          refine ⟨6203595072398717287095301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8271460096531623049460401 6203595072398717287095301)
          ·
            refine ⟨1163174076074759491330369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6203595072398717287095301 1163174076074759491330369)
            ·
              refine ⟨872380557056069618497777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163174076074759491330369 872380557056069618497777)
              ·
                refine ⟨654285417792052213873333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872380557056069618497777 654285417792052213873333)
                ·
                  refine ⟨61339257918004895050625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 654285417792052213873333 61339257918004895050625)
                  ·
                    rfl

theorem cell22_537560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_537560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537560 prefixEnd_537560 := by exact prefixLift 537560
  have htrace : WordTrace (prefixWord ++ tailWord_537560) baseStart_537560 baseEnd_537560 := by
    simpa [prefixWord, tailWord_537560, baseEnd_537560] using wordTrace_append hprefix tailTrace_537560
  have hstable : (prefixWord ++ tailWord_537560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537560).length < 2 ^ (prefixWord ++ tailWord_537560).sum := by decide
  have hdescent : baseEnd_537560 < baseStart_537560 := by decide
  rcases family_descends (prefixWord ++ tailWord_537560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537575 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_537575 : Nat := 118140960795 + 537575 * 2 ^ 59
def prefixEnd_537575 : Nat := 4983230072969 + 3 ^ 40 * 537575 * 2
def baseEnd_537575 : Nat := 184022908560559646026829

theorem tailTrace_537575 : CollatzResearch.WordTrace tailWord_537575 prefixEnd_537575 184022908560559646026829 := by
  unfold tailWord_537575
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606971027465060345702179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13071314018310040230468119 19606971027465060345702179)
  ·
    refine ⟨29410456541197590518553269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19606971027465060345702179 29410456541197590518553269)
    ·
      refine ⟨2757230300737274111114369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29410456541197590518553269 2757230300737274111114369)
      ·
        refine ⟨2067922725552955583335777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2757230300737274111114369 2067922725552955583335777)
        ·
          refine ⟨1550942044164716687501833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067922725552955583335777 1550942044164716687501833)
          ·
            refine ⟨1163206533123537515626375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550942044164716687501833 1163206533123537515626375)
            ·
              refine ⟨1744809799685306273439563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163206533123537515626375 1744809799685306273439563)
              ·
                refine ⟨2617214699527959410159345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744809799685306273439563 2617214699527959410159345)
                ·
                  refine ⟨1962911024645969557619509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2617214699527959410159345 1962911024645969557619509)
                  ·
                    refine ⟨184022908560559646026829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1962911024645969557619509 184022908560559646026829)
                    ·
                      rfl

theorem cell22_537575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_537575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537575 prefixEnd_537575 := by exact prefixLift 537575
  have htrace : WordTrace (prefixWord ++ tailWord_537575) baseStart_537575 baseEnd_537575 := by
    simpa [prefixWord, tailWord_537575, baseEnd_537575] using wordTrace_append hprefix tailTrace_537575
  have hstable : (prefixWord ++ tailWord_537575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537575).length < 2 ^ (prefixWord ++ tailWord_537575).sum := by decide
  have hdescent : baseEnd_537575 < baseStart_537575 := by decide
  rcases family_descends (prefixWord ++ tailWord_537575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537648 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_537648 : Nat := 118140960795 + 537648 * 2 ^ 59
def prefixEnd_537648 : Nat := 4983230072969 + 3 ^ 40 * 537648 * 2
def baseEnd_537648 : Nat := 184047897952411788951605

theorem tailTrace_537648 : CollatzResearch.WordTrace tailWord_537648 prefixEnd_537648 184047897952411788951605 := by
  unfold tailWord_537648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804816778100296906554799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13073089037467062542073065 9804816778100296906554799)
  ·
    refine ⟨14707225167150445359832199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804816778100296906554799 14707225167150445359832199)
    ·
      refine ⟨22060837750725668039748299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14707225167150445359832199 22060837750725668039748299)
      ·
        refine ⟨33091256626088502059622449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22060837750725668039748299 33091256626088502059622449)
        ·
          refine ⟨24818442469566376544716837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33091256626088502059622449 24818442469566376544716837)
          ·
            refine ⟨4653457963043695602134407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24818442469566376544716837 4653457963043695602134407)
            ·
              refine ⟨6980186944565543403201611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653457963043695602134407 6980186944565543403201611)
              ·
                refine ⟨10470280416848315104802417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980186944565543403201611 10470280416848315104802417)
                ·
                  refine ⟨7852710312636236328601813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470280416848315104802417 7852710312636236328601813)
                  ·
                    refine ⟨184047897952411788951605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7852710312636236328601813 184047897952411788951605)
                    ·
                      rfl

theorem cell22_537648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_537648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537648 prefixEnd_537648 := by exact prefixLift 537648
  have htrace : WordTrace (prefixWord ++ tailWord_537648) baseStart_537648 baseEnd_537648 := by
    simpa [prefixWord, tailWord_537648, baseEnd_537648] using wordTrace_append hprefix tailTrace_537648
  have hstable : (prefixWord ++ tailWord_537648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537648).length < 2 ^ (prefixWord ++ tailWord_537648).sum := by decide
  have hdescent : baseEnd_537648 < baseStart_537648 := by decide
  rcases family_descends (prefixWord ++ tailWord_537648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537652 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_537652 : Nat := 118140960795 + 537652 * 2 ^ 59
def prefixEnd_537652 : Nat := 4983230072969 + 3 ^ 40 * 537652 * 2
def baseEnd_537652 : Nat := 184049267234157111851593

theorem tailTrace_537652 : CollatzResearch.WordTrace tailWord_537652 prefixEnd_537652 184049267234157111851593 := by
  unfold tailWord_537652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804889724093051248127605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13073186298790734997503473 9804889724093051248127605)
  ·
    refine ⟨919208411633723554511963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9804889724093051248127605 919208411633723554511963)
    ·
      refine ⟨1378812617450585331767945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919208411633723554511963 1378812617450585331767945)
      ·
        refine ⟨1034109463087938998825959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378812617450585331767945 1034109463087938998825959)
        ·
          refine ⟨1551164194631908498238939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034109463087938998825959 1551164194631908498238939)
          ·
            refine ⟨2326746291947862747358409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551164194631908498238939 2326746291947862747358409)
            ·
              refine ⟨1745059718960897060518807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2326746291947862747358409 1745059718960897060518807)
              ·
                refine ⟨2617589578441345590778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1745059718960897060518807 2617589578441345590778211)
                ·
                  refine ⟨3926384367662018386167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617589578441345590778211 3926384367662018386167317)
                  ·
                    refine ⟨184049267234157111851593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3926384367662018386167317 184049267234157111851593)
                    ·
                      rfl

theorem cell22_537652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_537652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537652 prefixEnd_537652 := by exact prefixLift 537652
  have htrace : WordTrace (prefixWord ++ tailWord_537652) baseStart_537652 baseEnd_537652 := by
    simpa [prefixWord, tailWord_537652, baseEnd_537652] using wordTrace_append hprefix tailTrace_537652
  have hstable : (prefixWord ++ tailWord_537652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537652).length < 2 ^ (prefixWord ++ tailWord_537652).sum := by decide
  have hdescent : baseEnd_537652 < baseStart_537652 := by decide
  rcases family_descends (prefixWord ++ tailWord_537652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537663 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_537663 : Nat := 118140960795 + 537663 * 2 ^ 59
def prefixEnd_537663 : Nat := 4983230072969 + 3 ^ 40 * 537663 * 2
def baseEnd_537663 : Nat := 184053032758956749826559

theorem tailTrace_537663 : CollatzResearch.WordTrace tailWord_537663 prefixEnd_537663 184053032758956749826559 := by
  unfold tailWord_537663
  simp only [CollatzResearch.WordTrace]
  refine ⟨19610180651146251374905643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13073453767430834249937095 19610180651146251374905643)
  ·
    refine ⟨29415270976719377062358465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19610180651146251374905643 29415270976719377062358465)
    ·
      refine ⟨22061453232539532796768849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29415270976719377062358465 22061453232539532796768849)
      ·
        refine ⟨16546089924404649597576637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22061453232539532796768849 16546089924404649597576637)
        ·
          refine ⟨6204783721651743599091239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16546089924404649597576637 6204783721651743599091239)
          ·
            refine ⟨9307175582477615398636859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204783721651743599091239 9307175582477615398636859)
            ·
              refine ⟨13960763373716423097955289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307175582477615398636859 13960763373716423097955289)
              ·
                refine ⟨10470572530287317323466467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13960763373716423097955289 10470572530287317323466467)
                ·
                  refine ⟨15705858795430975985199701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10470572530287317323466467 15705858795430975985199701)
                  ·
                    refine ⟨184053032758956749826559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15705858795430975985199701 184053032758956749826559)
                    ·
                      rfl

theorem cell22_537663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_537663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537663 prefixEnd_537663 := by exact prefixLift 537663
  have htrace : WordTrace (prefixWord ++ tailWord_537663) baseStart_537663 baseEnd_537663 := by
    simpa [prefixWord, tailWord_537663, baseEnd_537663] using wordTrace_append hprefix tailTrace_537663
  have hstable : (prefixWord ++ tailWord_537663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537663).length < 2 ^ (prefixWord ++ tailWord_537663).sum := by decide
  have hdescent : baseEnd_537663 < baseStart_537663 := by decide
  rcases family_descends (prefixWord ++ tailWord_537663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537695 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 5]
def baseStart_537695 : Nat := 118140960795 + 537695 * 2 ^ 59
def prefixEnd_537695 : Nat := 4983230072969 + 3 ^ 40 * 537695 * 2
def baseEnd_537695 : Nat := 61354662337639777675487

theorem tailTrace_537695 : CollatzResearch.WordTrace tailWord_537695 prefixEnd_537695 61354662337639777675487 := by
  unfold tailWord_537695
  simp only [CollatzResearch.WordTrace]
  refine ⟨19611347787030320840070539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13074231858020213893380359 19611347787030320840070539)
  ·
    refine ⟨29417021680545481260105809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19611347787030320840070539 29417021680545481260105809)
    ·
      refine ⟨22062766260409110945079357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29417021680545481260105809 22062766260409110945079357)
      ·
        refine ⟨8273537347653416604404759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22062766260409110945079357 8273537347653416604404759)
        ·
          refine ⟨12410306021480124906607139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8273537347653416604404759 12410306021480124906607139)
          ·
            refine ⟨18615459032220187359910709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410306021480124906607139 18615459032220187359910709)
            ·
              refine ⟨1745199284270642564991629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18615459032220187359910709 1745199284270642564991629)
              ·
                refine ⟨654449731601490961871861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1745199284270642564991629 654449731601490961871861)
                ·
                  refine ⟨61354662337639777675487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 654449731601490961871861 61354662337639777675487)
                  ·
                    rfl

theorem cell22_537695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 5].length) (baseStart_537695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537695 prefixEnd_537695 := by exact prefixLift 537695
  have htrace : WordTrace (prefixWord ++ tailWord_537695) baseStart_537695 baseEnd_537695 := by
    simpa [prefixWord, tailWord_537695, baseEnd_537695] using wordTrace_append hprefix tailTrace_537695
  have hstable : (prefixWord ++ tailWord_537695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537695).length < 2 ^ (prefixWord ++ tailWord_537695).sum := by decide
  have hdescent : baseEnd_537695 < baseStart_537695 := by decide
  rcases family_descends (prefixWord ++ tailWord_537695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537733 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_537733 : Nat := 118140960795 + 537733 * 2 ^ 59
def prefixEnd_537733 : Nat := 4983230072969 + 3 ^ 40 * 537733 * 2
def baseEnd_537733 : Nat := 184076995189499900576345

theorem tailTrace_537733 : CollatzResearch.WordTrace tailWord_537733 prefixEnd_537733 184076995189499900576345 := by
  unfold tailWord_537733
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612733760892653329953853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13075155840595102219969235 19612733760892653329953853)
  ·
    refine ⟨7354775160334744998732695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19612733760892653329953853 7354775160334744998732695)
    ·
      refine ⟨11032162740502117498099043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354775160334744998732695 11032162740502117498099043)
      ·
        refine ⟨16548244110753176247148565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11032162740502117498099043 16548244110753176247148565)
        ·
          refine ⟨775698942691555136585089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16548244110753176247148565 775698942691555136585089)
          ·
            refine ⟨581774207018666352438817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775698942691555136585089 581774207018666352438817)
            ·
              refine ⟨436330655263999764329113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581774207018666352438817 436330655263999764329113)
              ·
                refine ⟨327247991447999823246835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436330655263999764329113 327247991447999823246835)
                ·
                  refine ⟨490871987171999734870253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327247991447999823246835 490871987171999734870253)
                  ·
                    refine ⟨184076995189499900576345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490871987171999734870253 184076995189499900576345)
                    ·
                      rfl

theorem cell22_537733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_537733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537733 prefixEnd_537733 := by exact prefixLift 537733
  have htrace : WordTrace (prefixWord ++ tailWord_537733) baseStart_537733 baseEnd_537733 := by
    simpa [prefixWord, tailWord_537733, baseEnd_537733] using wordTrace_append hprefix tailTrace_537733
  have hstable : (prefixWord ++ tailWord_537733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537733).length < 2 ^ (prefixWord ++ tailWord_537733).sum := by decide
  have hdescent : baseEnd_537733 < baseStart_537733 := by decide
  rcases family_descends (prefixWord ++ tailWord_537733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537742 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_537742 : Nat := 118140960795 + 537742 * 2 ^ 59
def prefixEnd_537742 : Nat := 4983230072969 + 3 ^ 40 * 537742 * 2
def baseEnd_537742 : Nat := 184080076073426877101317

theorem tailTrace_537742 : CollatzResearch.WordTrace tailWord_537742 prefixEnd_537742 184080076073426877101317 := by
  unfold tailWord_537742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451632752232505983378935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13075374678573365244687653 2451632752232505983378935)
  ·
    refine ⟨3677449128348758975068403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451632752232505983378935 3677449128348758975068403)
    ·
      refine ⟨5516173692523138462602605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677449128348758975068403 5516173692523138462602605)
      ·
        refine ⟨2068565134696176923475977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5516173692523138462602605 2068565134696176923475977)
        ·
          refine ⟨1551423851022132692606983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068565134696176923475977 1551423851022132692606983)
          ·
            refine ⟨2327135776533199038910475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551423851022132692606983 2327135776533199038910475)
            ·
              refine ⟨3490703664799798558365713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327135776533199038910475 3490703664799798558365713)
              ·
                refine ⟨2618027748599848918774285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490703664799798558365713 2618027748599848918774285)
                ·
                  refine ⟨981760405724943344540357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2618027748599848918774285 981760405724943344540357)
                  ·
                    refine ⟨184080076073426877101317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 981760405724943344540357 184080076073426877101317)
                    ·
                      rfl

theorem cell22_537742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_537742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537742 prefixEnd_537742 := by exact prefixLift 537742
  have htrace : WordTrace (prefixWord ++ tailWord_537742) baseStart_537742 baseEnd_537742 := by
    simpa [prefixWord, tailWord_537742, baseEnd_537742] using wordTrace_append hprefix tailTrace_537742
  have hstable : (prefixWord ++ tailWord_537742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537742).length < 2 ^ (prefixWord ++ tailWord_537742).sum := by decide
  have hdescent : baseEnd_537742 < baseStart_537742 := by decide
  rcases family_descends (prefixWord ++ tailWord_537742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537785 : List Nat := [1, 2, 1, 4, 1, 4, 9]
def baseStart_537785 : Nat := 118140960795 + 537785 * 2 ^ 59
def prefixEnd_537785 : Nat := 4983230072969 + 3 ^ 40 * 537785 * 2
def baseEnd_537785 : Nat := 6818325772303299936155

theorem tailTrace_537785 : CollatzResearch.WordTrace tailWord_537785 prefixEnd_537785 6818325772303299936155 := by
  unfold tailWord_537785
  simp only [CollatzResearch.WordTrace]
  refine ⟨19614630356704266210846809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13076420237802844140564539 19614630356704266210846809)
  ·
    refine ⟨14710972767528199658135107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19614630356704266210846809 14710972767528199658135107)
    ·
      refine ⟨22066459151292299487202661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14710972767528199658135107 22066459151292299487202661)
      ·
        refine ⟨4137461090867306153850499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22066459151292299487202661 4137461090867306153850499)
        ·
          refine ⟨6206191636300959230775749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137461090867306153850499 6206191636300959230775749)
          ·
            refine ⟨1163660931806429855770453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6206191636300959230775749 1163660931806429855770453)
            ·
              refine ⟨6818325772303299936155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1163660931806429855770453 6818325772303299936155)
              ·
                rfl

theorem cell22_537785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 9].length) (baseStart_537785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537785 prefixEnd_537785 := by exact prefixLift 537785
  have htrace : WordTrace (prefixWord ++ tailWord_537785) baseStart_537785 baseEnd_537785 := by
    simpa [prefixWord, tailWord_537785, baseEnd_537785] using wordTrace_append hprefix tailTrace_537785
  have hstable : (prefixWord ++ tailWord_537785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537785).length < 2 ^ (prefixWord ++ tailWord_537785).sum := by decide
  have hdescent : baseEnd_537785 < baseStart_537785 := by decide
  rcases family_descends (prefixWord ++ tailWord_537785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537789 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_537789 : Nat := 118140960795 + 537789 * 2 ^ 59
def prefixEnd_537789 : Nat := 4983230072969 + 3 ^ 40 * 537789 * 2
def baseEnd_537789 : Nat := 184096165133934421176173

theorem tailTrace_537789 : CollatzResearch.WordTrace tailWord_537789 prefixEnd_537789 184096165133934421176173 := by
  unfold tailWord_537789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19614776248689774893992421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13076517499126516595994947 19614776248689774893992421)
  ·
    refine ⟨3677770546629332792623579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19614776248689774893992421 3677770546629332792623579)
    ·
      refine ⟨5516655819943999188935369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677770546629332792623579 5516655819943999188935369)
      ·
        refine ⟨4137491864957999391701527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5516655819943999188935369 4137491864957999391701527)
        ·
          refine ⟨6206237797436999087552291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137491864957999391701527 6206237797436999087552291)
          ·
            refine ⟨9309356696155498631328437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206237797436999087552291 9309356696155498631328437)
            ·
              refine ⟨872752190264577996687041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9309356696155498631328437 872752190264577996687041)
              ·
                refine ⟨654564142698433497515281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872752190264577996687041 654564142698433497515281)
                ·
                  refine ⟨490923107023825123136461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 654564142698433497515281 490923107023825123136461)
                  ·
                    refine ⟨184096165133934421176173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490923107023825123136461 184096165133934421176173)
                    ·
                      rfl

theorem cell22_537789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_537789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537789 prefixEnd_537789 := by exact prefixLift 537789
  have htrace : WordTrace (prefixWord ++ tailWord_537789) baseStart_537789 baseEnd_537789 := by
    simpa [prefixWord, tailWord_537789, baseEnd_537789] using wordTrace_append hprefix tailTrace_537789
  have hstable : (prefixWord ++ tailWord_537789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537789).length < 2 ^ (prefixWord ++ tailWord_537789).sum := by decide
  have hdescent : baseEnd_537789 < baseStart_537789 := by decide
  rcases family_descends (prefixWord ++ tailWord_537789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537806 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_537806 : Nat := 118140960795 + 537806 * 2 ^ 59
def prefixEnd_537806 : Nat := 4983230072969 + 3 ^ 40 * 537806 * 2
def baseEnd_537806 : Nat := 184101984581352043501121

theorem tailTrace_537806 : CollatzResearch.WordTrace tailWord_537806 prefixEnd_537806 184101984581352043501121 := by
  unfold tailWord_537806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451924536203523349670159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13076930859752124531574181 2451924536203523349670159)
  ·
    refine ⟨3677886804305285024505239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451924536203523349670159 3677886804305285024505239)
    ·
      refine ⟨5516830206457927536757859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677886804305285024505239 5516830206457927536757859)
      ·
        refine ⟨8275245309686891305136789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516830206457927536757859 8275245309686891305136789)
        ·
          refine ⟨387902123891573029928287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8275245309686891305136789 387902123891573029928287)
          ·
            refine ⟨581853185837359544892431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387902123891573029928287 581853185837359544892431)
            ·
              refine ⟨872779778756039317338647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581853185837359544892431 872779778756039317338647)
              ·
                refine ⟨1309169668134058976007971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872779778756039317338647 1309169668134058976007971)
                ·
                  refine ⟨1963754502201088464011957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1309169668134058976007971 1963754502201088464011957)
                  ·
                    refine ⟨184101984581352043501121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1963754502201088464011957 184101984581352043501121)
                    ·
                      rfl

theorem cell22_537806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_537806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537806 prefixEnd_537806 := by exact prefixLift 537806
  have htrace : WordTrace (prefixWord ++ tailWord_537806) baseStart_537806 baseEnd_537806 := by
    simpa [prefixWord, tailWord_537806, baseEnd_537806] using wordTrace_append hprefix tailTrace_537806
  have hstable : (prefixWord ++ tailWord_537806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537806).length < 2 ^ (prefixWord ++ tailWord_537806).sum := by decide
  have hdescent : baseEnd_537806 < baseStart_537806 := by decide
  rcases family_descends (prefixWord ++ tailWord_537806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537815 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_537815 : Nat := 118140960795 + 537815 * 2 ^ 59
def prefixEnd_537815 : Nat := 4983230072969 + 3 ^ 40 * 537815 * 2
def baseEnd_537815 : Nat := 184105065465279020026093

theorem tailTrace_537815 : CollatzResearch.WordTrace tailWord_537815 prefixEnd_537815 184105065465279020026093 := by
  unfold tailWord_537815
  simp only [CollatzResearch.WordTrace]
  refine ⟨19615724546595581334438899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13077149697730387556292599 19615724546595581334438899)
  ·
    refine ⟨29423586819893372001658349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19615724546595581334438899 29423586819893372001658349)
    ·
      refine ⟨11033845057460014500621881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29423586819893372001658349 11033845057460014500621881)
      ·
        refine ⟨8275383793095010875466411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11033845057460014500621881 8275383793095010875466411)
        ·
          refine ⟨12413075689642516313199617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8275383793095010875466411 12413075689642516313199617)
          ·
            refine ⟨9309806767231887234899713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12413075689642516313199617 9309806767231887234899713)
            ·
              refine ⟨6982355075423915426174785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9309806767231887234899713 6982355075423915426174785)
              ·
                refine ⟨5236766306567936569631089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6982355075423915426174785 5236766306567936569631089)
                ·
                  refine ⟨3927574729925952427223317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5236766306567936569631089 3927574729925952427223317)
                  ·
                    refine ⟨184105065465279020026093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3927574729925952427223317 184105065465279020026093)
                    ·
                      rfl

theorem cell22_537815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_537815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_537815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_537815 prefixEnd_537815 := by exact prefixLift 537815
  have htrace : WordTrace (prefixWord ++ tailWord_537815) baseStart_537815 baseEnd_537815 := by
    simpa [prefixWord, tailWord_537815, baseEnd_537815] using wordTrace_append hprefix tailTrace_537815
  have hstable : (prefixWord ++ tailWord_537815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537815).length < 2 ^ (prefixWord ++ tailWord_537815).sum := by decide
  have hdescent : baseEnd_537815 < baseStart_537815 := by decide
  rcases family_descends (prefixWord ++ tailWord_537815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
