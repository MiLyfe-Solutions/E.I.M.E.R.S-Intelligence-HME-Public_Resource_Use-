import V185TrunkScan22Chunk463

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4137000 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_4137000 : Nat := 118140960795 + 4137000 * 2 ^ 59
def prefixEnd_4137000 : Nat := 4983230072969 + 3 ^ 40 * 4137000 * 2
def baseEnd_4137000 : Nat := 472059881700093156038731

theorem tailTrace_4137000 : CollatzResearch.WordTrace tailWord_4137000 prefixEnd_4137000 472059881700093156038731 := by
  unfold tailWord_4137000
  simp only [CollatzResearch.WordTrace]
  refine ⟨75444393006181509097160227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100592524008242012129546969 75444393006181509097160227)
  ·
    refine ⟨113166589509272263645740341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75444393006181509097160227 113166589509272263645740341)
    ·
      refine ⟨10609367766494274716788157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113166589509272263645740341 10609367766494274716788157)
      ·
        refine ⟨3978512912435353018795559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10609367766494274716788157 3978512912435353018795559)
        ·
          refine ⟨5967769368653029528193339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978512912435353018795559 5967769368653029528193339)
          ·
            refine ⟨8951654052979544292290009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967769368653029528193339 8951654052979544292290009)
            ·
              refine ⟨6713740539734658219217507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8951654052979544292290009 6713740539734658219217507)
              ·
                refine ⟨10070610809601987328826261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713740539734658219217507 10070610809601987328826261)
                ·
                  refine ⟨472059881700093156038731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10070610809601987328826261 472059881700093156038731)
                  ·
                    rfl

theorem cell22_4137000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_4137000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137000 prefixEnd_4137000 := by exact prefixLift 4137000
  have htrace : WordTrace (prefixWord ++ tailWord_4137000) baseStart_4137000 baseEnd_4137000 := by
    simpa [prefixWord, tailWord_4137000, baseEnd_4137000] using wordTrace_append hprefix tailTrace_4137000
  have hstable : (prefixWord ++ tailWord_4137000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137000).length < 2 ^ (prefixWord ++ tailWord_4137000).sum := by decide
  have hdescent : baseEnd_4137000 < baseStart_4137000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137030 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4137030 : Nat := 118140960795 + 4137030 * 2 ^ 59
def prefixEnd_4137030 : Nat := 4983230072969 + 3 ^ 40 * 4137030 * 2
def baseEnd_4137030 : Nat := 1416189914713369389866101

theorem tailTrace_4137030 : CollatzResearch.WordTrace tailWord_4137030 prefixEnd_4137030 1416189914713369389866101 := by
  unfold tailWord_4137030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715308756320447916184767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100593253468169555545275029 4715308756320447916184767)
  ·
    refine ⟨7072963134480671874277151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715308756320447916184767 7072963134480671874277151)
    ·
      refine ⟨10609444701721007811415727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072963134480671874277151 10609444701721007811415727)
      ·
        refine ⟨15914167052581511717123591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609444701721007811415727 15914167052581511717123591)
        ·
          refine ⟨23871250578872267575685387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15914167052581511717123591 23871250578872267575685387)
          ·
            refine ⟨35806875868308401363528081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23871250578872267575685387 35806875868308401363528081)
            ·
              refine ⟨26855156901231301022646061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35806875868308401363528081 26855156901231301022646061)
              ·
                refine ⟨10070683837961737883492273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26855156901231301022646061 10070683837961737883492273)
                ·
                  refine ⟨7553012878471303412619205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10070683837961737883492273 7553012878471303412619205)
                  ·
                    refine ⟨1416189914713369389866101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553012878471303412619205 1416189914713369389866101)
                    ·
                      rfl

theorem cell22_4137030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4137030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137030 prefixEnd_4137030 := by exact prefixLift 4137030
  have htrace : WordTrace (prefixWord ++ tailWord_4137030) baseStart_4137030 baseEnd_4137030 := by
    simpa [prefixWord, tailWord_4137030, baseEnd_4137030] using wordTrace_append hprefix tailTrace_4137030
  have hstable : (prefixWord ++ tailWord_4137030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137030).length < 2 ^ (prefixWord ++ tailWord_4137030).sum := by decide
  have hdescent : baseEnd_4137030 < baseStart_4137030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137056 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_4137056 : Nat := 118140960795 + 4137056 * 2 ^ 59
def prefixEnd_4137056 : Nat := 4983230072969 + 3 ^ 40 * 4137056 * 2
def baseEnd_4137056 : Nat := 472066271681571329572007

theorem tailTrace_4137056 : CollatzResearch.WordTrace tailWord_4137056 prefixEnd_4137056 472066271681571329572007 := by
  unfold tailWord_4137056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75445414250080069879179511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100593885666773426505572681 75445414250080069879179511)
  ·
    refine ⟨113168121375120104818769267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75445414250080069879179511 113168121375120104818769267)
    ·
      refine ⟨169752182062680157228153901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113168121375120104818769267 169752182062680157228153901)
      ·
        refine ⟨63657068273505058960557713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169752182062680157228153901 63657068273505058960557713)
        ·
          refine ⟨47742801205128794220418285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63657068273505058960557713 47742801205128794220418285)
          ·
            refine ⟨17903550451923297832656857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47742801205128794220418285 17903550451923297832656857)
            ·
              refine ⟨13427662838942473374492643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17903550451923297832656857 13427662838942473374492643)
              ·
                refine ⟨20141494258413710061738965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427662838942473374492643 20141494258413710061738965)
                ·
                  refine ⟨472066271681571329572007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20141494258413710061738965 472066271681571329572007)
                  ·
                    rfl

theorem cell22_4137056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_4137056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137056 prefixEnd_4137056 := by exact prefixLift 4137056
  have htrace : WordTrace (prefixWord ++ tailWord_4137056) baseStart_4137056 baseEnd_4137056 := by
    simpa [prefixWord, tailWord_4137056, baseEnd_4137056] using wordTrace_append hprefix tailTrace_4137056
  have hstable : (prefixWord ++ tailWord_4137056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137056).length < 2 ^ (prefixWord ++ tailWord_4137056).sum := by decide
  have hdescent : baseEnd_4137056 < baseStart_4137056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137060 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_4137060 : Nat := 118140960795 + 4137060 * 2 ^ 59
def prefixEnd_4137060 : Nat := 4983230072969 + 3 ^ 40 * 4137060 * 2
def baseEnd_4137060 : Nat := 1416200184326459311616009

theorem tailTrace_4137060 : CollatzResearch.WordTrace tailWord_4137060 prefixEnd_4137060 1416200184326459311616009 := by
  unfold tailWord_4137060
  simp only [CollatzResearch.WordTrace]
  refine ⟨75445487196072824220752317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100593982928097098961003089 75445487196072824220752317)
  ·
    refine ⟨28292057698527309082782119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75445487196072824220752317 28292057698527309082782119)
    ·
      refine ⟨42438086547790963624173179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28292057698527309082782119 42438086547790963624173179)
      ·
        refine ⟨63657129821686445436259769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42438086547790963624173179 63657129821686445436259769)
        ·
          refine ⟨47742847366264834077194827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63657129821686445436259769 47742847366264834077194827)
          ·
            refine ⟨71614271049397251115792241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47742847366264834077194827 71614271049397251115792241)
            ·
              refine ⟨53710703287047938336844181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71614271049397251115792241 53710703287047938336844181)
              ·
                refine ⟨2517689216580372109539571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53710703287047938336844181 2517689216580372109539571)
                ·
                  refine ⟨3776533824870558164309357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517689216580372109539571 3776533824870558164309357)
                  ·
                    refine ⟨1416200184326459311616009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776533824870558164309357 1416200184326459311616009)
                    ·
                      rfl

theorem cell22_4137060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_4137060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137060 prefixEnd_4137060 := by exact prefixLift 4137060
  have htrace : WordTrace (prefixWord ++ tailWord_4137060) baseStart_4137060 baseEnd_4137060 := by
    simpa [prefixWord, tailWord_4137060, baseEnd_4137060] using wordTrace_append hprefix tailTrace_4137060
  have hstable : (prefixWord ++ tailWord_4137060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137060).length < 2 ^ (prefixWord ++ tailWord_4137060).sum := by decide
  have hdescent : baseEnd_4137060 < baseStart_4137060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137111 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 1, 3]
def baseStart_4137111 : Nat := 118140960795 + 4137111 * 2 ^ 59
def prefixEnd_4137111 : Nat := 4983230072969 + 3 ^ 40 * 4137111 * 2
def baseEnd_4137111 : Nat := 1416217642668712178590853

theorem tailTrace_4137111 : CollatzResearch.WordTrace tailWord_4137111 prefixEnd_4137111 1416217642668712178590853 := by
  unfold tailWord_4137111
  simp only [CollatzResearch.WordTrace]
  refine ⟨150892834514960884151611187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100595223009973922767740791 150892834514960884151611187)
  ·
    refine ⟨226339251772441326227416781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150892834514960884151611187 226339251772441326227416781)
    ·
      refine ⟨84877219414665497335281293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226339251772441326227416781 84877219414665497335281293)
      ·
        refine ⟨31828957280499561500730485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84877219414665497335281293 31828957280499561500730485)
        ·
          refine ⟨2983964745046833890693483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31828957280499561500730485 2983964745046833890693483)
          ·
            refine ⟨4475947117570250836040225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983964745046833890693483 4475947117570250836040225)
            ·
              refine ⟨3356960338177688127030169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475947117570250836040225 3356960338177688127030169)
              ·
                refine ⟨2517720253633266095272627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356960338177688127030169 2517720253633266095272627)
                ·
                  refine ⟨3776580380449899142908941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517720253633266095272627 3776580380449899142908941)
                  ·
                    refine ⟨1416217642668712178590853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776580380449899142908941 1416217642668712178590853)
                    ·
                      rfl

theorem cell22_4137111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_4137111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137111 prefixEnd_4137111 := by exact prefixLift 4137111
  have htrace : WordTrace (prefixWord ++ tailWord_4137111) baseStart_4137111 baseEnd_4137111 := by
    simpa [prefixWord, tailWord_4137111, baseEnd_4137111] using wordTrace_append hprefix tailTrace_4137111
  have hstable : (prefixWord ++ tailWord_4137111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137111).length < 2 ^ (prefixWord ++ tailWord_4137111).sum := by decide
  have hdescent : baseEnd_4137111 < baseStart_4137111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137146 : List Nat := [3, 1, 1, 1, 2, 2, 2, 10]
def baseStart_4137146 : Nat := 118140960795 + 4137146 * 2 ^ 59
def prefixEnd_4137146 : Nat := 4983230072969 + 3 ^ 40 * 4137146 * 2
def baseEnd_4137146 : Nat := 157358847098220417107305

theorem tailTrace_4137146 : CollatzResearch.WordTrace tailWord_4137146 prefixEnd_4137146 157358847098220417107305 := by
  unfold tailWord_4137146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37723527767458521282283823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100596074046556056752756861 37723527767458521282283823)
  ·
    refine ⟨56585291651187781923425735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37723527767458521282283823 56585291651187781923425735)
    ·
      refine ⟨84877937476781672885138603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56585291651187781923425735 84877937476781672885138603)
      ·
        refine ⟨127316906215172509327707905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84877937476781672885138603 127316906215172509327707905)
        ·
          refine ⟨95487679661379381995780929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127316906215172509327707905 95487679661379381995780929)
          ·
            refine ⟨71615759746034536496835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95487679661379381995780929 71615759746034536496835697)
            ·
              refine ⟨53711819809525902372626773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71615759746034536496835697 53711819809525902372626773)
              ·
                refine ⟨157358847098220417107305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53711819809525902372626773 157358847098220417107305)
                ·
                  rfl

theorem cell22_4137146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_4137146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137146 prefixEnd_4137146 := by exact prefixLift 4137146
  have htrace : WordTrace (prefixWord ++ tailWord_4137146) baseStart_4137146 baseEnd_4137146 := by
    simpa [prefixWord, tailWord_4137146, baseEnd_4137146] using wordTrace_append hprefix tailTrace_4137146
  have hstable : (prefixWord ++ tailWord_4137146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137146).length < 2 ^ (prefixWord ++ tailWord_4137146).sum := by decide
  have hdescent : baseEnd_4137146 < baseStart_4137146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137154 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4137154 : Nat := 118140960795 + 4137154 * 2 ^ 59
def prefixEnd_4137154 : Nat := 4983230072969 + 3 ^ 40 * 4137154 * 2
def baseEnd_4137154 : Nat := 1416232362447474399765721

theorem tailTrace_4137154 : CollatzResearch.WordTrace tailWord_4137154 prefixEnd_4137154 1416232362447474399765721 := by
  unfold tailWord_4137154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37723600713451275623856629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100596268569203401663617677 37723600713451275623856629)
  ·
    refine ⟨3536587566886057089736559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37723600713451275623856629 3536587566886057089736559)
    ·
      refine ⟨5304881350329085634604839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536587566886057089736559 5304881350329085634604839)
      ·
        refine ⟨7957322025493628451907259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304881350329085634604839 7957322025493628451907259)
        ·
          refine ⟨11935983038240442677860889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957322025493628451907259 11935983038240442677860889)
          ·
            refine ⟨8951987278680332008395667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11935983038240442677860889 8951987278680332008395667)
            ·
              refine ⟨13427980918020498012593501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951987278680332008395667 13427980918020498012593501)
              ·
                refine ⟨5035492844257686754722563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13427980918020498012593501 5035492844257686754722563)
                ·
                  refine ⟨7553239266386530132083845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035492844257686754722563 7553239266386530132083845)
                  ·
                    refine ⟨1416232362447474399765721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553239266386530132083845 1416232362447474399765721)
                    ·
                      rfl

theorem cell22_4137154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4137154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137154 prefixEnd_4137154 := by exact prefixLift 4137154
  have htrace : WordTrace (prefixWord ++ tailWord_4137154) baseStart_4137154 baseEnd_4137154 := by
    simpa [prefixWord, tailWord_4137154, baseEnd_4137154] using wordTrace_append hprefix tailTrace_4137154
  have hstable : (prefixWord ++ tailWord_4137154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137154).length < 2 ^ (prefixWord ++ tailWord_4137154).sum := by decide
  have hdescent : baseEnd_4137154 < baseStart_4137154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137197 : List Nat := [1, 5, 1, 2, 3, 2, 2, 6]
def baseStart_4137197 : Nat := 118140960795 + 4137197 * 2 ^ 59
def prefixEnd_4137197 : Nat := 4983230072969 + 3 ^ 40 * 4137197 * 2
def baseEnd_4137197 : Nat := 157360786914026291215621

theorem tailTrace_4137197 : CollatzResearch.WordTrace tailWord_4137197 prefixEnd_4137197 157360786914026291215621 := by
  unfold tailWord_4137197
  simp only [CollatzResearch.WordTrace]
  refine ⟨150895971192649320839241845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100597314128432880559494563 150895971192649320839241845)
  ·
    refine ⟨14146497299310873828678923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150895971192649320839241845 14146497299310873828678923)
    ·
      refine ⟨21219745948966310743018385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14146497299310873828678923 21219745948966310743018385)
      ·
        refine ⟨15914809461724733057263789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21219745948966310743018385 15914809461724733057263789)
        ·
          refine ⟨5968053548146774896473921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15914809461724733057263789 5968053548146774896473921)
          ·
            refine ⟨4476040161110081172355441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5968053548146774896473921 4476040161110081172355441)
            ·
              refine ⟨3357030120832560879266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476040161110081172355441 3357030120832560879266581)
              ·
                refine ⟨157360786914026291215621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357030120832560879266581 157360786914026291215621)
                ·
                  rfl

theorem cell22_4137197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 6].length) (baseStart_4137197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137197 prefixEnd_4137197 := by exact prefixLift 4137197
  have htrace : WordTrace (prefixWord ++ tailWord_4137197) baseStart_4137197 baseEnd_4137197 := by
    simpa [prefixWord, tailWord_4137197, baseEnd_4137197] using wordTrace_append hprefix tailTrace_4137197
  have hstable : (prefixWord ++ tailWord_4137197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137197).length < 2 ^ (prefixWord ++ tailWord_4137197).sum := by decide
  have hdescent : baseEnd_4137197 < baseStart_4137197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137315 : List Nat := [1, 1, 1, 5, 2, 1, 5, 6]
def baseStart_4137315 : Nat := 118140960795 + 4137315 * 2 ^ 59
def prefixEnd_4137315 : Nat := 4983230072969 + 3 ^ 40 * 4137315 * 2
def baseEnd_4137315 : Nat := 157365275115302627387803

theorem tailTrace_4137315 : CollatzResearch.WordTrace tailWord_4137315 prefixEnd_4137315 157365275115302627387803 := by
  unfold tailWord_4137315
  simp only [CollatzResearch.WordTrace]
  refine ⟨150900275006221826992037399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600183337481217994691599 150900275006221826992037399)
  ·
    refine ⟨226350412509332740488056099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150900275006221826992037399 226350412509332740488056099)
    ·
      refine ⟨339525618763999110732084149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226350412509332740488056099 339525618763999110732084149)
      ·
        refine ⟨31830526759124916631132889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339525618763999110732084149 31830526759124916631132889)
        ·
          refine ⟨23872895069343687473349667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31830526759124916631132889 23872895069343687473349667)
          ·
            refine ⟨35809342604015531210024501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23872895069343687473349667 35809342604015531210024501)
            ·
              refine ⟨3357125869126456050939797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35809342604015531210024501 3357125869126456050939797)
              ·
                refine ⟨157365275115302627387803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357125869126456050939797 157365275115302627387803)
                ·
                  rfl

theorem cell22_4137315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 6].length) (baseStart_4137315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137315 prefixEnd_4137315 := by exact prefixLift 4137315
  have htrace : WordTrace (prefixWord ++ tailWord_4137315) baseStart_4137315 baseEnd_4137315 := by
    simpa [prefixWord, tailWord_4137315, baseEnd_4137315] using wordTrace_append hprefix tailTrace_4137315
  have hstable : (prefixWord ++ tailWord_4137315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137315).length < 2 ^ (prefixWord ++ tailWord_4137315).sum := by decide
  have hdescent : baseEnd_4137315 < baseStart_4137315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137317 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_4137317 : Nat := 118140960795 + 4137317 * 2 ^ 59
def prefixEnd_4137317 : Nat := 4983230072969 + 3 ^ 40 * 4137317 * 2
def baseEnd_4137317 : Nat := 1416288160678596307940221

theorem tailTrace_4137317 : CollatzResearch.WordTrace tailWord_4137317 prefixEnd_4137317 1416288160678596307940221 := by
  unfold tailWord_4137317
  simp only [CollatzResearch.WordTrace]
  refine ⟨150900347952214581333610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600231968143054222406803 150900347952214581333610205)
  ·
    refine ⟨56587630482080468000103827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150900347952214581333610205 56587630482080468000103827)
    ·
      refine ⟨84881445723120702000155741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56587630482080468000103827 84881445723120702000155741)
      ·
        refine ⟨31830542146170263250058403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84881445723120702000155741 31830542146170263250058403)
        ·
          refine ⟨47745813219255394875087605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31830542146170263250058403 47745813219255394875087605)
          ·
            refine ⟨4476169989305193269539463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47745813219255394875087605 4476169989305193269539463)
            ·
              refine ⟨6714254983957789904309195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476169989305193269539463 6714254983957789904309195)
              ·
                refine ⟨10071382475936684856463793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714254983957789904309195 10071382475936684856463793)
                ·
                  refine ⟨7553536856952513642347845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10071382475936684856463793 7553536856952513642347845)
                  ·
                    refine ⟨1416288160678596307940221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7553536856952513642347845 1416288160678596307940221)
                    ·
                      rfl

theorem cell22_4137317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_4137317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137317 prefixEnd_4137317 := by exact prefixLift 4137317
  have htrace : WordTrace (prefixWord ++ tailWord_4137317) baseStart_4137317 baseEnd_4137317 := by
    simpa [prefixWord, tailWord_4137317, baseEnd_4137317] using wordTrace_append hprefix tailTrace_4137317
  have hstable : (prefixWord ++ tailWord_4137317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137317).length < 2 ^ (prefixWord ++ tailWord_4137317).sum := by decide
  have hdescent : baseEnd_4137317 < baseStart_4137317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137343 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 7]
def baseStart_4137343 : Nat := 118140960795 + 4137343 * 2 ^ 59
def prefixEnd_4137343 : Nat := 4983230072969 + 3 ^ 40 * 4137343 * 2
def baseEnd_4137343 : Nat := 472099020336646968930047

theorem tailTrace_4137343 : CollatzResearch.WordTrace tailWord_4137343 prefixEnd_4137343 472099020336646968930047 := by
  unfold tailWord_4137343
  simp only [CollatzResearch.WordTrace]
  refine ⟨150901296250120387774056683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100600864166746925182704455 150901296250120387774056683)
  ·
    refine ⟨226351944375180581661085025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150901296250120387774056683 226351944375180581661085025)
    ·
      refine ⟨169763958281385436245813769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226351944375180581661085025 169763958281385436245813769)
      ·
        refine ⟨127322968711039077184360327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169763958281385436245813769 127322968711039077184360327)
        ·
          refine ⟨190984453066558615776540491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127322968711039077184360327 190984453066558615776540491)
          ·
            refine ⟨286476679599837923664810737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190984453066558615776540491 286476679599837923664810737)
            ·
              refine ⟨214857509699878442748608053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286476679599837923664810737 214857509699878442748608053)
              ·
                refine ⟨20142891534363604007682005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214857509699878442748608053 20142891534363604007682005)
                ·
                  refine ⟨472099020336646968930047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20142891534363604007682005 472099020336646968930047)
                  ·
                    rfl

theorem cell22_4137343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_4137343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137343 prefixEnd_4137343 := by exact prefixLift 4137343
  have htrace : WordTrace (prefixWord ++ tailWord_4137343) baseStart_4137343 baseEnd_4137343 := by
    simpa [prefixWord, tailWord_4137343, baseEnd_4137343] using wordTrace_append hprefix tailTrace_4137343
  have hstable : (prefixWord ++ tailWord_4137343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137343).length < 2 ^ (prefixWord ++ tailWord_4137343).sum := by decide
  have hdescent : baseEnd_4137343 < baseStart_4137343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137366 : List Nat := [5, 3, 1, 2, 1, 1, 1, 8]
def baseStart_4137366 : Nat := 118140960795 + 4137366 * 2 ^ 59
def prefixEnd_4137366 : Nat := 4983230072969 + 3 ^ 40 * 4137366 * 2
def baseEnd_4137366 : Nat := 157367214931108501496119

theorem tailTrace_4137366 : CollatzResearch.WordTrace tailWord_4137366 prefixEnd_4137366 157367214931108501496119 := by
  unfold tailWord_4137366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431383445564816418883997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100601423419358041801429301 9431383445564816418883997)
  ·
    refine ⟨3536768792086806157081499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9431383445564816418883997 3536768792086806157081499)
    ·
      refine ⟨5305153188130209235622249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536768792086806157081499 5305153188130209235622249)
      ·
        refine ⟨3978864891097656926716687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5305153188130209235622249 3978864891097656926716687)
        ·
          refine ⟨5968297336646485390075031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978864891097656926716687 5968297336646485390075031)
          ·
            refine ⟨8952446004969728085112547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968297336646485390075031 8952446004969728085112547)
            ·
              refine ⟨13428669007454592127668821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8952446004969728085112547 13428669007454592127668821)
              ·
                refine ⟨157367214931108501496119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13428669007454592127668821 157367214931108501496119)
                ·
                  rfl

theorem cell22_4137366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_4137366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137366 prefixEnd_4137366 := by exact prefixLift 4137366
  have htrace : WordTrace (prefixWord ++ tailWord_4137366) baseStart_4137366 baseEnd_4137366 := by
    simpa [prefixWord, tailWord_4137366, baseEnd_4137366] using wordTrace_append hprefix tailTrace_4137366
  have hstable : (prefixWord ++ tailWord_4137366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137366).length < 2 ^ (prefixWord ++ tailWord_4137366).sum := by decide
  have hdescent : baseEnd_4137366 < baseStart_4137366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137437 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4137437 : Nat := 118140960795 + 4137437 * 2 ^ 59
def prefixEnd_4137437 : Nat := 4983230072969 + 3 ^ 40 * 4137437 * 2
def baseEnd_4137437 : Nat := 1416329239130955994939853

theorem tailTrace_4137437 : CollatzResearch.WordTrace tailWord_4137437 prefixEnd_4137437 1416329239130955994939853 := by
  unfold tailWord_4137437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150904724711779841827978565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100603149807853227885319043 150904724711779841827978565)
  ·
    refine ⟨28294635883458720342745981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150904724711779841827978565 28294635883458720342745981)
    ·
      refine ⟨10610488456297020128529743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28294635883458720342745981 10610488456297020128529743)
      ·
        refine ⟨15915732684445530192794615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610488456297020128529743 15915732684445530192794615)
        ·
          refine ⟨23873599026668295289191923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15915732684445530192794615 23873599026668295289191923)
          ·
            refine ⟨35810398540002442933787885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23873599026668295289191923 35810398540002442933787885)
            ·
              refine ⟨13428899452500916100170457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35810398540002442933787885 13428899452500916100170457)
              ·
                refine ⟨10071674589375687075127843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13428899452500916100170457 10071674589375687075127843)
                ·
                  refine ⟨15107511884063530612691765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10071674589375687075127843 15107511884063530612691765)
                  ·
                    refine ⟨1416329239130955994939853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15107511884063530612691765 1416329239130955994939853)
                    ·
                      rfl

theorem cell22_4137437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4137437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137437 prefixEnd_4137437 := by exact prefixLift 4137437
  have htrace : WordTrace (prefixWord ++ tailWord_4137437) baseStart_4137437 baseEnd_4137437 := by
    simpa [prefixWord, tailWord_4137437, baseEnd_4137437] using wordTrace_append hprefix tailTrace_4137437
  have hstable : (prefixWord ++ tailWord_4137437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137437).length < 2 ^ (prefixWord ++ tailWord_4137437).sum := by decide
  have hdescent : baseEnd_4137437 < baseStart_4137437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137450 : List Nat := [3, 1, 3, 1, 3, 11]
def baseStart_4137450 : Nat := 118140960795 + 4137450 * 2 ^ 59
def prefixEnd_4137450 : Nat := 4983230072969 + 3 ^ 40 * 4137450 * 2
def baseEnd_4137450 : Nat := 17485601102427509806973

theorem tailTrace_4137450 : CollatzResearch.WordTrace tailWord_4137450 prefixEnd_4137450 17485601102427509806973 := by
  unfold tailWord_4137450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726299715183186262050451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100603465907155163365467869 37726299715183186262050451)
  ·
    refine ⟨56589449572774779393075677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37726299715183186262050451 56589449572774779393075677)
    ·
      refine ⟨21221043589790542272403379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56589449572774779393075677 21221043589790542272403379)
      ·
        refine ⟨31831565384685813408605069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21221043589790542272403379 31831565384685813408605069)
        ·
          refine ⟨11936837019257180028226901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31831565384685813408605069 11936837019257180028226901)
          ·
            refine ⟨17485601102427509806973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11936837019257180028226901 17485601102427509806973)
            ·
              rfl

theorem cell22_4137450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 11].length) (baseStart_4137450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137450 prefixEnd_4137450 := by exact prefixLift 4137450
  have htrace : WordTrace (prefixWord ++ tailWord_4137450) baseStart_4137450 baseEnd_4137450 := by
    simpa [prefixWord, tailWord_4137450, baseEnd_4137450] using wordTrace_append hprefix tailTrace_4137450
  have hstable : (prefixWord ++ tailWord_4137450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137450).length < 2 ^ (prefixWord ++ tailWord_4137450).sum := by decide
  have hdescent : baseEnd_4137450 < baseStart_4137450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137454 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4137454 : Nat := 118140960795 + 4137454 * 2 ^ 59
def prefixEnd_4137454 : Nat := 4983230072969 + 3 ^ 40 * 4137454 * 2
def baseEnd_4137454 : Nat := 1416335058578373617264801

theorem tailTrace_4137454 : CollatzResearch.WordTrace tailWord_4137454 prefixEnd_4137454 1416335058578373617264801 := by
  unfold tailWord_4137454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863168094089781716418427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100603563168478835820898277 18863168094089781716418427)
  ·
    refine ⟨28294752141134672574627641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863168094089781716418427 28294752141134672574627641)
    ·
      refine ⟨21221064105851004430970731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28294752141134672574627641 21221064105851004430970731)
      ·
        refine ⟨31831596158776506646456097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21221064105851004430970731 31831596158776506646456097)
        ·
          refine ⟨23873697119082379984842073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31831596158776506646456097 23873697119082379984842073)
          ·
            refine ⟨17905272839311784988631555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23873697119082379984842073 17905272839311784988631555)
            ·
              refine ⟨26857909258967677482947333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17905272839311784988631555 26857909258967677482947333)
              ·
                refine ⟨5035857986056439528052625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26857909258967677482947333 5035857986056439528052625)
                ·
                  refine ⟨3776893489542329646039469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5035857986056439528052625 3776893489542329646039469)
                  ·
                    refine ⟨1416335058578373617264801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776893489542329646039469 1416335058578373617264801)
                    ·
                      rfl

theorem cell22_4137454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4137454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137454 prefixEnd_4137454 := by exact prefixLift 4137454
  have htrace : WordTrace (prefixWord ++ tailWord_4137454) baseStart_4137454 baseEnd_4137454 := by
    simpa [prefixWord, tailWord_4137454, baseEnd_4137454] using wordTrace_append hprefix tailTrace_4137454
  have hstable : (prefixWord ++ tailWord_4137454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137454).length < 2 ^ (prefixWord ++ tailWord_4137454).sum := by decide
  have hdescent : baseEnd_4137454 < baseStart_4137454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137480 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4137480 : Nat := 118140960795 + 4137480 * 2 ^ 59
def prefixEnd_4137480 : Nat := 4983230072969 + 3 ^ 40 * 4137480 * 2
def baseEnd_4137480 : Nat := 1416343958909718216114721

theorem tailTrace_4137480 : CollatzResearch.WordTrace tailWord_4137480 prefixEnd_4137480 1416343958909718216114721 := by
  unfold tailWord_4137480
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453146525312030085896947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100604195367082706781195929 75453146525312030085896947)
  ·
    refine ⟨113179719787968045128845421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75453146525312030085896947 113179719787968045128845421)
    ·
      refine ⟨42442394920488016923317033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113179719787968045128845421 42442394920488016923317033)
      ·
        refine ⟨31831796190366012692487775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42442394920488016923317033 31831796190366012692487775)
        ·
          refine ⟨47747694285549019038731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31831796190366012692487775 47747694285549019038731663)
          ·
            refine ⟨71621541428323528558097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47747694285549019038731663 71621541428323528558097495)
            ·
              refine ⟨107432312142485292837146243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71621541428323528558097495 107432312142485292837146243)
              ·
                refine ⟨161148468213727939255719365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107432312142485292837146243 161148468213727939255719365)
                ·
                  refine ⟨30215337790073988610447381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161148468213727939255719365 30215337790073988610447381)
                  ·
                    refine ⟨1416343958909718216114721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30215337790073988610447381 1416343958909718216114721)
                    ·
                      rfl

theorem cell22_4137480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4137480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137480 prefixEnd_4137480 := by exact prefixLift 4137480
  have htrace : WordTrace (prefixWord ++ tailWord_4137480) baseStart_4137480 baseEnd_4137480 := by
    simpa [prefixWord, tailWord_4137480, baseEnd_4137480] using wordTrace_append hprefix tailTrace_4137480
  have hstable : (prefixWord ++ tailWord_4137480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137480).length < 2 ^ (prefixWord ++ tailWord_4137480).sum := by decide
  have hdescent : baseEnd_4137480 < baseStart_4137480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137529 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 5]
def baseStart_4137529 : Nat := 118140960795 + 4137529 * 2 ^ 59
def prefixEnd_4137529 : Nat := 4983230072969 + 3 ^ 40 * 4137529 * 2
def baseEnd_4137529 : Nat := 472120244203699473879857

theorem tailTrace_4137529 : CollatzResearch.WordTrace tailWord_4137529 prefixEnd_4137529 472120244203699473879857 := by
  unfold tailWord_4137529
  simp only [CollatzResearch.WordTrace]
  refine ⟨150908080227446541540327641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100605386818297694360218427 150908080227446541540327641)
  ·
    refine ⟨113181060170584906155245731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150908080227446541540327641 113181060170584906155245731)
    ·
      refine ⟨169771590255877359232868597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113181060170584906155245731 169771590255877359232868597)
      ·
        refine ⟨15916086586488502428081431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169771590255877359232868597 15916086586488502428081431)
        ·
          refine ⟨23874129879732753642122147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916086586488502428081431 23874129879732753642122147)
          ·
            refine ⟨35811194819599130463183221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23874129879732753642122147 35811194819599130463183221)
            ·
              refine ⟨3357299514337418480923427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35811194819599130463183221 3357299514337418480923427)
              ·
                refine ⟨5035949271506127721385141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357299514337418480923427 5035949271506127721385141)
                ·
                  refine ⟨472120244203699473879857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5035949271506127721385141 472120244203699473879857)
                  ·
                    rfl

theorem cell22_4137529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_4137529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137529 prefixEnd_4137529 := by exact prefixLift 4137529
  have htrace : WordTrace (prefixWord ++ tailWord_4137529) baseStart_4137529 baseEnd_4137529 := by
    simpa [prefixWord, tailWord_4137529, baseEnd_4137529] using wordTrace_append hprefix tailTrace_4137529
  have hstable : (prefixWord ++ tailWord_4137529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137529).length < 2 ^ (prefixWord ++ tailWord_4137529).sum := by decide
  have hdescent : baseEnd_4137529 < baseStart_4137529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137604 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4137604 : Nat := 118140960795 + 4137604 * 2 ^ 59
def prefixEnd_4137604 : Nat := 4983230072969 + 3 ^ 40 * 4137604 * 2
def baseEnd_4137604 : Nat := 1416386406643823226014341

theorem tailTrace_4137604 : CollatzResearch.WordTrace tailWord_4137604 prefixEnd_4137604 1416386406643823226014341 := by
  unfold tailWord_4137604
  simp only [CollatzResearch.WordTrace]
  refine ⟨75455407851087414674653933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100607210468116552899538577 75455407851087414674653933)
  ·
    refine ⟨28295777944157780502995225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75455407851087414674653933 28295777944157780502995225)
    ·
      refine ⟨21221833458118335377246419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28295777944157780502995225 21221833458118335377246419)
      ·
        refine ⟨31832750187177503065869629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21221833458118335377246419 31832750187177503065869629)
        ·
          refine ⟨11937281320191563649701111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31832750187177503065869629 11937281320191563649701111)
          ·
            refine ⟨17905921980287345474551667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11937281320191563649701111 17905921980287345474551667)
            ·
              refine ⟨26858882970431018211827501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17905921980287345474551667 26858882970431018211827501)
              ·
                refine ⟨10072081113911631829435313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26858882970431018211827501 10072081113911631829435313)
                ·
                  refine ⟨7554060835433723872076485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10072081113911631829435313 7554060835433723872076485)
                  ·
                    refine ⟨1416386406643823226014341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554060835433723872076485 1416386406643823226014341)
                    ·
                      rfl

theorem cell22_4137604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4137604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137604 prefixEnd_4137604 := by exact prefixLift 4137604
  have htrace : WordTrace (prefixWord ++ tailWord_4137604) baseStart_4137604 baseEnd_4137604 := by
    simpa [prefixWord, tailWord_4137604, baseEnd_4137604] using wordTrace_append hprefix tailTrace_4137604
  have hstable : (prefixWord ++ tailWord_4137604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137604).length < 2 ^ (prefixWord ++ tailWord_4137604).sum := by decide
  have hdescent : baseEnd_4137604 < baseStart_4137604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137668 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4137668 : Nat := 118140960795 + 4137668 * 2 ^ 59
def prefixEnd_4137668 : Nat := 4983230072969 + 3 ^ 40 * 4137668 * 2
def baseEnd_4137668 : Nat := 1416408315151748392414145

theorem tailTrace_4137668 : CollatzResearch.WordTrace tailWord_4137668 prefixEnd_4137668 1416408315151748392414145 := by
  unfold tailWord_4137668
  simp only [CollatzResearch.WordTrace]
  refine ⟨75456574986971484139818829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100608766649295312186425105 75456574986971484139818829)
  ·
    refine ⟨28296215620114306552432061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75456574986971484139818829 28296215620114306552432061)
    ·
      refine ⟨10611080857542864957162023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28296215620114306552432061 10611080857542864957162023)
      ·
        refine ⟨15916621286314297435743035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10611080857542864957162023 15916621286314297435743035)
        ·
          refine ⟨23874931929471446153614553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916621286314297435743035 23874931929471446153614553)
          ·
            refine ⟨17906198947103584615210915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23874931929471446153614553 17906198947103584615210915)
            ·
              refine ⟨26859298420655376922816373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17906198947103584615210915 26859298420655376922816373)
              ·
                refine ⟨2518059226936441586514035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26859298420655376922816373 2518059226936441586514035)
                ·
                  refine ⟨3777088840404662379771053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518059226936441586514035 3777088840404662379771053)
                  ·
                    refine ⟨1416408315151748392414145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777088840404662379771053 1416408315151748392414145)
                    ·
                      rfl

theorem cell22_4137668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4137668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137668 prefixEnd_4137668 := by exact prefixLift 4137668
  have htrace : WordTrace (prefixWord ++ tailWord_4137668) baseStart_4137668 baseEnd_4137668 := by
    simpa [prefixWord, tailWord_4137668, baseEnd_4137668] using wordTrace_append hprefix tailTrace_4137668
  have hstable : (prefixWord ++ tailWord_4137668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137668).length < 2 ^ (prefixWord ++ tailWord_4137668).sum := by decide
  have hdescent : baseEnd_4137668 < baseStart_4137668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137709 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4137709 : Nat := 118140960795 + 4137709 * 2 ^ 59
def prefixEnd_4137709 : Nat := 4983230072969 + 3 ^ 40 * 4137709 * 2
def baseEnd_4137709 : Nat := 472140783429879317379673

theorem tailTrace_4137709 : CollatzResearch.WordTrace tailWord_4137709 prefixEnd_4137709 472140783429879317379673 := by
  unfold tailWord_4137709
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914645366794432281880181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609763577862954854586787 150914645366794432281880181)
  ·
    refine ⟨14148248003136978026426267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150914645366794432281880181 14148248003136978026426267)
    ·
      refine ⟨21222372004705467039639401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14148248003136978026426267 21222372004705467039639401)
      ·
        refine ⟨15916779003529100279729551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21222372004705467039639401 15916779003529100279729551)
        ·
          refine ⟨23875168505293650419594327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15916779003529100279729551 23875168505293650419594327)
          ·
            refine ⟨35812752757940475629391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23875168505293650419594327 35812752757940475629391491)
            ·
              refine ⟨53719129136910713444087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35812752757940475629391491 53719129136910713444087237)
              ·
                refine ⟨10072336713170758770766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53719129136910713444087237 10072336713170758770766357)
                ·
                  refine ⟨472140783429879317379673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10072336713170758770766357 472140783429879317379673)
                  ·
                    rfl

theorem cell22_4137709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4137709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137709 prefixEnd_4137709 := by exact prefixLift 4137709
  have htrace : WordTrace (prefixWord ++ tailWord_4137709) baseStart_4137709 baseEnd_4137709 := by
    simpa [prefixWord, tailWord_4137709, baseEnd_4137709] using wordTrace_append hprefix tailTrace_4137709
  have hstable : (prefixWord ++ tailWord_4137709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137709).length < 2 ^ (prefixWord ++ tailWord_4137709).sum := by decide
  have hdescent : baseEnd_4137709 < baseStart_4137709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137711 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 1, 4]
def baseStart_4137711 : Nat := 118140960795 + 4137711 * 2 ^ 59
def prefixEnd_4137711 : Nat := 4983230072969 + 3 ^ 40 * 4137711 * 2
def baseEnd_4137711 : Nat := 1416423034930510613589013

theorem tailTrace_4137711 : CollatzResearch.WordTrace tailWord_4137711 prefixEnd_4137711 1416423034930510613589013 := by
  unfold tailWord_4137711
  simp only [CollatzResearch.WordTrace]
  refine ⟨150914718312787186623452987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100609812208524791082301991 150914718312787186623452987)
  ·
    refine ⟨226372077469180779935179481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150914718312787186623452987 226372077469180779935179481)
    ·
      refine ⟨169779058101885584951384611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226372077469180779935179481 169779058101885584951384611)
      ·
        refine ⟨254668587152828377427076917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169779058101885584951384611 254668587152828377427076917)
        ·
          refine ⟨23875180045577660383788461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254668587152828377427076917 23875180045577660383788461)
          ·
            refine ⟨8953192517091622643920673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23875180045577660383788461 8953192517091622643920673)
            ·
              refine ⟨6714894387818716982940505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953192517091622643920673 6714894387818716982940505)
              ·
                refine ⟨5036170790864037737205379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6714894387818716982940505 5036170790864037737205379)
                ·
                  refine ⟨7554256186296056605808069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036170790864037737205379 7554256186296056605808069)
                  ·
                    refine ⟨1416423034930510613589013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554256186296056605808069 1416423034930510613589013)
                    ·
                      rfl

theorem cell22_4137711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_4137711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137711 prefixEnd_4137711 := by exact prefixLift 4137711
  have htrace : WordTrace (prefixWord ++ tailWord_4137711) baseStart_4137711 baseEnd_4137711 := by
    simpa [prefixWord, tailWord_4137711, baseEnd_4137711] using wordTrace_append hprefix tailTrace_4137711
  have hstable : (prefixWord ++ tailWord_4137711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137711).length < 2 ^ (prefixWord ++ tailWord_4137711).sum := by decide
  have hdescent : baseEnd_4137711 < baseStart_4137711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137737 : List Nat := [1, 2, 1, 1, 3, 2, 12]
def baseStart_4137737 : Nat := 118140960795 + 4137737 * 2 ^ 59
def prefixEnd_4137737 : Nat := 4983230072969 + 3 ^ 40 * 4137737 * 2
def baseEnd_4137737 : Nat := 52460442046735378238479

theorem tailTrace_4137737 : CollatzResearch.WordTrace tailWord_4137737 prefixEnd_4137737 52460442046735378238479 := by
  unfold tailWord_4137737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150915666610692993063899465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100610444407128662042599643 150915666610692993063899465)
  ·
    refine ⟨113186749958019744797924599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150915666610692993063899465 113186749958019744797924599)
    ·
      refine ⟨169780124937029617196886899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113186749958019744797924599 169780124937029617196886899)
      ·
        refine ⟨254670187405544425795330349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169780124937029617196886899 254670187405544425795330349)
        ·
          refine ⟨95501320277079159673248881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254670187405544425795330349 95501320277079159673248881)
          ·
            refine ⟨71625990207809369754936661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95501320277079159673248881 71625990207809369754936661)
            ·
              refine ⟨52460442046735378238479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71625990207809369754936661 52460442046735378238479)
              ·
                rfl

theorem cell22_4137737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 12].length) (baseStart_4137737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137737 prefixEnd_4137737 := by exact prefixLift 4137737
  have htrace : WordTrace (prefixWord ++ tailWord_4137737) baseStart_4137737 baseEnd_4137737 := by
    simpa [prefixWord, tailWord_4137737, baseEnd_4137737] using wordTrace_append hprefix tailTrace_4137737
  have hstable : (prefixWord ++ tailWord_4137737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137737).length < 2 ^ (prefixWord ++ tailWord_4137737).sum := by decide
  have hdescent : baseEnd_4137737 < baseStart_4137737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137754 : List Nat := [3, 1, 1, 3, 2, 1, 4, 7]
def baseStart_4137754 : Nat := 118140960795 + 4137754 * 2 ^ 59
def prefixEnd_4137754 : Nat := 4983230072969 + 3 ^ 40 * 4137754 * 2
def baseEnd_4137754 : Nat := 157381972745474759418209

theorem tailTrace_4137754 : CollatzResearch.WordTrace tailWord_4137754 prefixEnd_4137754 157381972745474759418209 := by
  unfold tailWord_4137754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37729071662907851241817079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100610857767754269978178877 37729071662907851241817079)
  ·
    refine ⟨56593607494361776862725619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37729071662907851241817079 56593607494361776862725619)
    ·
      refine ⟨84890411241542665294088429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56593607494361776862725619 84890411241542665294088429)
      ·
        refine ⟨31833904215578499485283161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84890411241542665294088429 31833904215578499485283161)
        ·
          refine ⟨23875428161683874613962371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31833904215578499485283161 23875428161683874613962371)
          ·
            refine ⟨35813142242525811920943557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23875428161683874613962371 35813142242525811920943557)
            ·
              refine ⟨6714964170473589735176917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35813142242525811920943557 6714964170473589735176917)
              ·
                refine ⟨157381972745474759418209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6714964170473589735176917 157381972745474759418209)
                ·
                  rfl

theorem cell22_4137754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_4137754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137754 prefixEnd_4137754 := by exact prefixLift 4137754
  have htrace : WordTrace (prefixWord ++ tailWord_4137754) baseStart_4137754 baseEnd_4137754 := by
    simpa [prefixWord, tailWord_4137754, baseEnd_4137754] using wordTrace_append hprefix tailTrace_4137754
  have hstable : (prefixWord ++ tailWord_4137754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137754).length < 2 ^ (prefixWord ++ tailWord_4137754).sum := by decide
  have hdescent : baseEnd_4137754 < baseStart_4137754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137805 : List Nat := [1, 6, 1, 2, 3, 1, 1, 7]
def baseStart_4137805 : Nat := 118140960795 + 4137805 * 2 ^ 59
def prefixEnd_4137805 : Nat := 4983230072969 + 3 ^ 40 * 4137805 * 2
def baseEnd_4137805 : Nat := 157383912561280633526525

theorem tailTrace_4137805 : CollatzResearch.WordTrace tailWord_4137805 prefixEnd_4137805 157383912561280633526525 := by
  unfold tailWord_4137805
  simp only [CollatzResearch.WordTrace]
  refine ⟨150918146774446640677374869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100612097849631093784916579 150918146774446640677374869)
  ·
    refine ⟨7074288130052186281751947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150918146774446640677374869 7074288130052186281751947)
    ·
      refine ⟨10611432195078279422627921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074288130052186281751947 10611432195078279422627921)
      ·
        refine ⟨7958574146308709566970941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10611432195078279422627921 7958574146308709566970941)
        ·
          refine ⟨2984465304865766087614103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7958574146308709566970941 2984465304865766087614103)
          ·
            refine ⟨4476697957298649131421155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984465304865766087614103 4476697957298649131421155)
            ·
              refine ⟨6715046935947973697131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476697957298649131421155 6715046935947973697131733)
              ·
                refine ⟨157383912561280633526525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6715046935947973697131733 157383912561280633526525)
                ·
                  rfl

theorem cell22_4137805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 7].length) (baseStart_4137805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137805 prefixEnd_4137805 := by exact prefixLift 4137805
  have htrace : WordTrace (prefixWord ++ tailWord_4137805) baseStart_4137805 baseEnd_4137805 := by
    simpa [prefixWord, tailWord_4137805, baseEnd_4137805] using wordTrace_append hprefix tailTrace_4137805
  have hstable : (prefixWord ++ tailWord_4137805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137805).length < 2 ^ (prefixWord ++ tailWord_4137805).sum := by decide
  have hdescent : baseEnd_4137805 < baseStart_4137805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137861 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 6]
def baseStart_4137861 : Nat := 118140960795 + 4137861 * 2 ^ 59
def prefixEnd_4137861 : Nat := 4983230072969 + 3 ^ 40 * 4137861 * 2
def baseEnd_4137861 : Nat := 472158127665320074112851

theorem tailTrace_4137861 : CollatzResearch.WordTrace tailWord_4137861 prefixEnd_4137861 472158127665320074112851 := by
  unfold tailWord_4137861
  simp only [CollatzResearch.WordTrace]
  refine ⟨150920189262243762241413437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100613459508162508160942291 150920189262243762241413437)
  ·
    refine ⟨56595070973341410840530039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150920189262243762241413437 56595070973341410840530039)
    ·
      refine ⟨84892606460012116260795059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56595070973341410840530039 84892606460012116260795059)
      ·
        refine ⟨127338909690018174391192589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84892606460012116260795059 127338909690018174391192589)
        ·
          refine ⟨47752091133756815396697221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127338909690018174391192589 47752091133756815396697221)
          ·
            refine ⟨8953517087579402886880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47752091133756815396697221 8953517087579402886880729)
            ·
              refine ⟨6715137815684552165160547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8953517087579402886880729 6715137815684552165160547)
              ·
                refine ⟨10072706723526828247740821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715137815684552165160547 10072706723526828247740821)
                ·
                  refine ⟨472158127665320074112851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10072706723526828247740821 472158127665320074112851)
                  ·
                    rfl

theorem cell22_4137861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_4137861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137861 prefixEnd_4137861 := by exact prefixLift 4137861
  have htrace : WordTrace (prefixWord ++ tailWord_4137861) baseStart_4137861 baseEnd_4137861 := by
    simpa [prefixWord, tailWord_4137861, baseEnd_4137861] using wordTrace_append hprefix tailTrace_4137861
  have hstable : (prefixWord ++ tailWord_4137861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137861).length < 2 ^ (prefixWord ++ tailWord_4137861).sum := by decide
  have hdescent : baseEnd_4137861 < baseStart_4137861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137955 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 1, 3]
def baseStart_4137955 : Nat := 118140960795 + 4137955 * 2 ^ 59
def prefixEnd_4137955 : Nat := 4983230072969 + 3 ^ 40 * 4137955 * 2
def baseEnd_4137955 : Nat := 1416506561116975310488265

theorem tailTrace_4137955 : CollatzResearch.WordTrace tailWord_4137955 prefixEnd_4137955 1416506561116975310488265 := by
  unfold tailWord_4137955
  simp only [CollatzResearch.WordTrace]
  refine ⟨150923617723903216295335319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100615745149268810863556879 150923617723903216295335319)
  ·
    refine ⟨226385426585854824443002979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150923617723903216295335319 226385426585854824443002979)
    ·
      refine ⟨339578139878782236664504469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226385426585854824443002979 339578139878782236664504469)
      ·
        refine ⟨15917725306817917343648647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 339578139878782236664504469 15917725306817917343648647)
        ·
          refine ⟨23876587960226876015472971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15917725306817917343648647 23876587960226876015472971)
          ·
            refine ⟨35814881940340314023209457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23876587960226876015472971 35814881940340314023209457)
            ·
              refine ⟨26861161455255235517407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35814881940340314023209457 26861161455255235517407093)
              ·
                refine ⟨2518233886430178329756915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26861161455255235517407093 2518233886430178329756915)
                ·
                  refine ⟨3777350829645267494635373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518233886430178329756915 3777350829645267494635373)
                  ·
                    refine ⟨1416506561116975310488265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777350829645267494635373 1416506561116975310488265)
                    ·
                      rfl

theorem cell22_4137955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 3].length) (baseStart_4137955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137955 prefixEnd_4137955 := by exact prefixLift 4137955
  have htrace : WordTrace (prefixWord ++ tailWord_4137955) baseStart_4137955 baseEnd_4137955 := by
    simpa [prefixWord, tailWord_4137955, baseEnd_4137955] using wordTrace_append hprefix tailTrace_4137955
  have hstable : (prefixWord ++ tailWord_4137955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137955).length < 2 ^ (prefixWord ++ tailWord_4137955).sum := by decide
  have hdescent : baseEnd_4137955 < baseStart_4137955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137996 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_4137996 : Nat := 118140960795 + 4137996 * 2 ^ 59
def prefixEnd_4137996 : Nat := 4983230072969 + 3 ^ 40 * 4137996 * 2
def baseEnd_4137996 : Nat := 472173532084954956737713

theorem tailTrace_4137996 : CollatzResearch.WordTrace tailWord_4137996 prefixEnd_4137996 472173532084954956737713 := by
  unfold tailWord_4137996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75462556558377340148788921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100616742077836453531718561 75462556558377340148788921)
  ·
    refine ⟨56596917418783005111591691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75462556558377340148788921 56596917418783005111591691)
    ·
      refine ⟨84895376128174507667387537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56596917418783005111591691 84895376128174507667387537)
      ·
        refine ⟨63671532096130880750540653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84895376128174507667387537 63671532096130880750540653)
        ·
          refine ⟨23876824536049080281452745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63671532096130880750540653 23876824536049080281452745)
          ·
            refine ⟨17907618402036810211089559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23876824536049080281452745 17907618402036810211089559)
            ·
              refine ⟨26861427603055215316634339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17907618402036810211089559 26861427603055215316634339)
              ·
                refine ⟨40292141404582822974951509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26861427603055215316634339 40292141404582822974951509)
                ·
                  refine ⟨472173532084954956737713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40292141404582822974951509 472173532084954956737713)
                  ·
                    rfl

theorem cell22_4137996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_4137996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137996 prefixEnd_4137996 := by exact prefixLift 4137996
  have htrace : WordTrace (prefixWord ++ tailWord_4137996) baseStart_4137996 baseEnd_4137996 := by
    simpa [prefixWord, tailWord_4137996, baseEnd_4137996] using wordTrace_append hprefix tailTrace_4137996
  have hstable : (prefixWord ++ tailWord_4137996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137996).length < 2 ^ (prefixWord ++ tailWord_4137996).sum := by decide
  have hdescent : baseEnd_4137996 < baseStart_4137996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4137998 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_4137998 : Nat := 118140960795 + 4137998 * 2 ^ 59
def prefixEnd_4137998 : Nat := 4983230072969 + 3 ^ 40 * 4137998 * 2
def baseEnd_4137998 : Nat := 1416521280895737531663133

theorem tailTrace_4137998 : CollatzResearch.WordTrace tailWord_4137998 prefixEnd_4137998 1416521280895737531663133 := by
  unfold tailWord_4137998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865648257843429329893831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100616790708498289759433765 18865648257843429329893831)
  ·
    refine ⟨28298472386765143994840747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18865648257843429329893831 28298472386765143994840747)
    ·
      refine ⟨42447708580147715992261121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28298472386765143994840747 42447708580147715992261121)
      ·
        refine ⟨31835781435110786994195841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42447708580147715992261121 31835781435110786994195841)
        ·
          refine ⟨23876836076333090245646881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31835781435110786994195841 23876836076333090245646881)
          ·
            refine ⟨17907627057249817684235161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23876836076333090245646881 17907627057249817684235161)
            ·
              refine ⟨13430720292937363263176371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17907627057249817684235161 13430720292937363263176371)
              ·
                refine ⟨20146080439406044894764557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13430720292937363263176371 20146080439406044894764557)
                ·
                  refine ⟨7554780164777266835536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20146080439406044894764557 7554780164777266835536709)
                  ·
                    refine ⟨1416521280895737531663133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554780164777266835536709 1416521280895737531663133)
                    ·
                      rfl

theorem cell22_4137998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_4137998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4137998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4137998 prefixEnd_4137998 := by exact prefixLift 4137998
  have htrace : WordTrace (prefixWord ++ tailWord_4137998) baseStart_4137998 baseEnd_4137998 := by
    simpa [prefixWord, tailWord_4137998, baseEnd_4137998] using wordTrace_append hprefix tailTrace_4137998
  have hstable : (prefixWord ++ tailWord_4137998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4137998).length < 2 ^ (prefixWord ++ tailWord_4137998).sum := by decide
  have hdescent : baseEnd_4137998 < baseStart_4137998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4137998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138015 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 1, 4]
def baseStart_4138015 : Nat := 118140960795 + 4138015 * 2 ^ 59
def prefixEnd_4138015 : Nat := 4983230072969 + 3 ^ 40 * 4138015 * 2
def baseEnd_4138015 : Nat := 1416527100343155153988081

theorem tailTrace_4138015 : CollatzResearch.WordTrace tailWord_4138015 prefixEnd_4138015 1416527100343155153988081 := by
  unfold tailWord_4138015
  simp only [CollatzResearch.WordTrace]
  refine ⟨150925806103685846542519499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100617204069123897695012999 150925806103685846542519499)
  ·
    refine ⟨226388709155528769813779249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150925806103685846542519499 226388709155528769813779249)
    ·
      refine ⟨169791531866646577360334437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226388709155528769813779249 169791531866646577360334437)
      ·
        refine ⟨31835912224996233255062707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169791531866646577360334437 31835912224996233255062707)
        ·
          refine ⟨47753868337494349882594061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31835912224996233255062707 47753868337494349882594061)
          ·
            refine ⟨17907700626560381205972773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47753868337494349882594061 17907700626560381205972773)
            ·
              refine ⟨3357693867480071476119895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17907700626560381205972773 3357693867480071476119895)
              ·
                refine ⟨5036540801220107214179843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357693867480071476119895 5036540801220107214179843)
                ·
                  refine ⟨7554811201830160821269765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036540801220107214179843 7554811201830160821269765)
                  ·
                    refine ⟨1416527100343155153988081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554811201830160821269765 1416527100343155153988081)
                    ·
                      rfl

theorem cell22_4138015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_4138015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138015 prefixEnd_4138015 := by exact prefixLift 4138015
  have htrace : WordTrace (prefixWord ++ tailWord_4138015) baseStart_4138015 baseEnd_4138015 := by
    simpa [prefixWord, tailWord_4138015, baseEnd_4138015] using wordTrace_append hprefix tailTrace_4138015
  have hstable : (prefixWord ++ tailWord_4138015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138015).length < 2 ^ (prefixWord ++ tailWord_4138015).sum := by decide
  have hdescent : baseEnd_4138015 < baseStart_4138015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138028 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_4138028 : Nat := 118140960795 + 4138028 * 2 ^ 59
def prefixEnd_4138028 : Nat := 4983230072969 + 3 ^ 40 * 4138028 * 2
def baseEnd_4138028 : Nat := 1416531550508827453413041

theorem tailTrace_4138028 : CollatzResearch.WordTrace tailWord_4138028 prefixEnd_4138028 1416531550508827453413041 := by
  unfold tailWord_4138028
  simp only [CollatzResearch.WordTrace]
  refine ⟨75463140126319374881371369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100617520168425833175161825 75463140126319374881371369)
  ·
    refine ⟨56597355094739531161028527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75463140126319374881371369 56597355094739531161028527)
    ·
      refine ⟨84896032642109296741542791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56597355094739531161028527 84896032642109296741542791)
      ·
        refine ⟨127344048963163945112314187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84896032642109296741542791 127344048963163945112314187)
        ·
          refine ⟨191016073444745917668471281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127344048963163945112314187 191016073444745917668471281)
          ·
            refine ⟨143262055083559438251353461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191016073444745917668471281 143262055083559438251353461)
            ·
              refine ⟨13430817664083697336064387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143262055083559438251353461 13430817664083697336064387)
              ·
                refine ⟨20146226496125546004096581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13430817664083697336064387 20146226496125546004096581)
                ·
                  refine ⟨3777417468023539875768109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20146226496125546004096581 3777417468023539875768109)
                  ·
                    refine ⟨1416531550508827453413041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777417468023539875768109 1416531550508827453413041)
                    ·
                      rfl

theorem cell22_4138028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_4138028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138028 prefixEnd_4138028 := by exact prefixLift 4138028
  have htrace : WordTrace (prefixWord ++ tailWord_4138028) baseStart_4138028 baseEnd_4138028 := by
    simpa [prefixWord, tailWord_4138028, baseEnd_4138028] using wordTrace_append hprefix tailTrace_4138028
  have hstable : (prefixWord ++ tailWord_4138028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138028).length < 2 ^ (prefixWord ++ tailWord_4138028).sum := by decide
  have hdescent : baseEnd_4138028 < baseStart_4138028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138030 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_4138030 : Nat := 118140960795 + 4138030 * 2 ^ 59
def prefixEnd_4138030 : Nat := 4983230072969 + 3 ^ 40 * 4138030 * 2
def baseEnd_4138030 : Nat := 472177411716566704954345

theorem tailTrace_4138030 : CollatzResearch.WordTrace tailWord_4138030 prefixEnd_4138030 472177411716566704954345 := by
  unfold tailWord_4138030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18865794149828938013039443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100617568799087669402877029 18865794149828938013039443)
  ·
    refine ⟨28298691224743407019559165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18865794149828938013039443 28298691224743407019559165)
    ·
      refine ⟨10612009209278777632334687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28298691224743407019559165 10612009209278777632334687)
      ·
        refine ⟨15918013813918166448502031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612009209278777632334687 15918013813918166448502031)
        ·
          refine ⟨23877020720877249672753047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918013813918166448502031 23877020720877249672753047)
          ·
            refine ⟨35815531081315874509129571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23877020720877249672753047 35815531081315874509129571)
            ·
              refine ⟨53723296621973811763694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35815531081315874509129571 53723296621973811763694357)
              ·
                refine ⟨2518279529155022426423173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53723296621973811763694357 2518279529155022426423173)
                ·
                  refine ⟨472177411716566704954345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518279529155022426423173 472177411716566704954345)
                  ·
                    rfl

theorem cell22_4138030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_4138030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138030 prefixEnd_4138030 := by exact prefixLift 4138030
  have htrace : WordTrace (prefixWord ++ tailWord_4138030) baseStart_4138030 baseEnd_4138030 := by
    simpa [prefixWord, tailWord_4138030, baseEnd_4138030] using wordTrace_append hprefix tailTrace_4138030
  have hstable : (prefixWord ++ tailWord_4138030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138030).length < 2 ^ (prefixWord ++ tailWord_4138030).sum := by decide
  have hdescent : baseEnd_4138030 < baseStart_4138030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138045 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_4138045 : Nat := 118140960795 + 4138045 * 2 ^ 59
def prefixEnd_4138045 : Nat := 4983230072969 + 3 ^ 40 * 4138045 * 2
def baseEnd_4138045 : Nat := 1416537369956245075737989

theorem tailTrace_4138045 : CollatzResearch.WordTrace tailWord_4138045 prefixEnd_4138045 1416537369956245075737989 := by
  unfold tailWord_4138045
  simp only [CollatzResearch.WordTrace]
  refine ⟨150926900293577161666111589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100617933529051441110741059 150926900293577161666111589)
  ·
    refine ⟨28298793805045717812395923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150926900293577161666111589 28298793805045717812395923)
    ·
      refine ⟨42448190707568576718593885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28298793805045717812395923 42448190707568576718593885)
      ·
        refine ⟨15918071515338216269472707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42448190707568576718593885 15918071515338216269472707)
        ·
          refine ⟨23877107273007324404209061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918071515338216269472707 23877107273007324404209061)
          ·
            refine ⟨4476957613688873325789199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23877107273007324404209061 4476957613688873325789199)
            ·
              refine ⟨6715436420533309988683799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476957613688873325789199 6715436420533309988683799)
              ·
                refine ⟨10073154630799964983025699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6715436420533309988683799 10073154630799964983025699)
                ·
                  refine ⟨15109731946199947474538549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073154630799964983025699 15109731946199947474538549)
                  ·
                    refine ⟨1416537369956245075737989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15109731946199947474538549 1416537369956245075737989)
                    ·
                      rfl

theorem cell22_4138045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_4138045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138045 prefixEnd_4138045 := by exact prefixLift 4138045
  have htrace : WordTrace (prefixWord ++ tailWord_4138045) baseStart_4138045 baseEnd_4138045 := by
    simpa [prefixWord, tailWord_4138045, baseEnd_4138045] using wordTrace_append hprefix tailTrace_4138045
  have hstable : (prefixWord ++ tailWord_4138045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138045).length < 2 ^ (prefixWord ++ tailWord_4138045).sum := by decide
  have hdescent : baseEnd_4138045 < baseStart_4138045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138056 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4138056 : Nat := 118140960795 + 4138056 * 2 ^ 59
def prefixEnd_4138056 : Nat := 4983230072969 + 3 ^ 40 * 4138056 * 2
def baseEnd_4138056 : Nat := 1416541135481044713712955

theorem tailTrace_4138056 : CollatzResearch.WordTrace tailWord_4138056 prefixEnd_4138056 1416541135481044713712955 := by
  unfold tailWord_4138056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75463650748268655272381011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100618200997691540363174681 75463650748268655272381011)
  ·
    refine ⟨113195476122402982908571517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75463650748268655272381011 113195476122402982908571517)
    ·
      refine ⟨42448303545901118590714319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113195476122402982908571517 42448303545901118590714319)
      ·
        refine ⟨63672455318851677886071479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42448303545901118590714319 63672455318851677886071479)
        ·
          refine ⟨95508682978277516829107219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63672455318851677886071479 95508682978277516829107219)
          ·
            refine ⟨143263024467416275243660829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95508682978277516829107219 143263024467416275243660829)
            ·
              refine ⟨53723634175281103216372811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143263024467416275243660829 53723634175281103216372811)
              ·
                refine ⟨80585451262921654824559217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53723634175281103216372811 80585451262921654824559217)
                ·
                  refine ⟨60439088447191241118419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80585451262921654824559217 60439088447191241118419413)
                  ·
                    refine ⟨1416541135481044713712955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60439088447191241118419413 1416541135481044713712955)
                    ·
                      rfl

theorem cell22_4138056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4138056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138056 prefixEnd_4138056 := by exact prefixLift 4138056
  have htrace : WordTrace (prefixWord ++ tailWord_4138056) baseStart_4138056 baseEnd_4138056 := by
    simpa [prefixWord, tailWord_4138056, baseEnd_4138056] using wordTrace_append hprefix tailTrace_4138056
  have hstable : (prefixWord ++ tailWord_4138056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138056).length < 2 ^ (prefixWord ++ tailWord_4138056).sum := by decide
  have hdescent : baseEnd_4138056 < baseStart_4138056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138058 : List Nat := [3, 1, 2, 1, 1, 2, 6, 6]
def baseStart_4138058 : Nat := 118140960795 + 4138058 * 2 ^ 59
def prefixEnd_4138058 : Nat := 4983230072969 + 3 ^ 40 * 4138058 * 2
def baseEnd_4138058 : Nat := 157393535569101930573661

theorem tailTrace_4138058 : CollatzResearch.WordTrace tailWord_4138058 prefixEnd_4138058 157393535569101930573661 := by
  unfold tailWord_4138058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731843610632516221583707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100618249628353376590889885 37731843610632516221583707)
  ·
    refine ⟨56597765415948774332375561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37731843610632516221583707 56597765415948774332375561)
    ·
      refine ⟨42448324061961580749281671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56597765415948774332375561 42448324061961580749281671)
      ·
        refine ⟨63672486092942371123922507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42448324061961580749281671 63672486092942371123922507)
        ·
          refine ⟨95508729139413556685883761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63672486092942371123922507 95508729139413556685883761)
          ·
            refine ⟨71631546854560167514412821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95508729139413556685883761 71631546854560167514412821)
            ·
              refine ⟨3357728758807507852238101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71631546854560167514412821 3357728758807507852238101)
              ·
                refine ⟨157393535569101930573661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357728758807507852238101 157393535569101930573661)
                ·
                  rfl

theorem cell22_4138058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_4138058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138058 prefixEnd_4138058 := by exact prefixLift 4138058
  have htrace : WordTrace (prefixWord ++ tailWord_4138058) baseStart_4138058 baseEnd_4138058 := by
    simpa [prefixWord, tailWord_4138058, baseEnd_4138058] using wordTrace_append hprefix tailTrace_4138058
  have hstable : (prefixWord ++ tailWord_4138058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138058).length < 2 ^ (prefixWord ++ tailWord_4138058).sum := by decide
  have hdescent : baseEnd_4138058 < baseStart_4138058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138071 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_4138071 : Nat := 118140960795 + 4138071 * 2 ^ 59
def prefixEnd_4138071 : Nat := 4983230072969 + 3 ^ 40 * 4138071 * 2
def baseEnd_4138071 : Nat := 1416546270287589674587909

theorem tailTrace_4138071 : CollatzResearch.WordTrace tailWord_4138071 prefixEnd_4138071 1416546270287589674587909 := by
  unfold tailWord_4138071
  simp only [CollatzResearch.WordTrace]
  refine ⟨150927848591482968106558067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100618565727655312071038711 150927848591482968106558067)
  ·
    refine ⟨226391772887224452159837101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150927848591482968106558067 226391772887224452159837101)
    ·
      refine ⟨84896914832709169559938913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226391772887224452159837101 84896914832709169559938913)
      ·
        refine ⟨63672686124531877169954185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84896914832709169559938913 63672686124531877169954185)
        ·
          refine ⟨47754514593398907877465639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63672686124531877169954185 47754514593398907877465639)
          ·
            refine ⟨71631771890098361816198459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47754514593398907877465639 71631771890098361816198459)
            ·
              refine ⟨107447657835147542724297689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71631771890098361816198459 107447657835147542724297689)
              ·
                refine ⟨80585743376360657043223267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107447657835147542724297689 80585743376360657043223267)
                ·
                  refine ⟨120878615064540985564834901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80585743376360657043223267 120878615064540985564834901)
                  ·
                    refine ⟨1416546270287589674587909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120878615064540985564834901 1416546270287589674587909)
                    ·
                      rfl

theorem cell22_4138071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_4138071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138071 prefixEnd_4138071 := by exact prefixLift 4138071
  have htrace : WordTrace (prefixWord ++ tailWord_4138071) baseStart_4138071 baseEnd_4138071 := by
    simpa [prefixWord, tailWord_4138071, baseEnd_4138071] using wordTrace_append hprefix tailTrace_4138071
  have hstable : (prefixWord ++ tailWord_4138071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138071).length < 2 ^ (prefixWord ++ tailWord_4138071).sum := by decide
  have hdescent : baseEnd_4138071 < baseStart_4138071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138077 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4138077 : Nat := 118140960795 + 4138077 * 2 ^ 59
def prefixEnd_4138077 : Nat := 4983230072969 + 3 ^ 40 * 4138077 * 2
def baseEnd_4138077 : Nat := 1416548324210207658937891

theorem tailTrace_4138077 : CollatzResearch.WordTrace tailWord_4138077 prefixEnd_4138077 1416548324210207658937891 := by
  unfold tailWord_4138077
  simp only [CollatzResearch.WordTrace]
  refine ⟨150928067429461231131276485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100618711619640820754184323 150928067429461231131276485)
  ·
    refine ⟨28299012643023980837114341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150928067429461231131276485 28299012643023980837114341)
    ·
      refine ⟨5306064870566996406958939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28299012643023980837114341 5306064870566996406958939)
      ·
        refine ⟨7959097305850494610438409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306064870566996406958939 7959097305850494610438409)
        ·
          refine ⟨5969322979387870957828807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7959097305850494610438409 5969322979387870957828807)
          ·
            refine ⟨8953984469081806436743211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969322979387870957828807 8953984469081806436743211)
            ·
              refine ⟨13430976703622709655114817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8953984469081806436743211 13430976703622709655114817)
              ·
                refine ⟨10073232527717032241336113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13430976703622709655114817 10073232527717032241336113)
                ·
                  refine ⟨7554924395787774181002085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10073232527717032241336113 7554924395787774181002085)
                  ·
                    refine ⟨1416548324210207658937891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7554924395787774181002085 1416548324210207658937891)
                    ·
                      rfl

theorem cell22_4138077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4138077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138077 prefixEnd_4138077 := by exact prefixLift 4138077
  have htrace : WordTrace (prefixWord ++ tailWord_4138077) baseStart_4138077 baseEnd_4138077 := by
    simpa [prefixWord, tailWord_4138077, baseEnd_4138077] using wordTrace_append hprefix tailTrace_4138077
  have hstable : (prefixWord ++ tailWord_4138077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138077).length < 2 ^ (prefixWord ++ tailWord_4138077).sum := by decide
  have hdescent : baseEnd_4138077 < baseStart_4138077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138103 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 5]
def baseStart_4138103 : Nat := 118140960795 + 4138103 * 2 ^ 59
def prefixEnd_4138103 : Nat := 4983230072969 + 3 ^ 40 * 4138103 * 2
def baseEnd_4138103 : Nat := 472185741513850752595937

theorem tailTrace_4138103 : CollatzResearch.WordTrace tailWord_4138103 prefixEnd_4138103 472185741513850752595937 := by
  unfold tailWord_4138103
  simp only [CollatzResearch.WordTrace]
  refine ⟨150929015727367037571722963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100619343818244691714481975 150929015727367037571722963)
  ·
    refine ⟨226393523591050556357584445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150929015727367037571722963 226393523591050556357584445)
    ·
      refine ⟨84897571346643958634094167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226393523591050556357584445 84897571346643958634094167)
      ·
        refine ⟨127346357019965937951141251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84897571346643958634094167 127346357019965937951141251)
        ·
          refine ⟨191019535529948906926711877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127346357019965937951141251 191019535529948906926711877)
          ·
            refine ⟨35816162911865420048758477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191019535529948906926711877 35816162911865420048758477)
            ·
              refine ⟨13431061091949532518284429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35816162911865420048758477 13431061091949532518284429)
              ·
                refine ⟨5036647909481074694356661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13431061091949532518284429 5036647909481074694356661)
                ·
                  refine ⟨472185741513850752595937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5036647909481074694356661 472185741513850752595937)
                  ·
                    rfl

theorem cell22_4138103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 5].length) (baseStart_4138103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138103 prefixEnd_4138103 := by exact prefixLift 4138103
  have htrace : WordTrace (prefixWord ++ tailWord_4138103) baseStart_4138103 baseEnd_4138103 := by
    simpa [prefixWord, tailWord_4138103, baseEnd_4138103] using wordTrace_append hprefix tailTrace_4138103
  have hstable : (prefixWord ++ tailWord_4138103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138103).length < 2 ^ (prefixWord ++ tailWord_4138103).sum := by decide
  have hdescent : baseEnd_4138103 < baseStart_4138103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138163 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 5]
def baseStart_4138163 : Nat := 118140960795 + 4138163 * 2 ^ 59
def prefixEnd_4138163 : Nat := 4983230072969 + 3 ^ 40 * 4138163 * 2
def baseEnd_4138163 : Nat := 1416577763767732101287627

theorem tailTrace_4138163 : CollatzResearch.WordTrace tailWord_4138163 prefixEnd_4138163 1416577763767732101287627 := by
  unfold tailWord_4138163
  simp only [CollatzResearch.WordTrace]
  refine ⟨150931204107149667818907143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100620802738099778545938095 150931204107149667818907143)
  ·
    refine ⟨226396806160724501728360715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150931204107149667818907143 226396806160724501728360715)
    ·
      refine ⟨339595209241086752592541073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226396806160724501728360715 339595209241086752592541073)
      ·
        refine ⟨254696406930815064444405805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339595209241086752592541073 254696406930815064444405805)
        ·
          refine ⟨95511152599055649166652177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254696406930815064444405805 95511152599055649166652177)
          ·
            refine ⟨71633364449291736874989133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95511152599055649166652177 71633364449291736874989133)
            ·
              refine ⟨26862511668484401328120925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71633364449291736874989133 26862511668484401328120925)
              ·
                refine ⟨10073441875681650498045347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26862511668484401328120925 10073441875681650498045347)
                ·
                  refine ⟨15110162813522475747068021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10073441875681650498045347 15110162813522475747068021)
                  ·
                    refine ⟨1416577763767732101287627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15110162813522475747068021 1416577763767732101287627)
                    ·
                      rfl

theorem cell22_4138163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_4138163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138163 prefixEnd_4138163 := by exact prefixLift 4138163
  have htrace : WordTrace (prefixWord ++ tailWord_4138163) baseStart_4138163 baseEnd_4138163 := by
    simpa [prefixWord, tailWord_4138163, baseEnd_4138163] using wordTrace_append hprefix tailTrace_4138163
  have hstable : (prefixWord ++ tailWord_4138163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138163).length < 2 ^ (prefixWord ++ tailWord_4138163).sum := by decide
  have hdescent : baseEnd_4138163 < baseStart_4138163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138197 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_4138197 : Nat := 118140960795 + 4138197 * 2 ^ 59
def prefixEnd_4138197 : Nat := 4983230072969 + 3 ^ 40 * 4138197 * 2
def baseEnd_4138197 : Nat := 1416589402662567345937523

theorem tailTrace_4138197 : CollatzResearch.WordTrace tailWord_4138197 prefixEnd_4138197 1416589402662567345937523 := by
  unfold tailWord_4138197
  simp only [CollatzResearch.WordTrace]
  refine ⟨150932444189026491625644845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100621629459350994417096563 150932444189026491625644845)
  ·
    refine ⟨56599666570884934359616817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150932444189026491625644845 56599666570884934359616817)
    ·
      refine ⟨42449749928163700769712613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56599666570884934359616817 42449749928163700769712613)
      ·
        refine ⟨7959328111530693894321115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42449749928163700769712613 7959328111530693894321115)
        ·
          refine ⟨11938992167296040841481673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959328111530693894321115 11938992167296040841481673)
          ·
            refine ⟨8954244125472030631111255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11938992167296040841481673 8954244125472030631111255)
            ·
              refine ⟨13431366188208045946666883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954244125472030631111255 13431366188208045946666883)
              ·
                refine ⟨20147049282312068920000325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13431366188208045946666883 20147049282312068920000325)
                ·
                  refine ⟨3777571740433512922500061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20147049282312068920000325 3777571740433512922500061)
                  ·
                    refine ⟨1416589402662567345937523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777571740433512922500061 1416589402662567345937523)
                    ·
                      rfl

theorem cell22_4138197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_4138197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138197 prefixEnd_4138197 := by exact prefixLift 4138197
  have htrace : WordTrace (prefixWord ++ tailWord_4138197) baseStart_4138197 baseEnd_4138197 := by
    simpa [prefixWord, tailWord_4138197, baseEnd_4138197] using wordTrace_append hprefix tailTrace_4138197
  have hstable : (prefixWord ++ tailWord_4138197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138197).length < 2 ^ (prefixWord ++ tailWord_4138197).sum := by decide
  have hdescent : baseEnd_4138197 < baseStart_4138197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138272 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_4138272 : Nat := 118140960795 + 4138272 * 2 ^ 59
def prefixEnd_4138272 : Nat := 4983230072969 + 3 ^ 40 * 4138272 * 2
def baseEnd_4138272 : Nat := 472205025565097383437431

theorem tailTrace_4138272 : CollatzResearch.WordTrace tailWord_4138272 prefixEnd_4138272 472205025565097383437431 := by
  unfold tailWord_4138272
  simp only [CollatzResearch.WordTrace]
  refine ⟨75467589831877389717312535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100623453109169852956416713 75467589831877389717312535)
  ·
    refine ⟨113201384747816084575968803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75467589831877389717312535 113201384747816084575968803)
    ·
      refine ⟨169802077121724126863953205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113201384747816084575968803 169802077121724126863953205)
      ·
        refine ⟨15918944730161636893495613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169802077121724126863953205 15918944730161636893495613)
        ·
          refine ⟨5969604273810613835060855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15918944730161636893495613 5969604273810613835060855)
          ·
            refine ⟨8954406410715920752591283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969604273810613835060855 8954406410715920752591283)
            ·
              refine ⟨13431609616073881128886925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954406410715920752591283 13431609616073881128886925)
              ·
                refine ⟨5036853606027705423332597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13431609616073881128886925 5036853606027705423332597)
                ·
                  refine ⟨472205025565097383437431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5036853606027705423332597 472205025565097383437431)
                  ·
                    rfl

theorem cell22_4138272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_4138272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138272 prefixEnd_4138272 := by exact prefixLift 4138272
  have htrace : WordTrace (prefixWord ++ tailWord_4138272) baseStart_4138272 baseEnd_4138272 := by
    simpa [prefixWord, tailWord_4138272, baseEnd_4138272] using wordTrace_append hprefix tailTrace_4138272
  have hstable : (prefixWord ++ tailWord_4138272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138272).length < 2 ^ (prefixWord ++ tailWord_4138272).sum := by decide
  have hdescent : baseEnd_4138272 < baseStart_4138272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138310 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4138310 : Nat := 118140960795 + 4138310 * 2 ^ 59
def prefixEnd_4138310 : Nat := 4983230072969 + 3 ^ 40 * 4138310 * 2
def baseEnd_4138310 : Nat := 1416628084871872717862177

theorem tailTrace_4138310 : CollatzResearch.WordTrace tailWord_4138310 prefixEnd_4138310 1416628084871872717862177 := by
  unfold tailWord_4138310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716767676175534747640887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100624377091744741283005589 4716767676175534747640887)
  ·
    refine ⟨7075151514263302121461331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716767676175534747640887 7075151514263302121461331)
    ·
      refine ⟨10612727271394953182191997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075151514263302121461331 10612727271394953182191997)
      ·
        refine ⟨3979772726773107443321999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10612727271394953182191997 3979772726773107443321999)
        ·
          refine ⟨5969659090159661164982999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979772726773107443321999 5969659090159661164982999)
          ·
            refine ⟨8954488635239491747474499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969659090159661164982999 8954488635239491747474499)
            ·
              refine ⟨13431732952859237621211749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954488635239491747474499 13431732952859237621211749)
              ·
                refine ⟨2518449928661107053977203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13431732952859237621211749 2518449928661107053977203)
                ·
                  refine ⟨3777674892991660580965805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518449928661107053977203 3777674892991660580965805)
                  ·
                    refine ⟨1416628084871872717862177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777674892991660580965805 1416628084871872717862177)
                    ·
                      rfl

theorem cell22_4138310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4138310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138310 prefixEnd_4138310 := by exact prefixLift 4138310
  have htrace : WordTrace (prefixWord ++ tailWord_4138310) baseStart_4138310 baseEnd_4138310 := by
    simpa [prefixWord, tailWord_4138310, baseEnd_4138310] using wordTrace_append hprefix tailTrace_4138310
  have hstable : (prefixWord ++ tailWord_4138310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138310).length < 2 ^ (prefixWord ++ tailWord_4138310).sum := by decide
  have hdescent : baseEnd_4138310 < baseStart_4138310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138315 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 8, 3]
def baseStart_4138315 : Nat := 118140960795 + 4138315 * 2 ^ 59
def prefixEnd_4138315 : Nat := 4983230072969 + 3 ^ 40 * 4138315 * 2
def baseEnd_4138315 : Nat := 1416629796474054371487161

theorem tailTrace_4138315 : CollatzResearch.WordTrace tailWord_4138315 prefixEnd_4138315 1416629796474054371487161 := by
  unfold tailWord_4138315
  simp only [CollatzResearch.WordTrace]
  refine ⟨150936748002598997778440399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100624498668399331852293599 150936748002598997778440399)
  ·
    refine ⟨226405122003898496667660599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150936748002598997778440399 226405122003898496667660599)
    ·
      refine ⟨339607683005847745001490899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226405122003898496667660599 339607683005847745001490899)
      ·
        refine ⟨509411524508771617502236349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339607683005847745001490899 509411524508771617502236349)
        ·
          refine ⟨191029321690789356563338631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509411524508771617502236349 191029321690789356563338631)
          ·
            refine ⟨286543982536184034845007947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191029321690789356563338631 286543982536184034845007947)
            ·
              refine ⟨429815973804276052267511921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286543982536184034845007947 429815973804276052267511921)
              ·
                refine ⟨322361980353207039200633941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429815973804276052267511921 322361980353207039200633941)
                ·
                  refine ⟨3777679457264144990632429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 322361980353207039200633941 3777679457264144990632429)
                  ·
                    refine ⟨1416629796474054371487161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777679457264144990632429 1416629796474054371487161)
                    ·
                      rfl

theorem cell22_4138315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 3].length) (baseStart_4138315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138315 prefixEnd_4138315 := by exact prefixLift 4138315
  have htrace : WordTrace (prefixWord ++ tailWord_4138315) baseStart_4138315 baseEnd_4138315 := by
    simpa [prefixWord, tailWord_4138315, baseEnd_4138315] using wordTrace_append hprefix tailTrace_4138315
  have hstable : (prefixWord ++ tailWord_4138315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138315).length < 2 ^ (prefixWord ++ tailWord_4138315).sum := by decide
  have hdescent : baseEnd_4138315 < baseStart_4138315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138330 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_4138330 : Nat := 118140960795 + 4138330 * 2 ^ 59
def prefixEnd_4138330 : Nat := 4983230072969 + 3 ^ 40 * 4138330 * 2
def baseEnd_4138330 : Nat := 1416634931280599332362115

theorem tailTrace_4138330 : CollatzResearch.WordTrace tailWord_4138330 prefixEnd_4138330 1416634931280599332362115 := by
  unfold tailWord_4138330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37734323774386163835059111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100624863398363103560157629 37734323774386163835059111)
  ·
    refine ⟨56601485661579245752588667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37734323774386163835059111 56601485661579245752588667)
    ·
      refine ⟨84902228492368868628883001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56601485661579245752588667 84902228492368868628883001)
      ·
        refine ⟨63676671369276651471662251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84902228492368868628883001 63676671369276651471662251)
        ·
          refine ⟨95515007053914977207493377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63676671369276651471662251 95515007053914977207493377)
          ·
            refine ⟨71636255290436232905620033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95515007053914977207493377 71636255290436232905620033)
            ·
              refine ⟨53727191467827174679215025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71636255290436232905620033 53727191467827174679215025)
              ·
                refine ⟨40295393600870381009411269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53727191467827174679215025 40295393600870381009411269)
                ·
                  refine ⟨7555386300163196439264613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40295393600870381009411269 7555386300163196439264613)
                  ·
                    refine ⟨1416634931280599332362115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555386300163196439264613 1416634931280599332362115)
                    ·
                      rfl

theorem cell22_4138330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_4138330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138330 prefixEnd_4138330 := by exact prefixLift 4138330
  have htrace : WordTrace (prefixWord ++ tailWord_4138330) baseStart_4138330 baseEnd_4138330 := by
    simpa [prefixWord, tailWord_4138330, baseEnd_4138330] using wordTrace_append hprefix tailTrace_4138330
  have hstable : (prefixWord ++ tailWord_4138330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138330).length < 2 ^ (prefixWord ++ tailWord_4138330).sum := by decide
  have hdescent : baseEnd_4138330 < baseStart_4138330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138396 : List Nat := [2, 2, 3, 4, 1, 2, 2, 6]
def baseStart_4138396 : Nat := 118140960795 + 4138396 * 2 ^ 59
def prefixEnd_4138396 : Nat := 4983230072969 + 3 ^ 40 * 4138396 * 2
def baseEnd_4138396 : Nat := 157406391603266351134657

theorem tailTrace_4138396 : CollatzResearch.WordTrace tailWord_4138396 prefixEnd_4138396 157406391603266351134657 := by
  unfold tailWord_4138396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75469851157652774306069521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100626468210203699074759361 75469851157652774306069521)
  ·
    refine ⟨56602388368239580729552141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75469851157652774306069521 56602388368239580729552141)
    ·
      refine ⟨21225895638089842773582053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56602388368239580729552141 21225895638089842773582053)
      ·
        refine ⟨3979855432141845520046635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21225895638089842773582053 3979855432141845520046635)
        ·
          refine ⟨5969783148212768280069953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979855432141845520046635 5969783148212768280069953)
          ·
            refine ⟨4477337361159576210052465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5969783148212768280069953 4477337361159576210052465)
            ·
              refine ⟨3358003020869682157539349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477337361159576210052465 3358003020869682157539349)
              ·
                refine ⟨157406391603266351134657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3358003020869682157539349 157406391603266351134657)
                ·
                  rfl

theorem cell22_4138396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_4138396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138396 prefixEnd_4138396 := by exact prefixLift 4138396
  have htrace : WordTrace (prefixWord ++ tailWord_4138396) baseStart_4138396 baseEnd_4138396 := by
    simpa [prefixWord, tailWord_4138396, baseEnd_4138396] using wordTrace_append hprefix tailTrace_4138396
  have hstable : (prefixWord ++ tailWord_4138396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138396).length < 2 ^ (prefixWord ++ tailWord_4138396).sum := by decide
  have hdescent : baseEnd_4138396 < baseStart_4138396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138405 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_4138405 : Nat := 118140960795 + 4138405 * 2 ^ 59
def prefixEnd_4138405 : Nat := 4983230072969 + 3 ^ 40 * 4138405 * 2
def baseEnd_4138405 : Nat := 1416660605313324136736885

theorem tailTrace_4138405 : CollatzResearch.WordTrace tailWord_4138405 prefixEnd_4138405 1416660605313324136736885 := by
  unfold tailWord_4138405
  simp only [CollatzResearch.WordTrace]
  refine ⟨150940030572272943149216669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100626687048181962099477779 150940030572272943149216669)
  ·
    refine ⟨56602511464602353680956251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150940030572272943149216669 56602511464602353680956251)
    ·
      refine ⟨84903767196903530521434377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56602511464602353680956251 84903767196903530521434377)
      ·
        refine ⟨63677825397677647891075783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84903767196903530521434377 63677825397677647891075783)
        ·
          refine ⟨95516738096516471836613675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63677825397677647891075783 95516738096516471836613675)
          ·
            refine ⟨143275107144774707754920513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95516738096516471836613675 143275107144774707754920513)
            ·
              refine ⟨107456330358581030816190385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143275107144774707754920513 107456330358581030816190385)
              ·
                refine ⟨80592247768935773112142789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107456330358581030816190385 80592247768935773112142789)
                ·
                  refine ⟨15111046456675457458526773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80592247768935773112142789 15111046456675457458526773)
                  ·
                    refine ⟨1416660605313324136736885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15111046456675457458526773 1416660605313324136736885)
                    ·
                      rfl

theorem cell22_4138405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_4138405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138405 prefixEnd_4138405 := by exact prefixLift 4138405
  have htrace : WordTrace (prefixWord ++ tailWord_4138405) baseStart_4138405 baseEnd_4138405 := by
    simpa [prefixWord, tailWord_4138405, baseEnd_4138405] using wordTrace_append hprefix tailTrace_4138405
  have hstable : (prefixWord ++ tailWord_4138405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138405).length < 2 ^ (prefixWord ++ tailWord_4138405).sum := by decide
  have hdescent : baseEnd_4138405 < baseStart_4138405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138428 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_4138428 : Nat := 118140960795 + 4138428 * 2 ^ 59
def prefixEnd_4138428 : Nat := 4983230072969 + 3 ^ 40 * 4138428 * 2
def baseEnd_4138428 : Nat := 1416668478683359743411815

theorem tailTrace_4138428 : CollatzResearch.WordTrace tailWord_4138428 prefixEnd_4138428 1416668478683359743411815 := by
  unfold tailWord_4138428
  simp only [CollatzResearch.WordTrace]
  refine ⟨75470434725594809038651969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100627246300793078718202625 75470434725594809038651969)
  ·
    refine ⟨56602826044196106778988977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75470434725594809038651969 56602826044196106778988977)
    ·
      refine ⟨42452119533147080084241733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56602826044196106778988977 42452119533147080084241733)
      ·
        refine ⟨7959772412465077515795325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42452119533147080084241733 7959772412465077515795325)
        ·
          refine ⟨2984914654674404068423247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7959772412465077515795325 2984914654674404068423247)
          ·
            refine ⟨4477371982011606102634871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984914654674404068423247 4477371982011606102634871)
            ·
              refine ⟨6716057973017409153952307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477371982011606102634871 6716057973017409153952307)
              ·
                refine ⟨10074086959526113730928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716057973017409153952307 10074086959526113730928461)
                ·
                  refine ⟨3777782609822292649098173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10074086959526113730928461 3777782609822292649098173)
                  ·
                    refine ⟨1416668478683359743411815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777782609822292649098173 1416668478683359743411815)
                    ·
                      rfl

theorem cell22_4138428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_4138428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138428 prefixEnd_4138428 := by exact prefixLift 4138428
  have htrace : WordTrace (prefixWord ++ tailWord_4138428) baseStart_4138428 baseEnd_4138428 := by
    simpa [prefixWord, tailWord_4138428, baseEnd_4138428] using wordTrace_append hprefix tailTrace_4138428
  have hstable : (prefixWord ++ tailWord_4138428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138428).length < 2 ^ (prefixWord ++ tailWord_4138428).sum := by decide
  have hdescent : baseEnd_4138428 < baseStart_4138428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138434 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4138434 : Nat := 118140960795 + 4138434 * 2 ^ 59
def prefixEnd_4138434 : Nat := 4983230072969 + 3 ^ 40 * 4138434 * 2
def baseEnd_4138434 : Nat := 1416670532605977727761797

theorem tailTrace_4138434 : CollatzResearch.WordTrace tailWord_4138434 prefixEnd_4138434 1416670532605977727761797 := by
  unfold tailWord_4138434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735272072291970275505589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100627392192778587401348237 37735272072291970275505589)
  ·
    refine ⟨3537681756777372213328649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37735272072291970275505589 3537681756777372213328649)
    ·
      refine ⟨2653261317583029159996487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537681756777372213328649 2653261317583029159996487)
      ·
        refine ⟨3979891976374543739994731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653261317583029159996487 3979891976374543739994731)
        ·
          refine ⟨5969837964561815609992097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979891976374543739994731 5969837964561815609992097)
          ·
            refine ⟨4477378473421361707494073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5969837964561815609992097 4477378473421361707494073)
            ·
              refine ⟨3358033855066021280620555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477378473421361707494073 3358033855066021280620555)
              ·
                refine ⟨5037050782599031920930833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358033855066021280620555 5037050782599031920930833)
                ·
                  refine ⟨3777788086949273940698125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037050782599031920930833 3777788086949273940698125)
                  ·
                    refine ⟨1416670532605977727761797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777788086949273940698125 1416670532605977727761797)
                    ·
                      rfl

theorem cell22_4138434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4138434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138434 prefixEnd_4138434 := by exact prefixLift 4138434
  have htrace : WordTrace (prefixWord ++ tailWord_4138434) baseStart_4138434 baseEnd_4138434 := by
    simpa [prefixWord, tailWord_4138434, baseEnd_4138434] using wordTrace_append hprefix tailTrace_4138434
  have hstable : (prefixWord ++ tailWord_4138434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138434).length < 2 ^ (prefixWord ++ tailWord_4138434).sum := by decide
  have hdescent : baseEnd_4138434 < baseStart_4138434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138467 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 5]
def baseStart_4138467 : Nat := 118140960795 + 4138467 * 2 ^ 59
def prefixEnd_4138467 : Nat := 4983230072969 + 3 ^ 40 * 4138467 * 2
def baseEnd_4138467 : Nat := 1416681829180376641686695

theorem tailTrace_4138467 : CollatzResearch.WordTrace tailWord_4138467 prefixEnd_4138467 1416681829180376641686695 := by
  unfold tailWord_4138467
  simp only [CollatzResearch.WordTrace]
  refine ⟨150942291898048327737973655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100628194598698885158649103 150942291898048327737973655)
  ·
    refine ⟨226413437847072491606960483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150942291898048327737973655 226413437847072491606960483)
    ·
      refine ⟨339620156770608737410440725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226413437847072491606960483 339620156770608737410440725)
      ·
        refine ⟨15919694848622284566114409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 339620156770608737410440725 15919694848622284566114409)
        ·
          refine ⟨11939771136466713424585807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15919694848622284566114409 11939771136466713424585807)
          ·
            refine ⟨17909656704700070136878711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11939771136466713424585807 17909656704700070136878711)
            ·
              refine ⟨26864485057050105205318067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17909656704700070136878711 26864485057050105205318067)
              ·
                refine ⟨40296727585575157807977101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26864485057050105205318067 40296727585575157807977101)
                ·
                  refine ⟨15111272844590684177991413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40296727585575157807977101 15111272844590684177991413)
                  ·
                    refine ⟨1416681829180376641686695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15111272844590684177991413 1416681829180376641686695)
                    ·
                      rfl

theorem cell22_4138467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_4138467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138467 prefixEnd_4138467 := by exact prefixLift 4138467
  have htrace : WordTrace (prefixWord ++ tailWord_4138467) baseStart_4138467 baseEnd_4138467 := by
    simpa [prefixWord, tailWord_4138467, baseEnd_4138467] using wordTrace_append hprefix tailTrace_4138467
  have hstable : (prefixWord ++ tailWord_4138467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138467).length < 2 ^ (prefixWord ++ tailWord_4138467).sum := by decide
  have hdescent : baseEnd_4138467 < baseStart_4138467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138471 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4138471 : Nat := 118140960795 + 4138471 * 2 ^ 59
def prefixEnd_4138471 : Nat := 4983230072969 + 3 ^ 40 * 4138471 * 2
def baseEnd_4138471 : Nat := 1416683198462121964586683

theorem tailTrace_4138471 : CollatzResearch.WordTrace tailWord_4138471 prefixEnd_4138471 1416683198462121964586683 := by
  unfold tailWord_4138471
  simp only [CollatzResearch.WordTrace]
  refine ⟨150942437790033836421119267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100628291860022557614079511 150942437790033836421119267)
  ·
    refine ⟨226413656685050754631678901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150942437790033836421119267 226413656685050754631678901)
    ·
      refine ⟨21226280314223508246719897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226413656685050754631678901 21226280314223508246719897)
      ·
        refine ⟨15919710235667631185039923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21226280314223508246719897 15919710235667631185039923)
        ·
          refine ⟨23879565353501446777559885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15919710235667631185039923 23879565353501446777559885)
          ·
            refine ⟨8954837007563042541584957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23879565353501446777559885 8954837007563042541584957)
            ·
              refine ⟨3358063877836140953094359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8954837007563042541584957 3358063877836140953094359)
              ·
                refine ⟨5037095816754211429641539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358063877836140953094359 5037095816754211429641539)
                ·
                  refine ⟨7555643725131317144462309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037095816754211429641539 7555643725131317144462309)
                  ·
                    refine ⟨1416683198462121964586683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555643725131317144462309 1416683198462121964586683)
                    ·
                      rfl

theorem cell22_4138471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4138471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138471 prefixEnd_4138471 := by exact prefixLift 4138471
  have htrace : WordTrace (prefixWord ++ tailWord_4138471) baseStart_4138471 baseEnd_4138471 := by
    simpa [prefixWord, tailWord_4138471, baseEnd_4138471] using wordTrace_append hprefix tailTrace_4138471
  have hstable : (prefixWord ++ tailWord_4138471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138471).length < 2 ^ (prefixWord ++ tailWord_4138471).sum := by decide
  have hdescent : baseEnd_4138471 < baseStart_4138471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138480 : List Nat := [2, 1, 1, 1, 3, 14]
def baseStart_4138480 : Nat := 118140960795 + 4138480 * 2 ^ 59
def prefixEnd_4138480 : Nat := 4983230072969 + 3 ^ 40 * 4138480 * 2
def baseEnd_4138480 : Nat := 17489954066000604211255

theorem tailTrace_4138480 : CollatzResearch.WordTrace tailWord_4138480 prefixEnd_4138480 17489954066000604211255 := by
  unfold tailWord_4138480
  simp only [CollatzResearch.WordTrace]
  refine ⟨75471383023500615479098447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100628510698000820638797929 75471383023500615479098447)
  ·
    refine ⟨113207074535250923218647671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75471383023500615479098447 113207074535250923218647671)
    ·
      refine ⟨169810611802876384827971507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113207074535250923218647671 169810611802876384827971507)
      ·
        refine ⟨254715917704314577241957261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169810611802876384827971507 254715917704314577241957261)
        ·
          refine ⟨95518469139117966465733973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254715917704314577241957261 95518469139117966465733973)
          ·
            refine ⟨17489954066000604211255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 95518469139117966465733973 17489954066000604211255)
            ·
              rfl

theorem cell22_4138480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 14].length) (baseStart_4138480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138480 prefixEnd_4138480 := by exact prefixLift 4138480
  have htrace : WordTrace (prefixWord ++ tailWord_4138480) baseStart_4138480 baseEnd_4138480 := by
    simpa [prefixWord, tailWord_4138480, baseEnd_4138480] using wordTrace_append hprefix tailTrace_4138480
  have hstable : (prefixWord ++ tailWord_4138480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138480).length < 2 ^ (prefixWord ++ tailWord_4138480).sum := by decide
  have hdescent : baseEnd_4138480 < baseStart_4138480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138486 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_4138486 : Nat := 118140960795 + 4138486 * 2 ^ 59
def prefixEnd_4138486 : Nat := 4983230072969 + 3 ^ 40 * 4138486 * 2
def baseEnd_4138486 : Nat := 472229444422888975153879

theorem tailTrace_4138486 : CollatzResearch.WordTrace tailWord_4138486 prefixEnd_4138486 472229444422888975153879 := by
  unfold tailWord_4138486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9433936555311218373932207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100628656589986329321943541 9433936555311218373932207)
  ·
    refine ⟨14150904832966827560898311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9433936555311218373932207 14150904832966827560898311)
    ·
      refine ⟨21226357249450241341347467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14150904832966827560898311 21226357249450241341347467)
      ·
        refine ⟨31839535874175362012021201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21226357249450241341347467 31839535874175362012021201)
        ·
          refine ⟨23879651905631521509015901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31839535874175362012021201 23879651905631521509015901)
          ·
            refine ⟨8954869464611820565880963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23879651905631521509015901 8954869464611820565880963)
            ·
              refine ⟨13432304196917730848821445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954869464611820565880963 13432304196917730848821445)
              ·
                refine ⟨2518557036922074534154021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13432304196917730848821445 2518557036922074534154021)
                ·
                  refine ⟨472229444422888975153879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518557036922074534154021 472229444422888975153879)
                  ·
                    rfl

theorem cell22_4138486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_4138486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138486 prefixEnd_4138486 := by exact prefixLift 4138486
  have htrace : WordTrace (prefixWord ++ tailWord_4138486) baseStart_4138486 baseEnd_4138486 := by
    simpa [prefixWord, tailWord_4138486, baseEnd_4138486] using wordTrace_append hprefix tailTrace_4138486
  have hstable : (prefixWord ++ tailWord_4138486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138486).length < 2 ^ (prefixWord ++ tailWord_4138486).sum := by decide
  have hdescent : baseEnd_4138486 < baseStart_4138486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138516 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4138516 : Nat := 118140960795 + 4138516 * 2 ^ 59
def prefixEnd_4138516 : Nat := 4983230072969 + 3 ^ 40 * 4138516 * 2
def baseEnd_4138516 : Nat := 1416698602881756847211545

theorem tailTrace_4138516 : CollatzResearch.WordTrace tailWord_4138516 prefixEnd_4138516 1416698602881756847211545 := by
  unfold tailWord_4138516
  simp only [CollatzResearch.WordTrace]
  refine ⟨75472039537435404553253701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100629386049913872737671601 75472039537435404553253701)
  ·
    refine ⟨14151007413269138353735069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75472039537435404553253701 14151007413269138353735069)
    ·
      refine ⟨5306627779975926882650651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14151007413269138353735069 5306627779975926882650651)
      ·
        refine ⟨7959941669963890323975977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306627779975926882650651 7959941669963890323975977)
        ·
          refine ⟨5969956252472917742981983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7959941669963890323975977 5969956252472917742981983)
          ·
            refine ⟨8954934378709376614472975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969956252472917742981983 8954934378709376614472975)
            ·
              refine ⟨13432401568064064921709463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954934378709376614472975 13432401568064064921709463)
              ·
                refine ⟨20148602352096097382564195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13432401568064064921709463 20148602352096097382564195)
                ·
                  refine ⟨30222903528144146073846293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20148602352096097382564195 30222903528144146073846293)
                  ·
                    refine ⟨1416698602881756847211545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30222903528144146073846293 1416698602881756847211545)
                    ·
                      rfl

theorem cell22_4138516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4138516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138516 prefixEnd_4138516 := by exact prefixLift 4138516
  have htrace : WordTrace (prefixWord ++ tailWord_4138516) baseStart_4138516 baseEnd_4138516 := by
    simpa [prefixWord, tailWord_4138516, baseEnd_4138516] using wordTrace_append hprefix tailTrace_4138516
  have hstable : (prefixWord ++ tailWord_4138516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138516).length < 2 ^ (prefixWord ++ tailWord_4138516).sum := by decide
  have hdescent : baseEnd_4138516 < baseStart_4138516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138728 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_4138728 : Nat := 118140960795 + 4138728 * 2 ^ 59
def prefixEnd_4138728 : Nat := 4983230072969 + 3 ^ 40 * 4138728 * 2
def baseEnd_4138728 : Nat := 472257058271419653636965

theorem tailTrace_4138728 : CollatzResearch.WordTrace tailWord_4138728 prefixEnd_4138728 472257058271419653636965 := by
  unfold tailWord_4138728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475905675051384656612419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100634540900068512875483225 75475905675051384656612419)
  ·
    refine ⟨113213858512577076984918629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75475905675051384656612419 113213858512577076984918629)
    ·
      refine ⟨21227598471108201934672243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113213858512577076984918629 21227598471108201934672243)
      ·
        refine ⟨31841397706662302902008365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227598471108201934672243 31841397706662302902008365)
        ·
          refine ⟨11940524139998363588253137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31841397706662302902008365 11940524139998363588253137)
          ·
            refine ⟨8955393104998772691189853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940524139998363588253137 8955393104998772691189853)
            ·
              refine ⟨3358272414374539759196195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8955393104998772691189853 3358272414374539759196195)
              ·
                refine ⟨5037408621561809638794293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358272414374539759196195 5037408621561809638794293)
                ·
                  refine ⟨472257058271419653636965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037408621561809638794293 472257058271419653636965)
                  ·
                    rfl

theorem cell22_4138728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_4138728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138728 prefixEnd_4138728 := by exact prefixLift 4138728
  have htrace : WordTrace (prefixWord ++ tailWord_4138728) baseStart_4138728 baseEnd_4138728 := by
    simpa [prefixWord, tailWord_4138728, baseEnd_4138728] using wordTrace_append hprefix tailTrace_4138728
  have hstable : (prefixWord ++ tailWord_4138728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138728).length < 2 ^ (prefixWord ++ tailWord_4138728).sum := by decide
  have hdescent : baseEnd_4138728 < baseStart_4138728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138739 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 6]
def baseStart_4138739 : Nat := 118140960795 + 4138739 * 2 ^ 59
def prefixEnd_4138739 : Nat := 4983230072969 + 3 ^ 40 * 4138739 * 2
def baseEnd_4138739 : Nat := 472258313446352866295287

theorem tailTrace_4138739 : CollatzResearch.WordTrace tailWord_4138739 prefixEnd_4138739 472258313446352866295287 := by
  unfold tailWord_4138739
  simp only [CollatzResearch.WordTrace]
  refine ⟨150952212553062918191875271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100634808368708612127916847 150952212553062918191875271)
  ·
    refine ⟨226428318829594377287812907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150952212553062918191875271 226428318829594377287812907)
    ·
      refine ⟨339642478244391565931719361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226428318829594377287812907 339642478244391565931719361)
      ·
        refine ⟨254731858683293674448789521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339642478244391565931719361 254731858683293674448789521)
        ·
          refine ⟨191048894012470255836592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254731858683293674448789521 191048894012470255836592141)
          ·
            refine ⟨71643335254676345938722053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191048894012470255836592141 71643335254676345938722053)
            ·
              refine ⟨13433125360251814863510385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71643335254676345938722053 13433125360251814863510385)
              ·
                refine ⟨10074844020188861147632789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433125360251814863510385 10074844020188861147632789)
                ·
                  refine ⟨472258313446352866295287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10074844020188861147632789 472258313446352866295287)
                  ·
                    rfl

theorem cell22_4138739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_4138739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138739 prefixEnd_4138739 := by exact prefixLift 4138739
  have htrace : WordTrace (prefixWord ++ tailWord_4138739) baseStart_4138739 baseEnd_4138739 := by
    simpa [prefixWord, tailWord_4138739, baseEnd_4138739] using wordTrace_append hprefix tailTrace_4138739
  have hstable : (prefixWord ++ tailWord_4138739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138739).length < 2 ^ (prefixWord ++ tailWord_4138739).sum := by decide
  have hdescent : baseEnd_4138739 < baseStart_4138739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138786 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4138786 : Nat := 118140960795 + 4138786 * 2 ^ 59
def prefixEnd_4138786 : Nat := 4983230072969 + 3 ^ 40 * 4138786 * 2
def baseEnd_4138786 : Nat := 1416791029399566142960717

theorem tailTrace_4138786 : CollatzResearch.WordTrace tailWord_4138786 prefixEnd_4138786 1416791029399566142960717 := by
  unfold tailWord_4138786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37738481695973161304709053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100635951189261763479224141 37738481695973161304709053)
  ·
    refine ⟨14151930635989935489265895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37738481695973161304709053 14151930635989935489265895)
    ·
      refine ⟨21227895953984903233898843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14151930635989935489265895 21227895953984903233898843)
      ·
        refine ⟨31841843930977354850848265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227895953984903233898843 31841843930977354850848265)
        ·
          refine ⟨23881382948233016138136199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31841843930977354850848265 23881382948233016138136199)
          ·
            refine ⟨35822074422349524207204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23881382948233016138136199 35822074422349524207204299)
            ·
              refine ⟨53733111633524286310806449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35822074422349524207204299 53733111633524286310806449)
              ·
                refine ⟨40299833725143214733104837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53733111633524286310806449 40299833725143214733104837)
                ·
                  refine ⟨7556218823464352762457157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40299833725143214733104837 7556218823464352762457157)
                  ·
                    refine ⟨1416791029399566142960717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556218823464352762457157 1416791029399566142960717)
                    ·
                      rfl

theorem cell22_4138786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4138786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138786 prefixEnd_4138786 := by exact prefixLift 4138786
  have htrace : WordTrace (prefixWord ++ tailWord_4138786) baseStart_4138786 baseEnd_4138786 := by
    simpa [prefixWord, tailWord_4138786, baseEnd_4138786] using wordTrace_append hprefix tailTrace_4138786
  have hstable : (prefixWord ++ tailWord_4138786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138786).length < 2 ^ (prefixWord ++ tailWord_4138786).sum := by decide
  have hdescent : baseEnd_4138786 < baseStart_4138786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138803 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 2, 4]
def baseStart_4138803 : Nat := 118140960795 + 4138803 * 2 ^ 59
def prefixEnd_4138803 : Nat := 4983230072969 + 3 ^ 40 * 4138803 * 2
def baseEnd_4138803 : Nat := 1416796848846983765285665

theorem tailTrace_4138803 : CollatzResearch.WordTrace tailWord_4138803 prefixEnd_4138803 1416796848846983765285665 := by
  unfold tailWord_4138803
  simp only [CollatzResearch.WordTrace]
  refine ⟨150954546824831057122205063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100636364549887371414803375 150954546824831057122205063)
  ·
    refine ⟨226431820237246585683307595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150954546824831057122205063 226431820237246585683307595)
    ·
      refine ⟨339647730355869878524961393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226431820237246585683307595 339647730355869878524961393)
      ·
        refine ⟨254735797766902408893721045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339647730355869878524961393 254735797766902408893721045)
        ·
          refine ⟨5970370260161775208446587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254735797766902408893721045 5970370260161775208446587)
          ·
            refine ⟨8955555390242662812669881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970370260161775208446587 8955555390242662812669881)
            ·
              refine ⟨6716666542681997109502411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955555390242662812669881 6716666542681997109502411)
              ·
                refine ⟨10074999814022995664253617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716666542681997109502411 10074999814022995664253617)
                ·
                  refine ⟨7556249860517246748190213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074999814022995664253617 7556249860517246748190213)
                  ·
                    refine ⟨1416796848846983765285665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556249860517246748190213 1416796848846983765285665)
                    ·
                      rfl

theorem cell22_4138803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_4138803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138803 prefixEnd_4138803 := by exact prefixLift 4138803
  have htrace : WordTrace (prefixWord ++ tailWord_4138803) baseStart_4138803 baseEnd_4138803 := by
    simpa [prefixWord, tailWord_4138803, baseEnd_4138803] using wordTrace_append hprefix tailTrace_4138803
  have hstable : (prefixWord ++ tailWord_4138803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138803).length < 2 ^ (prefixWord ++ tailWord_4138803).sum := by decide
  have hdescent : baseEnd_4138803 < baseStart_4138803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138822 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4138822 : Nat := 118140960795 + 4138822 * 2 ^ 59
def prefixEnd_4138822 : Nat := 4983230072969 + 3 ^ 40 * 4138822 * 2
def baseEnd_4138822 : Nat := 1416803352935274049060607

theorem tailTrace_4138822 : CollatzResearch.WordTrace tailWord_4138822 prefixEnd_4138822 1416803352935274049060607 := by
  unfold tailWord_4138822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717351244117569480223335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100636826541174815578097813 4717351244117569480223335)
  ·
    refine ⟨7076026866176354220335003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717351244117569480223335 7076026866176354220335003)
    ·
      refine ⟨10614040299264531330502505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076026866176354220335003 10614040299264531330502505)
      ·
        refine ⟨7960530224448398497876879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10614040299264531330502505 7960530224448398497876879)
        ·
          refine ⟨11940795336672597746815319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960530224448398497876879 11940795336672597746815319)
          ·
            refine ⟨17911193005008896620222979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940795336672597746815319 17911193005008896620222979)
            ·
              refine ⟨26866789507513344930334469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17911193005008896620222979 26866789507513344930334469)
              ·
                refine ⟨5037523032658752174437713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26866789507513344930334469 5037523032658752174437713)
                ·
                  refine ⟨3778142274494064130828285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037523032658752174437713 3778142274494064130828285)
                  ·
                    refine ⟨1416803352935274049060607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778142274494064130828285 1416803352935274049060607)
                    ·
                      rfl

theorem cell22_4138822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4138822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138822 prefixEnd_4138822 := by exact prefixLift 4138822
  have htrace : WordTrace (prefixWord ++ tailWord_4138822) baseStart_4138822 baseEnd_4138822 := by
    simpa [prefixWord, tailWord_4138822, baseEnd_4138822] using wordTrace_append hprefix tailTrace_4138822
  have hstable : (prefixWord ++ tailWord_4138822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138822).length < 2 ^ (prefixWord ++ tailWord_4138822).sum := by decide
  have hdescent : baseEnd_4138822 < baseStart_4138822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138850 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4138850 : Nat := 118140960795 + 4138850 * 2 ^ 59
def prefixEnd_4138850 : Nat := 4983230072969 + 3 ^ 40 * 4138850 * 2
def baseEnd_4138850 : Nat := 1416812937907491309360521

theorem tailTrace_4138850 : CollatzResearch.WordTrace tailWord_4138850 prefixEnd_4138850 1416812937907491309360521 := by
  unfold tailWord_4138850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37739065263915196037291501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100637507370440522766110669 37739065263915196037291501)
  ·
    refine ⟨14152149473968198513984313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37739065263915196037291501 14152149473968198513984313)
    ·
      refine ⟨10614112105476148885488235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14152149473968198513984313 10614112105476148885488235)
      ·
        refine ⟨15921168158214223328232353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614112105476148885488235 15921168158214223328232353)
        ·
          refine ⟨11940876118660667496174265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15921168158214223328232353 11940876118660667496174265)
          ·
            refine ⟨8955657088995500622130699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940876118660667496174265 8955657088995500622130699)
            ·
              refine ⟨13433485633493250933196049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955657088995500622130699 13433485633493250933196049)
              ·
                refine ⟨10075114225119938199897037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433485633493250933196049 10075114225119938199897037)
                ·
                  refine ⟨3778167834419976824961389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10075114225119938199897037 3778167834419976824961389)
                  ·
                    refine ⟨1416812937907491309360521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778167834419976824961389 1416812937907491309360521)
                    ·
                      rfl

theorem cell22_4138850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4138850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138850 prefixEnd_4138850 := by exact prefixLift 4138850
  have htrace : WordTrace (prefixWord ++ tailWord_4138850) baseStart_4138850 baseEnd_4138850 := by
    simpa [prefixWord, tailWord_4138850, baseEnd_4138850] using wordTrace_append hprefix tailTrace_4138850
  have hstable : (prefixWord ++ tailWord_4138850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138850).length < 2 ^ (prefixWord ++ tailWord_4138850).sum := by decide
  have hdescent : baseEnd_4138850 < baseStart_4138850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138908 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_4138908 : Nat := 118140960795 + 4138908 * 2 ^ 59
def prefixEnd_4138908 : Nat := 4983230072969 + 3 ^ 40 * 4138908 * 2
def baseEnd_4138908 : Nat := 472277597497599497136781

theorem tailTrace_4138908 : CollatzResearch.WordTrace tailWord_4138908 prefixEnd_4138908 472277597497599497136781 := by
  unfold tailWord_4138908
  simp only [CollatzResearch.WordTrace]
  refine ⟨75479188244725330027388689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100638917659633773369851585 75479188244725330027388689)
  ·
    refine ⟨56609391183543997520541517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75479188244725330027388689 56609391183543997520541517)
    ·
      refine ⟨21228521693828999070203069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56609391183543997520541517 21228521693828999070203069)
      ·
        refine ⟨7960695635185874651326151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21228521693828999070203069 7960695635185874651326151)
        ·
          refine ⟨11941043452778811976989227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960695635185874651326151 11941043452778811976989227)
          ·
            refine ⟨17911565179168217965483841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941043452778811976989227 17911565179168217965483841)
            ·
              refine ⟨13433673884376163474112881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17911565179168217965483841 13433673884376163474112881)
              ·
                refine ⟨10075255413282122605584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433673884376163474112881 10075255413282122605584661)
                ·
                  refine ⟨472277597497599497136781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10075255413282122605584661 472277597497599497136781)
                  ·
                    rfl

theorem cell22_4138908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_4138908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138908 prefixEnd_4138908 := by exact prefixLift 4138908
  have htrace : WordTrace (prefixWord ++ tailWord_4138908) baseStart_4138908 baseEnd_4138908 := by
    simpa [prefixWord, tailWord_4138908, baseEnd_4138908] using wordTrace_append hprefix tailTrace_4138908
  have hstable : (prefixWord ++ tailWord_4138908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138908).length < 2 ^ (prefixWord ++ tailWord_4138908).sum := by decide
  have hdescent : baseEnd_4138908 < baseStart_4138908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138942 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4138942 : Nat := 118140960795 + 4138942 * 2 ^ 59
def prefixEnd_4138942 : Nat := 4983230072969 + 3 ^ 40 * 4138942 * 2
def baseEnd_4138942 : Nat := 472281477129211245353413

theorem tailTrace_4138942 : CollatzResearch.WordTrace tailWord_4138942 prefixEnd_4138942 472281477129211245353413 := by
  unfold tailWord_4138942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18869952071415935482689385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100639744380884989241010053 18869952071415935482689385)
  ·
    refine ⟨14152464053561951612017039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18869952071415935482689385 14152464053561951612017039)
    ·
      refine ⟨21228696080342927418025559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14152464053561951612017039 21228696080342927418025559)
      ·
        refine ⟨31843044120514391127038339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21228696080342927418025559 31843044120514391127038339)
        ·
          refine ⟨47764566180771586690557509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31843044120514391127038339 47764566180771586690557509)
          ·
            refine ⟨8955856158894672504479533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47764566180771586690557509 8955856158894672504479533)
            ·
              refine ⟨3358446059585502189179825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8955856158894672504479533 3358446059585502189179825)
              ·
                refine ⟨2518834544689126641884869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358446059585502189179825 2518834544689126641884869)
                ·
                  refine ⟨472281477129211245353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518834544689126641884869 472281477129211245353413)
                  ·
                    rfl

theorem cell22_4138942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4138942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138942 prefixEnd_4138942 := by exact prefixLift 4138942
  have htrace : WordTrace (prefixWord ++ tailWord_4138942) baseStart_4138942 baseEnd_4138942 := by
    simpa [prefixWord, tailWord_4138942, baseEnd_4138942] using wordTrace_append hprefix tailTrace_4138942
  have hstable : (prefixWord ++ tailWord_4138942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138942).length < 2 ^ (prefixWord ++ tailWord_4138942).sum := by decide
  have hdescent : baseEnd_4138942 < baseStart_4138942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4138968 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_4138968 : Nat := 118140960795 + 4138968 * 2 ^ 59
def prefixEnd_4138968 : Nat := 4983230072969 + 3 ^ 40 * 4138968 * 2
def baseEnd_4138968 : Nat := 1416853331718978334910159

theorem tailTrace_4138968 : CollatzResearch.WordTrace tailWord_4138968 prefixEnd_4138968 1416853331718978334910159 := by
  unfold tailWord_4138968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75480282434616645150980779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100640376579488860201307705 75480282434616645150980779)
  ·
    refine ⟨113220423651924967726471169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75480282434616645150980779 113220423651924967726471169)
    ·
      refine ⟨84915317738943725794853377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113220423651924967726471169 84915317738943725794853377)
      ·
        refine ⟨63686488304207794346140033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84915317738943725794853377 63686488304207794346140033)
        ·
          refine ⟨47764866228155845759605025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63686488304207794346140033 47764866228155845759605025)
          ·
            refine ⟨35823649671116884319703769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47764866228155845759605025 35823649671116884319703769)
            ·
              refine ⟨26867737253337663239777827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35823649671116884319703769 26867737253337663239777827)
              ·
                refine ⟨40301605880006494859666741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26867737253337663239777827 40301605880006494859666741)
                ·
                  refine ⟨3778275551250608893093757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40301605880006494859666741 3778275551250608893093757)
                  ·
                    refine ⟨1416853331718978334910159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778275551250608893093757 1416853331718978334910159)
                    ·
                      rfl

theorem cell22_4138968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_4138968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4138968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4138968 prefixEnd_4138968 := by exact prefixLift 4138968
  have htrace : WordTrace (prefixWord ++ tailWord_4138968) baseStart_4138968 baseEnd_4138968 := by
    simpa [prefixWord, tailWord_4138968, baseEnd_4138968] using wordTrace_append hprefix tailTrace_4138968
  have hstable : (prefixWord ++ tailWord_4138968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4138968).length < 2 ^ (prefixWord ++ tailWord_4138968).sum := by decide
  have hdescent : baseEnd_4138968 < baseStart_4138968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4138968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139013 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4139013 : Nat := 118140960795 + 4139013 * 2 ^ 59
def prefixEnd_4139013 : Nat := 4983230072969 + 3 ^ 40 * 4139013 * 2
def baseEnd_4139013 : Nat := 1416868736138613217535021

theorem tailTrace_4139013 : CollatzResearch.WordTrace tailWord_4139013 prefixEnd_4139013 1416868736138613217535021 := by
  unfold tailWord_4139013
  simp only [CollatzResearch.WordTrace]
  refine ⟨150962206154070262987349693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100641470769380175324899795 150962206154070262987349693)
  ·
    refine ⟨56610827307776348620256135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150962206154070262987349693 56610827307776348620256135)
    ·
      refine ⟨84916240961664522930384203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56610827307776348620256135 84916240961664522930384203)
      ·
        refine ⟨127374361442496784395576305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84916240961664522930384203 127374361442496784395576305)
        ·
          refine ⟨95530771081872588296682229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127374361442496784395576305 95530771081872588296682229)
          ·
            refine ⟨8956009788925555152813959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95530771081872588296682229 8956009788925555152813959)
            ·
              refine ⟨13434014683388332729220939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956009788925555152813959 13434014683388332729220939)
              ·
                refine ⟨20151022025082499093831409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434014683388332729220939 20151022025082499093831409)
                ·
                  refine ⟨15113266518811874320373557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20151022025082499093831409 15113266518811874320373557)
                  ·
                    refine ⟨1416868736138613217535021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15113266518811874320373557 1416868736138613217535021)
                    ·
                      rfl

theorem cell22_4139013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4139013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139013 prefixEnd_4139013 := by exact prefixLift 4139013
  have htrace : WordTrace (prefixWord ++ tailWord_4139013) baseStart_4139013 baseEnd_4139013 := by
    simpa [prefixWord, tailWord_4139013, baseEnd_4139013] using wordTrace_append hprefix tailTrace_4139013
  have hstable : (prefixWord ++ tailWord_4139013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139013).length < 2 ^ (prefixWord ++ tailWord_4139013).sum := by decide
  have hdescent : baseEnd_4139013 < baseStart_4139013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139045 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_4139045 : Nat := 118140960795 + 4139045 * 2 ^ 59
def prefixEnd_4139045 : Nat := 4983230072969 + 3 ^ 40 * 4139045 * 2
def baseEnd_4139045 : Nat := 1416879690392575800734923

theorem tailTrace_4139045 : CollatzResearch.WordTrace tailWord_4139045 prefixEnd_4139045 1416879690392575800734923 := by
  unfold tailWord_4139045
  simp only [CollatzResearch.WordTrace]
  refine ⟨150963373289954332452514589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100642248859969554968343059 150963373289954332452514589)
  ·
    refine ⟨56611264983732874669692971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150963373289954332452514589 56611264983732874669692971)
    ·
      refine ⟨84916897475599312004539457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56611264983732874669692971 84916897475599312004539457)
      ·
        refine ⟨63687673106699484003404593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84916897475599312004539457 63687673106699484003404593)
        ·
          refine ⟨47765754830024613002553445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63687673106699484003404593 47765754830024613002553445)
          ·
            refine ⟨8956079030629614937978771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47765754830024613002553445 8956079030629614937978771)
            ·
              refine ⟨13434118545944422406968157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956079030629614937978771 13434118545944422406968157)
              ·
                refine ⟨5037794454729158402613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13434118545944422406968157 5037794454729158402613059)
                ·
                  refine ⟨7556691682093737603919589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037794454729158402613059 7556691682093737603919589)
                  ·
                    refine ⟨1416879690392575800734923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7556691682093737603919589 1416879690392575800734923)
                    ·
                      rfl

theorem cell22_4139045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_4139045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139045 prefixEnd_4139045 := by exact prefixLift 4139045
  have htrace : WordTrace (prefixWord ++ tailWord_4139045) baseStart_4139045 baseEnd_4139045 := by
    simpa [prefixWord, tailWord_4139045, baseEnd_4139045] using wordTrace_append hprefix tailTrace_4139045
  have hstable : (prefixWord ++ tailWord_4139045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139045).length < 2 ^ (prefixWord ++ tailWord_4139045).sum := by decide
  have hdescent : baseEnd_4139045 < baseStart_4139045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139126 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_4139126 : Nat := 118140960795 + 4139126 * 2 ^ 59
def prefixEnd_4139126 : Nat := 4983230072969 + 3 ^ 40 * 4139126 * 2
def baseEnd_4139126 : Nat := 1416907418347918589459675

theorem tailTrace_4139126 : CollatzResearch.WordTrace tailWord_4139126 prefixEnd_4139126 1416907418347918589459675 := by
  unfold tailWord_4139126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435395475166305205388327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100644218401773922190808821 9435395475166305205388327)
  ·
    refine ⟨14153093212749457808082491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9435395475166305205388327 14153093212749457808082491)
    ·
      refine ⟨21229639819124186712123737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153093212749457808082491 21229639819124186712123737)
      ·
        refine ⟨15922229864343140034092803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21229639819124186712123737 15922229864343140034092803)
        ·
          refine ⟨23883344796514710051139205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922229864343140034092803 23883344796514710051139205)
          ·
            refine ⟨4478127149346508134588601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23883344796514710051139205 4478127149346508134588601)
            ·
              refine ⟨3358595362009881100941451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478127149346508134588601 3358595362009881100941451)
              ·
                refine ⟨5037893043014821651412177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358595362009881100941451 5037893043014821651412177)
                ·
                  refine ⟨3778419782261116238559133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037893043014821651412177 3778419782261116238559133)
                  ·
                    refine ⟨1416907418347918589459675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778419782261116238559133 1416907418347918589459675)
                    ·
                      rfl

theorem cell22_4139126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_4139126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139126 prefixEnd_4139126 := by exact prefixLift 4139126
  have htrace : WordTrace (prefixWord ++ tailWord_4139126) baseStart_4139126 baseEnd_4139126 := by
    simpa [prefixWord, tailWord_4139126, baseEnd_4139126] using wordTrace_append hprefix tailTrace_4139126
  have hstable : (prefixWord ++ tailWord_4139126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139126).length < 2 ^ (prefixWord ++ tailWord_4139126).sum := by decide
  have hdescent : baseEnd_4139126 < baseStart_4139126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139148 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_4139148 : Nat := 118140960795 + 4139148 * 2 ^ 59
def prefixEnd_4139148 : Nat := 4983230072969 + 3 ^ 40 * 4139148 * 2
def baseEnd_4139148 : Nat := 1416914949397517865409607

theorem tailTrace_4139148 : CollatzResearch.WordTrace tailWord_4139148 prefixEnd_4139148 1416914949397517865409607 := by
  unfold tailWord_4139148
  simp only [CollatzResearch.WordTrace]
  refine ⟨75483565004290590521757049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100644753339054120695676065 75483565004290590521757049)
  ·
    refine ⟨56612673753217942891317787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75483565004290590521757049 56612673753217942891317787)
    ·
      refine ⟨84919010629826914336976681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56612673753217942891317787 84919010629826914336976681)
      ·
        refine ⟨63689257972370185752732511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84919010629826914336976681 63689257972370185752732511)
        ·
          refine ⟨95533886958555278629098767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63689257972370185752732511 95533886958555278629098767)
          ·
            refine ⟨143300830437832917943648151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95533886958555278629098767 143300830437832917943648151)
            ·
              refine ⟨214951245656749376915472227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143300830437832917943648151 214951245656749376915472227)
              ·
                refine ⟨322426868485124065373208341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214951245656749376915472227 322426868485124065373208341)
                ·
                  refine ⟨15113759460240190564369141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322426868485124065373208341 15113759460240190564369141)
                  ·
                    refine ⟨1416914949397517865409607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15113759460240190564369141 1416914949397517865409607)
                    ·
                      rfl

theorem cell22_4139148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_4139148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139148 prefixEnd_4139148 := by exact prefixLift 4139148
  have htrace : WordTrace (prefixWord ++ tailWord_4139148) baseStart_4139148 baseEnd_4139148 := by
    simpa [prefixWord, tailWord_4139148, baseEnd_4139148] using wordTrace_append hprefix tailTrace_4139148
  have hstable : (prefixWord ++ tailWord_4139148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139148).length < 2 ^ (prefixWord ++ tailWord_4139148).sum := by decide
  have hdescent : baseEnd_4139148 < baseStart_4139148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139154 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_4139154 : Nat := 118140960795 + 4139154 * 2 ^ 59
def prefixEnd_4139154 : Nat := 4983230072969 + 3 ^ 40 * 4139154 * 2
def baseEnd_4139154 : Nat := 1416917003320135849759589

theorem tailTrace_4139154 : CollatzResearch.WordTrace tailWord_4139154 prefixEnd_4139154 1416917003320135849759589 := by
  unfold tailWord_4139154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37741837211639861017058129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100644899231039629378821677 37741837211639861017058129)
  ·
    refine ⟨28306377908729895762793597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37741837211639861017058129 28306377908729895762793597)
    ·
      refine ⟨10614891715773710911047599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28306377908729895762793597 10614891715773710911047599)
      ·
        refine ⟨15922337573660566366571399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614891715773710911047599 15922337573660566366571399)
        ·
          refine ⟨23883506360490849549857099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922337573660566366571399 23883506360490849549857099)
          ·
            refine ⟨35825259540736274324785649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23883506360490849549857099 35825259540736274324785649)
            ·
              refine ⟨26868944655552205743589237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35825259540736274324785649 26868944655552205743589237)
              ·
                refine ⟨2518963561458019288461491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26868944655552205743589237 2518963561458019288461491)
                ·
                  refine ⟨3778445342187028932692237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518963561458019288461491 3778445342187028932692237)
                  ·
                    refine ⟨1416917003320135849759589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778445342187028932692237 1416917003320135849759589)
                    ·
                      rfl

theorem cell22_4139154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_4139154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139154 prefixEnd_4139154 := by exact prefixLift 4139154
  have htrace : WordTrace (prefixWord ++ tailWord_4139154) baseStart_4139154 baseEnd_4139154 := by
    simpa [prefixWord, tailWord_4139154, baseEnd_4139154] using wordTrace_append hprefix tailTrace_4139154
  have hstable : (prefixWord ++ tailWord_4139154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139154).length < 2 ^ (prefixWord ++ tailWord_4139154).sum := by decide
  have hdescent : baseEnd_4139154 < baseStart_4139154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139167 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 5]
def baseStart_4139167 : Nat := 118140960795 + 4139167 * 2 ^ 59
def prefixEnd_4139167 : Nat := 4983230072969 + 3 ^ 40 * 4139167 * 2
def baseEnd_4139167 : Nat := 472307151161936049728183

theorem tailTrace_4139167 : CollatzResearch.WordTrace tailWord_4139167 prefixEnd_4139167 472307151161936049728183 := by
  unfold tailWord_4139167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150967822995512347288455755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100645215330341564858970503 150967822995512347288455755)
  ·
    refine ⟨226451734493268520932683633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150967822995512347288455755 226451734493268520932683633)
    ·
      refine ⟨169838800869951390699512725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226451734493268520932683633 169838800869951390699512725)
      ·
        refine ⟨7961193790778971439039659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169838800869951390699512725 7961193790778971439039659)
        ·
          refine ⟨11941790686168457158559489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961193790778971439039659 11941790686168457158559489)
          ·
            refine ⟨8956343014626342868919617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11941790686168457158559489 8956343014626342868919617)
            ·
              refine ⟨6717257260969757151689713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8956343014626342868919617 6717257260969757151689713)
              ·
                refine ⟨5037942945727317863767285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717257260969757151689713 5037942945727317863767285)
                ·
                  refine ⟨472307151161936049728183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037942945727317863767285 472307151161936049728183)
                  ·
                    rfl

theorem cell22_4139167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 5].length) (baseStart_4139167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139167 prefixEnd_4139167 := by exact prefixLift 4139167
  have htrace : WordTrace (prefixWord ++ tailWord_4139167) baseStart_4139167 baseEnd_4139167 := by
    simpa [prefixWord, tailWord_4139167, baseEnd_4139167] using wordTrace_append hprefix tailTrace_4139167
  have hstable : (prefixWord ++ tailWord_4139167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139167).length < 2 ^ (prefixWord ++ tailWord_4139167).sum := by decide
  have hdescent : baseEnd_4139167 < baseStart_4139167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139188 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4139188 : Nat := 118140960795 + 4139188 * 2 ^ 59
def prefixEnd_4139188 : Nat := 4983230072969 + 3 ^ 40 * 4139188 * 2
def baseEnd_4139188 : Nat := 1416928642214971094409485

theorem tailTrace_4139188 : CollatzResearch.WordTrace tailWord_4139188 prefixEnd_4139188 1416928642214971094409485 := by
  unfold tailWord_4139188
  simp only [CollatzResearch.WordTrace]
  refine ⟨75484294464218133937485109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100645725952290845249980145 75484294464218133937485109)
  ·
    refine ⟨7076652606020450056639229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75484294464218133937485109 7076652606020450056639229)
    ·
      refine ⟨2653744727257668771239711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7076652606020450056639229 2653744727257668771239711)
      ·
        refine ⟨3980617090886503156859567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653744727257668771239711 3980617090886503156859567)
        ·
          refine ⟨5970925636329754735289351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980617090886503156859567 5970925636329754735289351)
          ·
            refine ⟨8956388454494632102934027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970925636329754735289351 8956388454494632102934027)
            ·
              refine ⟨13434582681741948154401041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956388454494632102934027 13434582681741948154401041)
              ·
                refine ⟨10075937011306461115800781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13434582681741948154401041 10075937011306461115800781)
                ·
                  refine ⟨3778476379239922918425293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10075937011306461115800781 3778476379239922918425293)
                  ·
                    refine ⟨1416928642214971094409485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778476379239922918425293 1416928642214971094409485)
                    ·
                      rfl

theorem cell22_4139188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4139188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139188 prefixEnd_4139188 := by exact prefixLift 4139188
  have htrace : WordTrace (prefixWord ++ tailWord_4139188) baseStart_4139188 baseEnd_4139188 := by
    simpa [prefixWord, tailWord_4139188, baseEnd_4139188] using wordTrace_append hprefix tailTrace_4139188
  have hstable : (prefixWord ++ tailWord_4139188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139188).length < 2 ^ (prefixWord ++ tailWord_4139188).sum := by decide
  have hdescent : baseEnd_4139188 < baseStart_4139188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139210 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4139210 : Nat := 118140960795 + 4139210 * 2 ^ 59
def prefixEnd_4139210 : Nat := 4983230072969 + 3 ^ 40 * 4139210 * 2
def baseEnd_4139210 : Nat := 1416936173264570370359417

theorem tailTrace_4139210 : CollatzResearch.WordTrace tailWord_4139210 prefixEnd_4139210 1416936173264570370359417 := by
  unfold tailWord_4139210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742347833589141408067771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100646260889571043754847389 37742347833589141408067771)
  ·
    refine ⟨56613521750383712112101657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37742347833589141408067771 56613521750383712112101657)
    ·
      refine ⟨42460141312787784084076243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56613521750383712112101657 42460141312787784084076243)
      ·
        refine ⟨63690211969181676126114365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42460141312787784084076243 63690211969181676126114365)
        ·
          refine ⟨23883829488443128547292887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63690211969181676126114365 23883829488443128547292887)
          ·
            refine ⟨35825744232664692820939331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23883829488443128547292887 35825744232664692820939331)
            ·
              refine ⟨53738616348997039231408997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35825744232664692820939331 53738616348997039231408997)
              ·
                refine ⟨10075990565436944855889187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53738616348997039231408997 10075990565436944855889187)
                ·
                  refine ⟨15113985848155417283833781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10075990565436944855889187 15113985848155417283833781)
                  ·
                    refine ⟨1416936173264570370359417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15113985848155417283833781 1416936173264570370359417)
                    ·
                      rfl

theorem cell22_4139210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4139210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139210 prefixEnd_4139210 := by exact prefixLift 4139210
  have htrace : WordTrace (prefixWord ++ tailWord_4139210) baseStart_4139210 baseEnd_4139210 := by
    simpa [prefixWord, tailWord_4139210, baseEnd_4139210] using wordTrace_append hprefix tailTrace_4139210
  have hstable : (prefixWord ++ tailWord_4139210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139210).length < 2 ^ (prefixWord ++ tailWord_4139210).sum := by decide
  have hdescent : baseEnd_4139210 < baseStart_4139210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139214 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_4139214 : Nat := 118140960795 + 4139214 * 2 ^ 59
def prefixEnd_4139214 : Nat := 4983230072969 + 3 ^ 40 * 4139214 * 2
def baseEnd_4139214 : Nat := 1416937542546315693259405

theorem tailTrace_4139214 : CollatzResearch.WordTrace tailWord_4139214 prefixEnd_4139214 1416937542546315693259405 := by
  unfold tailWord_4139214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871192153292759289427087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100646358150894716210277797 18871192153292759289427087)
  ·
    refine ⟨28306788229939138934140631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18871192153292759289427087 28306788229939138934140631)
    ·
      refine ⟨42460182344908708401210947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28306788229939138934140631 42460182344908708401210947)
      ·
        refine ⟨63690273517363062601816421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42460182344908708401210947 63690273517363062601816421)
        ·
          refine ⟨11941926284505574237840579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63690273517363062601816421 11941926284505574237840579)
          ·
            refine ⟨17912889426758361356760869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941926284505574237840579 17912889426758361356760869)
            ·
              refine ⟨3358666767517192754392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17912889426758361356760869 3358666767517192754392663)
              ·
                refine ⟨5038000151275789131588995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358666767517192754392663 5038000151275789131588995)
                ·
                  refine ⟨7557000226913683697383493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038000151275789131588995 7557000226913683697383493)
                  ·
                    refine ⟨1416937542546315693259405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557000226913683697383493 1416937542546315693259405)
                    ·
                      rfl

theorem cell22_4139214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_4139214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139214 prefixEnd_4139214 := by exact prefixLift 4139214
  have htrace : WordTrace (prefixWord ++ tailWord_4139214) baseStart_4139214 baseEnd_4139214 := by
    simpa [prefixWord, tailWord_4139214, baseEnd_4139214] using wordTrace_append hprefix tailTrace_4139214
  have hstable : (prefixWord ++ tailWord_4139214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139214).length < 2 ^ (prefixWord ++ tailWord_4139214).sum := by decide
  have hdescent : baseEnd_4139214 < baseStart_4139214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139225 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_4139225 : Nat := 118140960795 + 4139225 * 2 ^ 59
def prefixEnd_4139225 : Nat := 4983230072969 + 3 ^ 40 * 4139225 * 2
def baseEnd_4139225 : Nat := 1416941308071115331234371

theorem tailTrace_4139225 : CollatzResearch.WordTrace tailWord_4139225 prefixEnd_4139225 1416941308071115331234371 := by
  unfold tailWord_4139225
  simp only [CollatzResearch.WordTrace]
  refine ⟨150969938429302223194067129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100646625619534815462711419 150969938429302223194067129)
  ·
    refine ⟨113227453821976667395550347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150969938429302223194067129 113227453821976667395550347)
    ·
      refine ⟨169841180732965001093325521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113227453821976667395550347 169841180732965001093325521)
      ·
        refine ⟨127380885549723750819994141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169841180732965001093325521 127380885549723750819994141)
        ·
          refine ⟨47767832081146406557497803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127380885549723750819994141 47767832081146406557497803)
          ·
            refine ⟨71651748121719609836246705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47767832081146406557497803 71651748121719609836246705)
            ·
              refine ⟨53738811091289707377185029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71651748121719609836246705 53738811091289707377185029)
              ·
                refine ⟨10076027079616820133222193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53738811091289707377185029 10076027079616820133222193)
                ·
                  refine ⟨7557020309712615099916645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10076027079616820133222193 7557020309712615099916645)
                  ·
                    refine ⟨1416941308071115331234371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557020309712615099916645 1416941308071115331234371)
                    ·
                      rfl

theorem cell22_4139225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_4139225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139225 prefixEnd_4139225 := by exact prefixLift 4139225
  have htrace : WordTrace (prefixWord ++ tailWord_4139225) baseStart_4139225 baseEnd_4139225 := by
    simpa [prefixWord, tailWord_4139225, baseEnd_4139225] using wordTrace_append hprefix tailTrace_4139225
  have hstable : (prefixWord ++ tailWord_4139225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139225).length < 2 ^ (prefixWord ++ tailWord_4139225).sum := by decide
  have hdescent : baseEnd_4139225 < baseStart_4139225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139229 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 4]
def baseStart_4139229 : Nat := 118140960795 + 4139229 * 2 ^ 59
def prefixEnd_4139229 : Nat := 4983230072969 + 3 ^ 40 * 4139229 * 2
def baseEnd_4139229 : Nat := 472314225784286884711453

theorem tailTrace_4139229 : CollatzResearch.WordTrace tailWord_4139229 prefixEnd_4139229 472314225784286884711453 := by
  unfold tailWord_4139229
  simp only [CollatzResearch.WordTrace]
  refine ⟨150970084321287731877212741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100646722880858487918141827 150970084321287731877212741)
  ·
    refine ⟨28306890810241449726977389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150970084321287731877212741 28306890810241449726977389)
    ·
      refine ⟨10615084053840543647616521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28306890810241449726977389 10615084053840543647616521)
      ·
        refine ⟨7961313040380407735712391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10615084053840543647616521 7961313040380407735712391)
        ·
          refine ⟨11941969560570611603568587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961313040380407735712391 11941969560570611603568587)
          ·
            refine ⟨17912954340855917405352881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941969560570611603568587 17912954340855917405352881)
            ·
              refine ⟨13434715755641938054014661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17912954340855917405352881 13434715755641938054014661)
              ·
                refine ⟨2519009204182863385127749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13434715755641938054014661 2519009204182863385127749)
                ·
                  refine ⟨472314225784286884711453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519009204182863385127749 472314225784286884711453)
                  ·
                    rfl

theorem cell22_4139229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_4139229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139229 prefixEnd_4139229 := by exact prefixLift 4139229
  have htrace : WordTrace (prefixWord ++ tailWord_4139229) baseStart_4139229 baseEnd_4139229 := by
    simpa [prefixWord, tailWord_4139229, baseEnd_4139229] using wordTrace_append hprefix tailTrace_4139229
  have hstable : (prefixWord ++ tailWord_4139229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139229).length < 2 ^ (prefixWord ++ tailWord_4139229).sum := by decide
  have hdescent : baseEnd_4139229 < baseStart_4139229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139244 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_4139244 : Nat := 118140960795 + 4139244 * 2 ^ 59
def prefixEnd_4139244 : Nat := 4983230072969 + 3 ^ 40 * 4139244 * 2
def baseEnd_4139244 : Nat := 1416947812159405615009313

theorem tailTrace_4139244 : CollatzResearch.WordTrace tailWord_4139244 prefixEnd_4139244 1416947812159405615009313 := by
  unfold tailWord_4139244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75485315708116694719504393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100647087610822259626005857 75485315708116694719504393)
  ·
    refine ⟨56613986781087521039628295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75485315708116694719504393 56613986781087521039628295)
    ·
      refine ⟨84920980171631281559442443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56613986781087521039628295 84920980171631281559442443)
      ·
        refine ⟨127381470257446922339163665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84920980171631281559442443 127381470257446922339163665)
        ·
          refine ⟨95536102693085191754372749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127381470257446922339163665 95536102693085191754372749)
          ·
            refine ⟨35826038509906946907889781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95536102693085191754372749 35826038509906946907889781)
            ·
              refine ⟨3358691110303776272614667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35826038509906946907889781 3358691110303776272614667)
              ·
                refine ⟨5038036665455664408922001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358691110303776272614667 5038036665455664408922001)
                ·
                  refine ⟨3778527499091748306691501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038036665455664408922001 3778527499091748306691501)
                  ·
                    refine ⟨1416947812159405615009313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778527499091748306691501 1416947812159405615009313)
                    ·
                      rfl

theorem cell22_4139244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_4139244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139244 prefixEnd_4139244 := by exact prefixLift 4139244
  have htrace : WordTrace (prefixWord ++ tailWord_4139244) baseStart_4139244 baseEnd_4139244 := by
    simpa [prefixWord, tailWord_4139244, baseEnd_4139244] using wordTrace_append hprefix tailTrace_4139244
  have hstable : (prefixWord ++ tailWord_4139244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139244).length < 2 ^ (prefixWord ++ tailWord_4139244).sum := by decide
  have hdescent : baseEnd_4139244 < baseStart_4139244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139285 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 7]
def baseStart_4139285 : Nat := 118140960795 + 4139285 * 2 ^ 59
def prefixEnd_4139285 : Nat := 4983230072969 + 3 ^ 40 * 4139285 * 2
def baseEnd_4139285 : Nat := 472320615765765058244729

theorem tailTrace_4139285 : CollatzResearch.WordTrace tailWord_4139285 prefixEnd_4139285 472320615765765058244729 := by
  unfold tailWord_4139285
  simp only [CollatzResearch.WordTrace]
  refine ⟨150972126809084853441251309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100648084539389902294167539 150972126809084853441251309)
  ·
    refine ⟨56614547553406820040469241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150972126809084853441251309 56614547553406820040469241)
    ·
      refine ⟨42460910665055115030351931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56614547553406820040469241 42460910665055115030351931)
      ·
        refine ⟨63691365997582672545527897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42460910665055115030351931 63691365997582672545527897)
        ·
          refine ⟨47768524498187004409145923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63691365997582672545527897 47768524498187004409145923)
          ·
            refine ⟨71652786747280506613718885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47768524498187004409145923 71652786747280506613718885)
            ·
              refine ⟨13434897515115094990072291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71652786747280506613718885 13434897515115094990072291)
              ·
                refine ⟨20152346272672642485108437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13434897515115094990072291 20152346272672642485108437)
                ·
                  refine ⟨472320615765765058244729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20152346272672642485108437 472320615765765058244729)
                  ·
                    rfl

theorem cell22_4139285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_4139285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139285 prefixEnd_4139285 := by exact prefixLift 4139285
  have htrace : WordTrace (prefixWord ++ tailWord_4139285) baseStart_4139285 baseEnd_4139285 := by
    simpa [prefixWord, tailWord_4139285, baseEnd_4139285] using wordTrace_append hprefix tailTrace_4139285
  have hstable : (prefixWord ++ tailWord_4139285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139285).length < 2 ^ (prefixWord ++ tailWord_4139285).sum := by decide
  have hdescent : baseEnd_4139285 < baseStart_4139285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139381 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 4]
def baseStart_4139381 : Nat := 118140960795 + 4139381 * 2 ^ 59
def prefixEnd_4139381 : Nat := 4983230072969 + 3 ^ 40 * 4139381 * 2
def baseEnd_4139381 : Nat := 472331570019727641444631

theorem tailTrace_4139381 : CollatzResearch.WordTrace tailWord_4139381 prefixEnd_4139381 472331570019727641444631 := by
  unfold tailWord_4139381
  simp only [CollatzResearch.WordTrace]
  refine ⟨150975628216737061836745997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100650418811158041224497331 150975628216737061836745997)
  ·
    refine ⟨56615860581276398188779749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150975628216737061836745997 56615860581276398188779749)
    ·
      refine ⟨10615473858989324660396203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56615860581276398188779749 10615473858989324660396203)
      ·
        refine ⟨15923210788483986990594305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10615473858989324660396203 15923210788483986990594305)
        ·
          refine ⟨11942408091362990242945729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15923210788483986990594305 11942408091362990242945729)
          ·
            refine ⟨8956806068522242682209297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942408091362990242945729 8956806068522242682209297)
            ·
              refine ⟨6717604551391682011656973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8956806068522242682209297 6717604551391682011656973)
              ·
                refine ⟨2519101706771880754371365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6717604551391682011656973 2519101706771880754371365)
                ·
                  refine ⟨472331570019727641444631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519101706771880754371365 472331570019727641444631)
                  ·
                    rfl

theorem cell22_4139381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_4139381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139381 prefixEnd_4139381 := by exact prefixLift 4139381
  have htrace : WordTrace (prefixWord ++ tailWord_4139381) baseStart_4139381 baseEnd_4139381 := by
    simpa [prefixWord, tailWord_4139381, baseEnd_4139381] using wordTrace_append hprefix tailTrace_4139381
  have hstable : (prefixWord ++ tailWord_4139381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139381).length < 2 ^ (prefixWord ++ tailWord_4139381).sum := by decide
  have hdescent : baseEnd_4139381 < baseStart_4139381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139424 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_4139424 : Nat := 118140960795 + 4139424 * 2 ^ 59
def prefixEnd_4139424 : Nat := 4983230072969 + 3 ^ 40 * 4139424 * 2
def baseEnd_4139424 : Nat := 1417009429837945145508761

theorem tailTrace_4139424 : CollatzResearch.WordTrace tailWord_4139424 prefixEnd_4139424 1417009429837945145508761 := by
  unfold tailWord_4139424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75488598277790640090280663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100651464370387520120374217 75488598277790640090280663)
  ·
    refine ⟨113232897416685960135420995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75488598277790640090280663 113232897416685960135420995)
    ·
      refine ⟨169849346125028940203131493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113232897416685960135420995 169849346125028940203131493)
      ·
        refine ⟨31846752398442926288087155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169849346125028940203131493 31846752398442926288087155)
        ·
          refine ⟨47770128597664389432130733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846752398442926288087155 47770128597664389432130733)
          ·
            refine ⟨17913798224124146037049025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47770128597664389432130733 17913798224124146037049025)
            ·
              refine ⟨13435348668093109527786769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17913798224124146037049025 13435348668093109527786769)
              ·
                refine ⟨10076511501069832145840077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435348668093109527786769 10076511501069832145840077)
                ·
                  refine ⟨3778691812901187054690029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10076511501069832145840077 3778691812901187054690029)
                  ·
                    refine ⟨1417009429837945145508761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778691812901187054690029 1417009429837945145508761)
                    ·
                      rfl

theorem cell22_4139424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_4139424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139424 prefixEnd_4139424 := by exact prefixLift 4139424
  have htrace : WordTrace (prefixWord ++ tailWord_4139424) baseStart_4139424 baseEnd_4139424 := by
    simpa [prefixWord, tailWord_4139424, baseEnd_4139424] using wordTrace_append hprefix tailTrace_4139424
  have hstable : (prefixWord ++ tailWord_4139424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139424).length < 2 ^ (prefixWord ++ tailWord_4139424).sum := by decide
  have hdescent : baseEnd_4139424 < baseStart_4139424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139467 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 3, 4]
def baseStart_4139467 : Nat := 118140960795 + 4139467 * 2 ^ 59
def prefixEnd_4139467 : Nat := 4983230072969 + 3 ^ 40 * 4139467 * 2
def baseEnd_4139467 : Nat := 1417024149616707366683629

theorem tailTrace_4139467 : CollatzResearch.WordTrace tailWord_4139467 prefixEnd_4139467 1417024149616707366683629 := by
  unfold tailWord_4139467
  simp only [CollatzResearch.WordTrace]
  refine ⟨150978764894425498524376655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100652509929616999016251103 150978764894425498524376655)
  ·
    refine ⟨226468147341638247786564983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150978764894425498524376655 226468147341638247786564983)
    ·
      refine ⟨339702221012457371679847475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226468147341638247786564983 339702221012457371679847475)
      ·
        refine ⟨509553331518686057519771213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339702221012457371679847475 509553331518686057519771213)
        ·
          refine ⟨191082499319507271569914205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509553331518686057519771213 191082499319507271569914205)
          ·
            refine ⟨71655937244815226838717827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191082499319507271569914205 71655937244815226838717827)
            ·
              refine ⟨107483905867222840258076741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71655937244815226838717827 107483905867222840258076741)
              ·
                refine ⟨20153232350104282548389389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107483905867222840258076741 20153232350104282548389389)
                ·
                  refine ⟨7557462131289105955646021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20153232350104282548389389 7557462131289105955646021)
                  ·
                    refine ⟨1417024149616707366683629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557462131289105955646021 1417024149616707366683629)
                    ·
                      rfl

theorem cell22_4139467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_4139467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139467 prefixEnd_4139467 := by exact prefixLift 4139467
  have htrace : WordTrace (prefixWord ++ tailWord_4139467) baseStart_4139467 baseEnd_4139467 := by
    simpa [prefixWord, tailWord_4139467, baseEnd_4139467] using wordTrace_append hprefix tailTrace_4139467
  have hstable : (prefixWord ++ tailWord_4139467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139467).length < 2 ^ (prefixWord ++ tailWord_4139467).sum := by decide
  have hdescent : baseEnd_4139467 < baseStart_4139467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139482 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_4139482 : Nat := 118140960795 + 4139482 * 2 ^ 59
def prefixEnd_4139482 : Nat := 4983230072969 + 3 ^ 40 * 4139482 * 2
def baseEnd_4139482 : Nat := 472343094807750775852861

theorem tailTrace_4139482 : CollatzResearch.WordTrace tailWord_4139482 prefixEnd_4139482 472343094807750775852861 := by
  unfold tailWord_4139482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37744827997342789021543175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100652874659580770724115133 37744827997342789021543175)
  ·
    refine ⟨56617241996014183532314763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37744827997342789021543175 56617241996014183532314763)
    ·
      refine ⟨84925862994021275298472145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56617241996014183532314763 84925862994021275298472145)
      ·
        refine ⟨63694397245515956473854109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84925862994021275298472145 63694397245515956473854109)
        ·
          refine ⟨23885398967068483677695291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63694397245515956473854109 23885398967068483677695291)
          ·
            refine ⟨35828098450602725516542937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885398967068483677695291 35828098450602725516542937)
            ·
              refine ⟨26871073837952044137407203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35828098450602725516542937 26871073837952044137407203)
              ·
                refine ⟨40306610756928066206110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26871073837952044137407203 40306610756928066206110805)
                ·
                  refine ⟨472343094807750775852861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40306610756928066206110805 472343094807750775852861)
                  ·
                    rfl

theorem cell22_4139482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_4139482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139482 prefixEnd_4139482 := by exact prefixLift 4139482
  have htrace : WordTrace (prefixWord ++ tailWord_4139482) baseStart_4139482 baseEnd_4139482 := by
    simpa [prefixWord, tailWord_4139482, baseEnd_4139482] using wordTrace_append hprefix tailTrace_4139482
  have hstable : (prefixWord ++ tailWord_4139482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139482).length < 2 ^ (prefixWord ++ tailWord_4139482).sum := by decide
  have hdescent : baseEnd_4139482 < baseStart_4139482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139499 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 4]
def baseStart_4139499 : Nat := 118140960795 + 4139499 * 2 ^ 59
def prefixEnd_4139499 : Nat := 4983230072969 + 3 ^ 40 * 4139499 * 2
def baseEnd_4139499 : Nat := 472345034623556649961177

theorem tailTrace_4139499 : CollatzResearch.WordTrace tailWord_4139499 prefixEnd_4139499 472345034623556649961177 := by
  unfold tailWord_4139499
  simp only [CollatzResearch.WordTrace]
  refine ⟨150979932030309567989541551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100653288020206378659694367 150979932030309567989541551)
  ·
    refine ⟨226469898045464351984312327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150979932030309567989541551 226469898045464351984312327)
    ·
      refine ⟨339704847068196527976468491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226469898045464351984312327 339704847068196527976468491)
      ·
        refine ⟨509557270602294791964702737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339704847068196527976468491 509557270602294791964702737)
        ·
          refine ⟨382167952951721093973527053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509557270602294791964702737 382167952951721093973527053)
          ·
            refine ⟨143312982356895410240072645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382167952951721093973527053 143312982356895410240072645)
            ·
              refine ⟨26871184191917889420013621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143312982356895410240072645 26871184191917889420013621)
              ·
                refine ⟨2519173517992302133126277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26871184191917889420013621 2519173517992302133126277)
                ·
                  refine ⟨472345034623556649961177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519173517992302133126277 472345034623556649961177)
                  ·
                    rfl

theorem cell22_4139499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 4].length) (baseStart_4139499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139499 prefixEnd_4139499 := by exact prefixLift 4139499
  have htrace : WordTrace (prefixWord ++ tailWord_4139499) baseStart_4139499 baseEnd_4139499 := by
    simpa [prefixWord, tailWord_4139499, baseEnd_4139499] using wordTrace_append hprefix tailTrace_4139499
  have hstable : (prefixWord ++ tailWord_4139499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139499).length < 2 ^ (prefixWord ++ tailWord_4139499).sum := by decide
  have hdescent : baseEnd_4139499 < baseStart_4139499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139509 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4139509 : Nat := 118140960795 + 4139509 * 2 ^ 59
def prefixEnd_4139509 : Nat := 4983230072969 + 3 ^ 40 * 4139509 * 2
def baseEnd_4139509 : Nat := 1417038527075033257133501

theorem tailTrace_4139509 : CollatzResearch.WordTrace tailWord_4139509 prefixEnd_4139509 1417038527075033257133501 := by
  unfold tailWord_4139509
  simp only [CollatzResearch.WordTrace]
  refine ⟨150980296760273339697405581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100653531173515559798270387 150980296760273339697405581)
  ·
    refine ⟨56617611285102502386527093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150980296760273339697405581 56617611285102502386527093)
    ·
      refine ⟨5307901057978359598736915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56617611285102502386527093 5307901057978359598736915)
      ·
        refine ⟨7961851586967539398105373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307901057978359598736915 7961851586967539398105373)
        ·
          refine ⟨2985694345112827274289515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7961851586967539398105373 2985694345112827274289515)
          ·
            refine ⟨4478541517669240911434273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985694345112827274289515 4478541517669240911434273)
            ·
              refine ⟨3358906138251930683575705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478541517669240911434273 3358906138251930683575705)
              ·
                refine ⟨2519179603688948012681779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358906138251930683575705 2519179603688948012681779)
                ·
                  refine ⟨3778769405533422019022669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519179603688948012681779 3778769405533422019022669)
                  ·
                    refine ⟨1417038527075033257133501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778769405533422019022669 1417038527075033257133501)
                    ·
                      rfl

theorem cell22_4139509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4139509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139509 prefixEnd_4139509 := by exact prefixLift 4139509
  have htrace : WordTrace (prefixWord ++ tailWord_4139509) baseStart_4139509 baseEnd_4139509 := by
    simpa [prefixWord, tailWord_4139509, baseEnd_4139509] using wordTrace_append hprefix tailTrace_4139509
  have hstable : (prefixWord ++ tailWord_4139509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139509).length < 2 ^ (prefixWord ++ tailWord_4139509).sum := by decide
  have hdescent : baseEnd_4139509 < baseStart_4139509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139531 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 2, 3]
def baseStart_4139531 : Nat := 118140960795 + 4139531 * 2 ^ 59
def prefixEnd_4139531 : Nat := 4983230072969 + 3 ^ 40 * 4139531 * 2
def baseEnd_4139531 : Nat := 1417046058124632533083433

theorem tailTrace_4139531 : CollatzResearch.WordTrace tailWord_4139531 prefixEnd_4139531 1417046058124632533083433 := by
  unfold tailWord_4139531
  simp only [CollatzResearch.WordTrace]
  refine ⟨150981099166193637454706447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100654066110795758303137631 150981099166193637454706447)
  ·
    refine ⟨226471648749290456182059671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150981099166193637454706447 226471648749290456182059671)
    ·
      refine ⟨339707473123935684273089507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226471648749290456182059671 339707473123935684273089507)
      ·
        refine ⟨509561209685903526409634261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339707473123935684273089507 509561209685903526409634261)
        ·
          refine ⟨11942840852013363900225803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 509561209685903526409634261 11942840852013363900225803)
          ·
            refine ⟨17914261278020045850338705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942840852013363900225803 17914261278020045850338705)
            ·
              refine ⟨13435695958515034387754029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914261278020045850338705 13435695958515034387754029)
              ·
                refine ⟨5038385984443137895407761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13435695958515034387754029 5038385984443137895407761)
                ·
                  refine ⟨3778789488332353421555821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038385984443137895407761 3778789488332353421555821)
                  ·
                    refine ⟨1417046058124632533083433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778789488332353421555821 1417046058124632533083433)
                    ·
                      rfl

theorem cell22_4139531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 3].length) (baseStart_4139531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139531 prefixEnd_4139531 := by exact prefixLift 4139531
  have htrace : WordTrace (prefixWord ++ tailWord_4139531) baseStart_4139531 baseEnd_4139531 := by
    simpa [prefixWord, tailWord_4139531, baseEnd_4139531] using wordTrace_append hprefix tailTrace_4139531
  have hstable : (prefixWord ++ tailWord_4139531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139531).length < 2 ^ (prefixWord ++ tailWord_4139531).sum := by decide
  have hdescent : baseEnd_4139531 < baseStart_4139531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139533 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4139533 : Nat := 118140960795 + 4139533 * 2 ^ 59
def prefixEnd_4139533 : Nat := 4983230072969 + 3 ^ 40 * 4139533 * 2
def baseEnd_4139533 : Nat := 472348914255168398177809

theorem tailTrace_4139533 : CollatzResearch.WordTrace tailWord_4139533 prefixEnd_4139533 472348914255168398177809 := by
  unfold tailWord_4139533
  simp only [CollatzResearch.WordTrace]
  refine ⟨150981172112186391796279253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100654114741457594530852835 150981172112186391796279253)
  ·
    refine ⟨3538621221379368557725295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 150981172112186391796279253 3538621221379368557725295)
    ·
      refine ⟨5307931832069052836587943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538621221379368557725295 5307931832069052836587943)
      ·
        refine ⟨7961897748103579254881915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307931832069052836587943 7961897748103579254881915)
        ·
          refine ⟨11942846622155368882322873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961897748103579254881915 11942846622155368882322873)
          ·
            refine ⟨8957134966616526661742155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942846622155368882322873 8957134966616526661742155)
            ·
              refine ⟨13435702449924789992613233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957134966616526661742155 13435702449924789992613233)
              ·
                refine ⟨10076776837443592494459925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13435702449924789992613233 10076776837443592494459925)
                ·
                  refine ⟨472348914255168398177809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10076776837443592494459925 472348914255168398177809)
                  ·
                    rfl

theorem cell22_4139533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4139533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139533 prefixEnd_4139533 := by exact prefixLift 4139533
  have htrace : WordTrace (prefixWord ++ tailWord_4139533) baseStart_4139533 baseEnd_4139533 := by
    simpa [prefixWord, tailWord_4139533, baseEnd_4139533] using wordTrace_append hprefix tailTrace_4139533
  have hstable : (prefixWord ++ tailWord_4139533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139533).length < 2 ^ (prefixWord ++ tailWord_4139533).sum := by decide
  have hdescent : baseEnd_4139533 < baseStart_4139533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139576 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_4139576 : Nat := 118140960795 + 4139576 * 2 ^ 59
def prefixEnd_4139576 : Nat := 4983230072969 + 3 ^ 40 * 4139576 * 2
def baseEnd_4139576 : Nat := 1417061462544267415708295

theorem tailTrace_4139576 : CollatzResearch.WordTrace tailWord_4139576 prefixEnd_4139576 1417061462544267415708295 := by
  unfold tailWord_4139576
  simp only [CollatzResearch.WordTrace]
  refine ⟨75491370225515305070047291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100655160300687073426729721 75491370225515305070047291)
  ·
    refine ⟨113237055338272957605070937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75491370225515305070047291 113237055338272957605070937)
    ·
      refine ⟨84927791503704718203803203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113237055338272957605070937 84927791503704718203803203)
      ·
        refine ⟨127391687255557077305704805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84927791503704718203803203 127391687255557077305704805)
        ·
          refine ⟨23885941360416951994819651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127391687255557077305704805 23885941360416951994819651)
          ·
            refine ⟨35828912040625427992229477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885941360416951994819651 35828912040625427992229477)
            ·
              refine ⟨6717921007617267748543027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35828912040625427992229477 6717921007617267748543027)
              ·
                refine ⟨10076881511425901622814541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717921007617267748543027 10076881511425901622814541)
                ·
                  refine ⟨3778830566784713108555453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10076881511425901622814541 3778830566784713108555453)
                  ·
                    refine ⟨1417061462544267415708295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778830566784713108555453 1417061462544267415708295)
                    ·
                      rfl

theorem cell22_4139576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_4139576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139576 prefixEnd_4139576 := by exact prefixLift 4139576
  have htrace : WordTrace (prefixWord ++ tailWord_4139576) baseStart_4139576 baseEnd_4139576 := by
    simpa [prefixWord, tailWord_4139576, baseEnd_4139576] using wordTrace_append hprefix tailTrace_4139576
  have hstable : (prefixWord ++ tailWord_4139576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139576).length < 2 ^ (prefixWord ++ tailWord_4139576).sum := by decide
  have hdescent : baseEnd_4139576 < baseStart_4139576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139582 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4139582 : Nat := 118140960795 + 4139582 * 2 ^ 59
def prefixEnd_4139582 : Nat := 4983230072969 + 3 ^ 40 * 4139582 * 2
def baseEnd_4139582 : Nat := 1417063516466885400058277

theorem tailTrace_4139582 : CollatzResearch.WordTrace tailWord_4139582 prefixEnd_4139582 1417063516466885400058277 := by
  unfold tailWord_4139582
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872869911126109145601625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100655306192672582109875333 18872869911126109145601625)
  ·
    refine ⟨14154652433344581859201219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18872869911126109145601625 14154652433344581859201219)
    ·
      refine ⟨21231978650016872788801829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154652433344581859201219 21231978650016872788801829)
      ·
        refine ⟨3980995996878163647900343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21231978650016872788801829 3980995996878163647900343)
        ·
          refine ⟨5971493995317245471850515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980995996878163647900343 5971493995317245471850515)
          ·
            refine ⟨8957240992975868207775773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971493995317245471850515 8957240992975868207775773)
            ·
              refine ⟨3358965372365950577915915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8957240992975868207775773 3358965372365950577915915)
              ·
                refine ⟨5038448058548925866873873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358965372365950577915915 5038448058548925866873873)
                ·
                  refine ⟨3778836043911694400155405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038448058548925866873873 3778836043911694400155405)
                  ·
                    refine ⟨1417063516466885400058277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778836043911694400155405 1417063516466885400058277)
                    ·
                      rfl

theorem cell22_4139582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4139582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139582 prefixEnd_4139582 := by exact prefixLift 4139582
  have htrace : WordTrace (prefixWord ++ tailWord_4139582) baseStart_4139582 baseEnd_4139582 := by
    simpa [prefixWord, tailWord_4139582, baseEnd_4139582] using wordTrace_append hprefix tailTrace_4139582
  have hstable : (prefixWord ++ tailWord_4139582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139582).length < 2 ^ (prefixWord ++ tailWord_4139582).sum := by decide
  have hdescent : baseEnd_4139582 < baseStart_4139582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139653 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_4139653 : Nat := 118140960795 + 4139653 * 2 ^ 59
def prefixEnd_4139653 : Nat := 4983230072969 + 3 ^ 40 * 4139653 * 2
def baseEnd_4139653 : Nat := 1417087821217864881533059

theorem tailTrace_4139653 : CollatzResearch.WordTrace tailWord_4139653 prefixEnd_4139653 1417087821217864881533059 := by
  unfold tailWord_4139653
  simp only [CollatzResearch.WordTrace]
  refine ⟨150985548871751652290647613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100657032581167768193765075 150985548871751652290647613)
  ·
    refine ⟨56619580826906869608992855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150985548871751652290647613 56619580826906869608992855)
    ·
      refine ⟨84929371240360304413489283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56619580826906869608992855 84929371240360304413489283)
      ·
        refine ⟨127394056860540456620233925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84929371240360304413489283 127394056860540456620233925)
        ·
          refine ⟨23886385661351335616293861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127394056860540456620233925 23886385661351335616293861)
          ·
            refine ⟨4478697311503375428055099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23886385661351335616293861 4478697311503375428055099)
            ·
              refine ⟨6718045967255063142082649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478697311503375428055099 6718045967255063142082649)
              ·
                refine ⟨5038534475441297356561987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718045967255063142082649 5038534475441297356561987)
                ·
                  refine ⟨7557801713161946034842981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038534475441297356561987 7557801713161946034842981)
                  ·
                    refine ⟨1417087821217864881533059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557801713161946034842981 1417087821217864881533059)
                    ·
                      rfl

theorem cell22_4139653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_4139653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139653 prefixEnd_4139653 := by exact prefixLift 4139653
  have htrace : WordTrace (prefixWord ++ tailWord_4139653) baseStart_4139653 baseEnd_4139653 := by
    simpa [prefixWord, tailWord_4139653, baseEnd_4139653] using wordTrace_append hprefix tailTrace_4139653
  have hstable : (prefixWord ++ tailWord_4139653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139653).length < 2 ^ (prefixWord ++ tailWord_4139653).sum := by decide
  have hdescent : baseEnd_4139653 < baseStart_4139653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139666 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4139666 : Nat := 118140960795 + 4139666 * 2 ^ 59
def prefixEnd_4139666 : Nat := 4983230072969 + 3 ^ 40 * 4139666 * 2
def baseEnd_4139666 : Nat := 1417092271383537180958019

theorem tailTrace_4139666 : CollatzResearch.WordTrace tailWord_4139666 prefixEnd_4139666 1417092271383537180958019 := by
  unfold tailWord_4139666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37746505755176138877717713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100657348680469703673913901 37746505755176138877717713)
  ·
    refine ⟨28309879316382104158288285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37746505755176138877717713 28309879316382104158288285)
    ·
      refine ⟨10616204743643289059358107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28309879316382104158288285 10616204743643289059358107)
      ·
        refine ⟨15924307115464933589037161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616204743643289059358107 15924307115464933589037161)
        ·
          refine ⟨11943230336598700191777871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15924307115464933589037161 11943230336598700191777871)
          ·
            refine ⟨17914845504898050287666807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943230336598700191777871 17914845504898050287666807)
            ·
              refine ⟨26872268257347075431500211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914845504898050287666807 26872268257347075431500211)
              ·
                refine ⟨40308402386020613147250317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26872268257347075431500211 40308402386020613147250317)
                ·
                  refine ⟨15115650894757729930218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40308402386020613147250317 15115650894757729930218869)
                  ·
                    refine ⟨1417092271383537180958019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15115650894757729930218869 1417092271383537180958019)
                    ·
                      rfl

theorem cell22_4139666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4139666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139666 prefixEnd_4139666 := by exact prefixLift 4139666
  have htrace : WordTrace (prefixWord ++ tailWord_4139666) baseStart_4139666 baseEnd_4139666 := by
    simpa [prefixWord, tailWord_4139666, baseEnd_4139666] using wordTrace_append hprefix tailTrace_4139666
  have hstable : (prefixWord ++ tailWord_4139666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139666).length < 2 ^ (prefixWord ++ tailWord_4139666).sum := by decide
  have hdescent : baseEnd_4139666 < baseStart_4139666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139711 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 5, 3]
def baseStart_4139711 : Nat := 118140960795 + 4139711 * 2 ^ 59
def prefixEnd_4139711 : Nat := 4983230072969 + 3 ^ 40 * 4139711 * 2
def baseEnd_4139711 : Nat := 1417107675803172063582881

theorem tailTrace_4139711 : CollatzResearch.WordTrace tailWord_4139711 prefixEnd_4139711 1417107675803172063582881 := by
  unfold tailWord_4139711
  simp only [CollatzResearch.WordTrace]
  refine ⟨150987664305541528196258987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100658442870361018797505991 150987664305541528196258987)
  ·
    refine ⟨226481496458312292294388481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150987664305541528196258987 226481496458312292294388481)
    ·
      refine ⟨169861122343734219220791361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226481496458312292294388481 169861122343734219220791361)
      ·
        refine ⟨127395841757800664415593521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169861122343734219220791361 127395841757800664415593521)
        ·
          refine ⟨95546881318350498311695141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127395841757800664415593521 95546881318350498311695141)
          ·
            refine ⟨17915040247190718433442839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95546881318350498311695141 17915040247190718433442839)
            ·
              refine ⟨26872560370786077650164259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17915040247190718433442839 26872560370786077650164259)
              ·
                refine ⟨40308840556179116475246389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26872560370786077650164259 40308840556179116475246389)
                ·
                  refine ⟨3778953802141792169554349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40308840556179116475246389 3778953802141792169554349)
                  ·
                    refine ⟨1417107675803172063582881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778953802141792169554349 1417107675803172063582881)
                    ·
                      rfl

theorem cell22_4139711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_4139711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139711 prefixEnd_4139711 := by exact prefixLift 4139711
  have htrace : WordTrace (prefixWord ++ tailWord_4139711) baseStart_4139711 baseEnd_4139711 := by
    simpa [prefixWord, tailWord_4139711, baseEnd_4139711] using wordTrace_append hprefix tailTrace_4139711
  have hstable : (prefixWord ++ tailWord_4139711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139711).length < 2 ^ (prefixWord ++ tailWord_4139711).sum := by decide
  have hdescent : baseEnd_4139711 < baseStart_4139711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139745 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_4139745 : Nat := 118140960795 + 4139745 * 2 ^ 59
def prefixEnd_4139745 : Nat := 4983230072969 + 3 ^ 40 * 4139745 * 2
def baseEnd_4139745 : Nat := 1417119314698007308232777

theorem tailTrace_4139745 : CollatzResearch.WordTrace tailWord_4139745 prefixEnd_4139745 1417119314698007308232777 := by
  unfold tailWord_4139745
  simp only [CollatzResearch.WordTrace]
  refine ⟨150988904387418352002996689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100659269591612234668664459 150988904387418352002996689)
  ·
    refine ⟨113241678290563764002247517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150988904387418352002996689 113241678290563764002247517)
    ·
      refine ⟨42465629358961411500842819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113241678290563764002247517 42465629358961411500842819)
      ·
        refine ⟨63698444038442117251264229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42465629358961411500842819 63698444038442117251264229)
        ·
          refine ⟨11943458257207896984612043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63698444038442117251264229 11943458257207896984612043)
          ·
            refine ⟨17915187385811845476918065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943458257207896984612043 17915187385811845476918065)
            ·
              refine ⟨13436390539358884107688549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17915187385811845476918065 13436390539358884107688549)
              ·
                refine ⟨2519323226129790770191603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13436390539358884107688549 2519323226129790770191603)
                ·
                  refine ⟨3778984839194686155287405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519323226129790770191603 3778984839194686155287405)
                  ·
                    refine ⟨1417119314698007308232777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778984839194686155287405 1417119314698007308232777)
                    ·
                      rfl

theorem cell22_4139745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_4139745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139745 prefixEnd_4139745 := by exact prefixLift 4139745
  have htrace : WordTrace (prefixWord ++ tailWord_4139745) baseStart_4139745 baseEnd_4139745 := by
    simpa [prefixWord, tailWord_4139745, baseEnd_4139745] using wordTrace_append hprefix tailTrace_4139745
  have hstable : (prefixWord ++ tailWord_4139745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139745).length < 2 ^ (prefixWord ++ tailWord_4139745).sum := by decide
  have hdescent : baseEnd_4139745 < baseStart_4139745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139764 : List Nat := [2, 6, 1, 1, 3, 1, 2, 6]
def baseStart_4139764 : Nat := 118140960795 + 4139764 * 2 ^ 59
def prefixEnd_4139764 : Nat := 4983230072969 + 3 ^ 40 * 4139764 * 2
def baseEnd_4139764 : Nat := 157458424309588621334191

theorem tailTrace_4139764 : CollatzResearch.WordTrace tailWord_4139764 prefixEnd_4139764 157458424309588621334191 := by
  unfold tailWord_4139764
  simp only [CollatzResearch.WordTrace]
  refine ⟨75494798687174759123969173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100659731582899678831958897 75494798687174759123969173)
  ·
    refine ⟨3538818688461316833936055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75494798687174759123969173 3538818688461316833936055)
    ·
      refine ⟨5308228032691975250904083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538818688461316833936055 5308228032691975250904083)
      ·
        refine ⟨7962342049037962876356125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308228032691975250904083 7962342049037962876356125)
        ·
          refine ⟨2985878268389236078633547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7962342049037962876356125 2985878268389236078633547)
          ·
            refine ⟨4478817402583854117950321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985878268389236078633547 4478817402583854117950321)
            ·
              refine ⟨3359113051937890588462741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478817402583854117950321 3359113051937890588462741)
              ·
                refine ⟨157458424309588621334191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3359113051937890588462741 157458424309588621334191)
                ·
                  rfl

theorem cell22_4139764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_4139764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139764 prefixEnd_4139764 := by exact prefixLift 4139764
  have htrace : WordTrace (prefixWord ++ tailWord_4139764) baseStart_4139764 baseEnd_4139764 := by
    simpa [prefixWord, tailWord_4139764, baseEnd_4139764] using wordTrace_append hprefix tailTrace_4139764
  have hstable : (prefixWord ++ tailWord_4139764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139764).length < 2 ^ (prefixWord ++ tailWord_4139764).sum := by decide
  have hdescent : baseEnd_4139764 < baseStart_4139764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139822 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4139822 : Nat := 118140960795 + 4139822 * 2 ^ 59
def prefixEnd_4139822 : Nat := 4983230072969 + 3 ^ 40 * 4139822 * 2
def baseEnd_4139822 : Nat := 1417145673371604774057541

theorem tailTrace_4139822 : CollatzResearch.WordTrace tailWord_4139822 prefixEnd_4139822 1417145673371604774057541 := by
  unfold tailWord_4139822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873964101017424269193715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100661141872092929435699813 18873964101017424269193715)
  ·
    refine ⟨28310946151526136403790573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18873964101017424269193715 28310946151526136403790573)
    ·
      refine ⟨10616604806822301151421465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28310946151526136403790573 10616604806822301151421465)
      ·
        refine ⟨7962453605116725863566099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10616604806822301151421465 7962453605116725863566099)
        ·
          refine ⟨11943680407675088795349149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962453605116725863566099 11943680407675088795349149)
          ·
            refine ⟨4478880152878158298255931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11943680407675088795349149 4478880152878158298255931)
            ·
              refine ⟨6718320229317237447383897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478880152878158298255931 6718320229317237447383897)
              ·
                refine ⟨5038740171987928085537923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718320229317237447383897 5038740171987928085537923)
                ·
                  refine ⟨7558110257981892128306885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038740171987928085537923 7558110257981892128306885)
                  ·
                    refine ⟨1417145673371604774057541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558110257981892128306885 1417145673371604774057541)
                    ·
                      rfl

theorem cell22_4139822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4139822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139822 prefixEnd_4139822 := by exact prefixLift 4139822
  have htrace : WordTrace (prefixWord ++ tailWord_4139822) baseStart_4139822 baseEnd_4139822 := by
    simpa [prefixWord, tailWord_4139822, baseEnd_4139822] using wordTrace_append hprefix tailTrace_4139822
  have hstable : (prefixWord ++ tailWord_4139822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139822).length < 2 ^ (prefixWord ++ tailWord_4139822).sum := by decide
  have hdescent : baseEnd_4139822 < baseStart_4139822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139861 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4139861 : Nat := 118140960795 + 4139861 * 2 ^ 59
def prefixEnd_4139861 : Nat := 4983230072969 + 3 ^ 40 * 4139861 * 2
def baseEnd_4139861 : Nat := 1417159023868621672332421

theorem tailTrace_4139861 : CollatzResearch.WordTrace tailWord_4139861 prefixEnd_4139861 1417159023868621672332421 := by
  unfold tailWord_4139861
  simp only [CollatzResearch.WordTrace]
  refine ⟨150993135254998103814219437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100662090169998735876146291 150993135254998103814219437)
  ·
    refine ⟨56622425720624288930332289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150993135254998103814219437 56622425720624288930332289)
    ·
      refine ⟨42466819290468216697749217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56622425720624288930332289 42466819290468216697749217)
      ·
        refine ⟨31850114467851162523311913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42466819290468216697749217 31850114467851162523311913)
        ·
          refine ⟨23887585850888371892483935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31850114467851162523311913 23887585850888371892483935)
          ·
            refine ⟨35831378776332557838725903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23887585850888371892483935 35831378776332557838725903)
            ·
              refine ⟨53747068164498836758088855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35831378776332557838725903 53747068164498836758088855)
              ·
                refine ⟨80620602246748255137133283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53747068164498836758088855 80620602246748255137133283)
                ·
                  refine ⟨120930903370122382705699925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80620602246748255137133283 120930903370122382705699925)
                  ·
                    refine ⟨1417159023868621672332421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120930903370122382705699925 1417159023868621672332421)
                    ·
                      rfl

theorem cell22_4139861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4139861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139861 prefixEnd_4139861 := by exact prefixLift 4139861
  have htrace : WordTrace (prefixWord ++ tailWord_4139861) baseStart_4139861 baseEnd_4139861 := by
    simpa [prefixWord, tailWord_4139861, baseEnd_4139861] using wordTrace_append hprefix tailTrace_4139861
  have hstable : (prefixWord ++ tailWord_4139861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139861).length < 2 ^ (prefixWord ++ tailWord_4139861).sum := by decide
  have hdescent : baseEnd_4139861 < baseStart_4139861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139880 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_4139880 : Nat := 118140960795 + 4139880 * 2 ^ 59
def prefixEnd_4139880 : Nat := 4983230072969 + 3 ^ 40 * 4139880 * 2
def baseEnd_4139880 : Nat := 1417165527956911956107363

theorem tailTrace_4139880 : CollatzResearch.WordTrace tailWord_4139880 prefixEnd_4139880 1417165527956911956107363 := by
  unfold tailWord_4139880
  simp only [CollatzResearch.WordTrace]
  refine ⟨75496914120964635029580547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100662552161286180039440729 75496914120964635029580547)
  ·
    refine ⟨113245371181446952544370821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75496914120964635029580547 113245371181446952544370821)
    ·
      refine ⟨21233507096521303602069529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113245371181446952544370821 21233507096521303602069529)
      ·
        refine ⟨15925130322390977701552147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21233507096521303602069529 15925130322390977701552147)
        ·
          refine ⟨23887695483586466552328221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15925130322390977701552147 23887695483586466552328221)
          ·
            refine ⟨8957885806344924957123083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23887695483586466552328221 8957885806344924957123083)
            ·
              refine ⟨13436828709517387435684625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957885806344924957123083 13436828709517387435684625)
              ·
                refine ⟨10077621532138040576763469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13436828709517387435684625 10077621532138040576763469)
                ·
                  refine ⟨3779108074551765216286301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10077621532138040576763469 3779108074551765216286301)
                  ·
                    refine ⟨1417165527956911956107363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779108074551765216286301 1417165527956911956107363)
                    ·
                      rfl

theorem cell22_4139880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_4139880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139880 prefixEnd_4139880 := by exact prefixLift 4139880
  have htrace : WordTrace (prefixWord ++ tailWord_4139880) baseStart_4139880 baseEnd_4139880 := by
    simpa [prefixWord, tailWord_4139880, baseEnd_4139880] using wordTrace_append hprefix tailTrace_4139880
  have hstable : (prefixWord ++ tailWord_4139880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139880).length < 2 ^ (prefixWord ++ tailWord_4139880).sum := by decide
  have hdescent : baseEnd_4139880 < baseStart_4139880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139897 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_4139897 : Nat := 118140960795 + 4139897 * 2 ^ 59
def prefixEnd_4139897 : Nat := 4983230072969 + 3 ^ 40 * 4139897 * 2
def baseEnd_4139897 : Nat := 1417171347404329578432311

theorem tailTrace_4139897 : CollatzResearch.WordTrace tailWord_4139897 prefixEnd_4139897 1417171347404329578432311 := by
  unfold tailWord_4139897
  simp only [CollatzResearch.WordTrace]
  refine ⟨150994448282867681962529945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100662965521911787975019963 150994448282867681962529945)
  ·
    refine ⟨113245836212150761471897459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150994448282867681962529945 113245836212150761471897459)
    ·
      refine ⟨169868754318226142207846189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113245836212150761471897459 169868754318226142207846189)
      ·
        refine ⟨63700782869334803327942321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169868754318226142207846189 63700782869334803327942321)
        ·
          refine ⟨47775587152001102495956741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63700782869334803327942321 47775587152001102495956741)
          ·
            refine ⟨8957922591000206717991889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47775587152001102495956741 8957922591000206717991889)
            ·
              refine ⟨6718441943250155038493917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957922591000206717991889 6718441943250155038493917)
              ·
                refine ⟨2519415728718808139435219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6718441943250155038493917 2519415728718808139435219)
                ·
                  refine ⟨3779123593078212209152829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519415728718808139435219 3779123593078212209152829)
                  ·
                    refine ⟨1417171347404329578432311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779123593078212209152829 1417171347404329578432311)
                    ·
                      rfl

theorem cell22_4139897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_4139897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139897 prefixEnd_4139897 := by exact prefixLift 4139897
  have htrace : WordTrace (prefixWord ++ tailWord_4139897) baseStart_4139897 baseEnd_4139897 := by
    simpa [prefixWord, tailWord_4139897, baseEnd_4139897] using wordTrace_append hprefix tailTrace_4139897
  have hstable : (prefixWord ++ tailWord_4139897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139897).length < 2 ^ (prefixWord ++ tailWord_4139897).sum := by decide
  have hdescent : baseEnd_4139897 < baseStart_4139897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139940 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_4139940 : Nat := 118140960795 + 4139940 * 2 ^ 59
def prefixEnd_4139940 : Nat := 4983230072969 + 3 ^ 40 * 4139940 * 2
def baseEnd_4139940 : Nat := 1417186067183091799607179

theorem tailTrace_4139940 : CollatzResearch.WordTrace tailWord_4139940 prefixEnd_4139940 1417186067183091799607179 := by
  unfold tailWord_4139940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75498008310855950153172637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100664011081141266870896849 75498008310855950153172637)
  ·
    refine ⟨28311753116570981307439739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75498008310855950153172637 28311753116570981307439739)
    ·
      refine ⟨42467629674856471961159609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28311753116570981307439739 42467629674856471961159609)
      ·
        refine ⟨31850722256142353970869707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42467629674856471961159609 31850722256142353970869707)
        ·
          refine ⟨47776083384213530956304561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31850722256142353970869707 47776083384213530956304561)
          ·
            refine ⟨35832062538160148217228421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47776083384213530956304561 35832062538160148217228421)
            ·
              refine ⟨6718511725905027790730329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35832062538160148217228421 6718511725905027790730329)
              ·
                refine ⟨5038883794428770843047747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718511725905027790730329 5038883794428770843047747)
                ·
                  refine ⟨7558325691643156264571621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038883794428770843047747 7558325691643156264571621)
                  ·
                    refine ⟨1417186067183091799607179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558325691643156264571621 1417186067183091799607179)
                    ·
                      rfl

theorem cell22_4139940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_4139940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139940 prefixEnd_4139940 := by exact prefixLift 4139940
  have htrace : WordTrace (prefixWord ++ tailWord_4139940) baseStart_4139940 baseEnd_4139940 := by
    simpa [prefixWord, tailWord_4139940, baseEnd_4139940] using wordTrace_append hprefix tailTrace_4139940
  have hstable : (prefixWord ++ tailWord_4139940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139940).length < 2 ^ (prefixWord ++ tailWord_4139940).sum := by decide
  have hdescent : baseEnd_4139940 < baseStart_4139940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139968 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_4139968 : Nat := 118140960795 + 4139968 * 2 ^ 59
def prefixEnd_4139968 : Nat := 4983230072969 + 3 ^ 40 * 4139968 * 2
def baseEnd_4139968 : Nat := 1417195652155309059907093

theorem tailTrace_4139968 : CollatzResearch.WordTrace tailWord_4139968 prefixEnd_4139968 1417195652155309059907093 := by
  unfold tailWord_4139968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75498518932805230544182279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100664691910406974058909705 75498518932805230544182279)
  ·
    refine ⟨113247778399207845816273419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75498518932805230544182279 113247778399207845816273419)
    ·
      refine ⟨169871667598811768724410129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113247778399207845816273419 169871667598811768724410129)
      ·
        refine ⟨127403750699108826543307597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169871667598811768724410129 127403750699108826543307597)
        ·
          refine ⟨47776406512165809953740349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127403750699108826543307597 47776406512165809953740349)
          ·
            refine ⟨17916152442062178732652631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47776406512165809953740349 17916152442062178732652631)
            ·
              refine ⟨26874228663093268098978947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17916152442062178732652631 26874228663093268098978947)
              ·
                refine ⟨40311342994639902148468421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26874228663093268098978947 40311342994639902148468421)
                ·
                  refine ⟨7558376811494981652837829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40311342994639902148468421 7558376811494981652837829)
                  ·
                    refine ⟨1417195652155309059907093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558376811494981652837829 1417195652155309059907093)
                    ·
                      rfl

theorem cell22_4139968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_4139968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139968 prefixEnd_4139968 := by exact prefixLift 4139968
  have htrace : WordTrace (prefixWord ++ tailWord_4139968) baseStart_4139968 baseEnd_4139968 := by
    simpa [prefixWord, tailWord_4139968, baseEnd_4139968] using wordTrace_append hprefix tailTrace_4139968
  have hstable : (prefixWord ++ tailWord_4139968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139968).length < 2 ^ (prefixWord ++ tailWord_4139968).sum := by decide
  have hdescent : baseEnd_4139968 < baseStart_4139968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4139983 : List Nat := [1, 1, 2, 1, 1, 7, 2, 7]
def baseStart_4139983 : Nat := 118140960795 + 4139983 * 2 ^ 59
def prefixEnd_4139983 : Nat := 4983230072969 + 3 ^ 40 * 4139983 * 2
def baseEnd_4139983 : Nat := 157466754106872668975783

theorem tailTrace_4139983 : CollatzResearch.WordTrace tailWord_4139983 prefixEnd_4139983 157466754106872668975783 := by
  unfold tailWord_4139983
  simp only [CollatzResearch.WordTrace]
  refine ⟨150997584960556118650160603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100665056640370745766773735 150997584960556118650160603)
  ·
    refine ⟨226496377440834177975240905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150997584960556118650160603 226496377440834177975240905)
    ·
      refine ⟨169872283080625633481430679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226496377440834177975240905 169872283080625633481430679)
      ·
        refine ⟨254808424620938450222146019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169872283080625633481430679 254808424620938450222146019)
        ·
          refine ⟨382212636931407675333219029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254808424620938450222146019 382212636931407675333219029)
          ·
            refine ⟨8958108678079867390622321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 382212636931407675333219029 8958108678079867390622321)
            ·
              refine ⟨6718581508559900542966741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958108678079867390622321 6718581508559900542966741)
              ·
                refine ⟨157466754106872668975783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6718581508559900542966741 157466754106872668975783)
                ·
                  rfl

theorem cell22_4139983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 7].length) (baseStart_4139983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4139983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4139983 prefixEnd_4139983 := by exact prefixLift 4139983
  have htrace : WordTrace (prefixWord ++ tailWord_4139983) baseStart_4139983 baseEnd_4139983 := by
    simpa [prefixWord, tailWord_4139983, baseEnd_4139983] using wordTrace_append hprefix tailTrace_4139983
  have hstable : (prefixWord ++ tailWord_4139983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4139983).length < 2 ^ (prefixWord ++ tailWord_4139983).sum := by decide
  have hdescent : baseEnd_4139983 < baseStart_4139983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4139983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140002 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4140002 : Nat := 118140960795 + 4140002 * 2 ^ 59
def prefixEnd_4140002 : Nat := 4983230072969 + 3 ^ 40 * 4140002 * 2
def baseEnd_4140002 : Nat := 1417207291050144304556989

theorem tailTrace_4140002 : CollatzResearch.WordTrace tailWord_4140002 prefixEnd_4140002 1417207291050144304556989 := by
  unfold tailWord_4140002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37749569486871821223775565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100665518631658189930068173 37749569486871821223775565)
  ·
    refine ⟨14156088557576932958915837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37749569486871821223775565 14156088557576932958915837)
    ·
      refine ⟨5308533209091349859593439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14156088557576932958915837 5308533209091349859593439)
      ·
        refine ⟨7962799813637024789390159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308533209091349859593439 7962799813637024789390159)
        ·
          refine ⟨11944199720455537184085239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962799813637024789390159 11944199720455537184085239)
          ·
            refine ⟨17916299580683305776127859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11944199720455537184085239 17916299580683305776127859)
            ·
              refine ⟨26874449371024958664191789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17916299580683305776127859 26874449371024958664191789)
              ·
                refine ⟨10077918514134359499071921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26874449371024958664191789 10077918514134359499071921)
                ·
                  refine ⟨7558438885600769624303941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10077918514134359499071921 7558438885600769624303941)
                  ·
                    refine ⟨1417207291050144304556989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558438885600769624303941 1417207291050144304556989)
                    ·
                      rfl

theorem cell22_4140002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4140002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140002 prefixEnd_4140002 := by exact prefixLift 4140002
  have htrace : WordTrace (prefixWord ++ tailWord_4140002) baseStart_4140002 baseEnd_4140002 := by
    simpa [prefixWord, tailWord_4140002, baseEnd_4140002] using wordTrace_append hprefix tailTrace_4140002
  have hstable : (prefixWord ++ tailWord_4140002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140002).length < 2 ^ (prefixWord ++ tailWord_4140002).sum := by decide
  have hdescent : baseEnd_4140002 < baseStart_4140002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140021 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4140021 : Nat := 118140960795 + 4140021 * 2 ^ 59
def prefixEnd_4140021 : Nat := 4983230072969 + 3 ^ 40 * 4140021 * 2
def baseEnd_4140021 : Nat := 1417213795138434588331931

theorem tailTrace_4140021 : CollatzResearch.WordTrace tailWord_4140021 prefixEnd_4140021 1417213795138434588331931 := by
  unfold tailWord_4140021
  simp only [CollatzResearch.WordTrace]
  refine ⟨150998970934418451140043917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100665980622945634093362611 150998970934418451140043917)
  ·
    refine ⟨56624614100406919177516469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150998970934418451140043917 56624614100406919177516469)
    ·
      refine ⟨5308557571913148672892169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56624614100406919177516469 5308557571913148672892169)
      ·
        refine ⟨3981418178934861504669127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308557571913148672892169 3981418178934861504669127)
        ·
          refine ⟨5972127268402292257003691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981418178934861504669127 5972127268402292257003691)
          ·
            refine ⟨8958190902603438385505537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972127268402292257003691 8958190902603438385505537)
            ·
              refine ⟨6718643176952578789129153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958190902603438385505537 6718643176952578789129153)
              ·
                refine ⟨5038982382714434091846865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718643176952578789129153 5038982382714434091846865)
                ·
                  refine ⟨3779236787035825568885149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038982382714434091846865 3779236787035825568885149)
                  ·
                    refine ⟨1417213795138434588331931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779236787035825568885149 1417213795138434588331931)
                    ·
                      rfl

theorem cell22_4140021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4140021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140021 prefixEnd_4140021 := by exact prefixLift 4140021
  have htrace : WordTrace (prefixWord ++ tailWord_4140021) baseStart_4140021 baseEnd_4140021 := by
    simpa [prefixWord, tailWord_4140021, baseEnd_4140021] using wordTrace_append hprefix tailTrace_4140021
  have hstable : (prefixWord ++ tailWord_4140021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140021).length < 2 ^ (prefixWord ++ tailWord_4140021).sum := by decide
  have hdescent : baseEnd_4140021 < baseStart_4140021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140034 : List Nat := [3, 4, 1, 3, 1, 2, 1, 7]
def baseStart_4140034 : Nat := 118140960795 + 4140034 * 2 ^ 59
def prefixEnd_4140034 : Nat := 4983230072969 + 3 ^ 40 * 4140034 * 2
def baseEnd_4140034 : Nat := 157468693922678543084099

theorem tailTrace_4140034 : CollatzResearch.WordTrace tailWord_4140034 prefixEnd_4140034 157468693922678543084099 := by
  unfold tailWord_4140034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37749861270842838590066789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100666296722247569573511437 37749861270842838590066789)
  ·
    refine ⟨7078098988283032235637523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37749861270842838590066789 7078098988283032235637523)
    ·
      refine ⟨10617148482424548353456285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078098988283032235637523 10617148482424548353456285)
      ·
        refine ⟨3981430680909205632546107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10617148482424548353456285 3981430680909205632546107)
        ·
          refine ⟨5972146021363808448819161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981430680909205632546107 5972146021363808448819161)
          ·
            refine ⟨4479109516022856336614371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972146021363808448819161 4479109516022856336614371)
            ·
              refine ⟨6718664274034284504921557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479109516022856336614371 6718664274034284504921557)
              ·
                refine ⟨157468693922678543084099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6718664274034284504921557 157468693922678543084099)
                ·
                  rfl

theorem cell22_4140034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_4140034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140034 prefixEnd_4140034 := by exact prefixLift 4140034
  have htrace : WordTrace (prefixWord ++ tailWord_4140034) baseStart_4140034 baseEnd_4140034 := by
    simpa [prefixWord, tailWord_4140034, baseEnd_4140034] using wordTrace_append hprefix tailTrace_4140034
  have hstable : (prefixWord ++ tailWord_4140034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140034).length < 2 ^ (prefixWord ++ tailWord_4140034).sum := by decide
  have hdescent : baseEnd_4140034 < baseStart_4140034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140043 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_4140043 : Nat := 118140960795 + 4140043 * 2 ^ 59
def prefixEnd_4140043 : Nat := 4983230072969 + 3 ^ 40 * 4140043 * 2
def baseEnd_4140043 : Nat := 1417221326188033864281863

theorem tailTrace_4140043 : CollatzResearch.WordTrace tailWord_4140043 prefixEnd_4140043 1417221326188033864281863 := by
  unfold tailWord_4140043
  simp only [CollatzResearch.WordTrace]
  refine ⟨150999773340338748897344783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100666515560225832598229855 150999773340338748897344783)
  ·
    refine ⟨226499660010508123346017175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150999773340338748897344783 226499660010508123346017175)
    ·
      refine ⟨339749490015762185019025763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226499660010508123346017175 339749490015762185019025763)
      ·
        refine ⟨509624235023643277528538645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339749490015762185019025763 509624235023643277528538645)
        ·
          refine ⟨23888636016733278634150249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 509624235023643277528538645 23888636016733278634150249)
          ·
            refine ⟨17916477012549958975612687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23888636016733278634150249 17916477012549958975612687)
            ·
              refine ⟨26874715518824938463419031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17916477012549958975612687 26874715518824938463419031)
              ·
                refine ⟨40312073278237407695128547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26874715518824938463419031 40312073278237407695128547)
                ·
                  refine ⟨60468109917356111542692821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40312073278237407695128547 60468109917356111542692821)
                  ·
                    refine ⟨1417221326188033864281863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60468109917356111542692821 1417221326188033864281863)
                    ·
                      rfl

theorem cell22_4140043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_4140043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140043 prefixEnd_4140043 := by exact prefixLift 4140043
  have htrace : WordTrace (prefixWord ++ tailWord_4140043) baseStart_4140043 baseEnd_4140043 := by
    simpa [prefixWord, tailWord_4140043, baseEnd_4140043] using wordTrace_append hprefix tailTrace_4140043
  have hstable : (prefixWord ++ tailWord_4140043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140043).length < 2 ^ (prefixWord ++ tailWord_4140043).sum := by decide
  have hdescent : baseEnd_4140043 < baseStart_4140043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140075 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 1, 4]
def baseStart_4140075 : Nat := 118140960795 + 4140075 * 2 ^ 59
def prefixEnd_4140075 : Nat := 4983230072969 + 3 ^ 40 * 4140075 * 2
def baseEnd_4140075 : Nat := 1417232280441996447481765

theorem tailTrace_4140075 : CollatzResearch.WordTrace tailWord_4140075 prefixEnd_4140075 1417232280441996447481765 := by
  unfold tailWord_4140075
  simp only [CollatzResearch.WordTrace]
  refine ⟨151000940476222818362509679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100667293650815212241673119 151000940476222818362509679)
  ·
    refine ⟨226501410714334227543764519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151000940476222818362509679 226501410714334227543764519)
    ·
      refine ⟨339752116071501341315646779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226501410714334227543764519 339752116071501341315646779)
      ·
        refine ⟨509628174107252011973470169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339752116071501341315646779 509628174107252011973470169)
        ·
          refine ⟨382221130580439008980102627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509628174107252011973470169 382221130580439008980102627)
          ·
            refine ⟨573331695870658513470153941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382221130580439008980102627 573331695870658513470153941)
            ·
              refine ⟨13437461621968558909456733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 573331695870658513470153941 13437461621968558909456733)
              ·
                refine ⟨5039048108238209591046275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13437461621968558909456733 5039048108238209591046275)
                ·
                  refine ⟨7558572162357314386569413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039048108238209591046275 7558572162357314386569413)
                  ·
                    refine ⟨1417232280441996447481765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558572162357314386569413 1417232280441996447481765)
                    ·
                      rfl

theorem cell22_4140075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_4140075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140075 prefixEnd_4140075 := by exact prefixLift 4140075
  have htrace : WordTrace (prefixWord ++ tailWord_4140075) baseStart_4140075 baseEnd_4140075 := by
    simpa [prefixWord, tailWord_4140075, baseEnd_4140075] using wordTrace_append hprefix tailTrace_4140075
  have hstable : (prefixWord ++ tailWord_4140075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140075).length < 2 ^ (prefixWord ++ tailWord_4140075).sum := by decide
  have hdescent : baseEnd_4140075 < baseStart_4140075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140109 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4140109 : Nat := 118140960795 + 4140109 * 2 ^ 59
def prefixEnd_4140109 : Nat := 4983230072969 + 3 ^ 40 * 4140109 * 2
def baseEnd_4140109 : Nat := 1417243919336831692131661

theorem tailTrace_4140109 : CollatzResearch.WordTrace tailWord_4140109 prefixEnd_4140109 1417243919336831692131661 := by
  unfold tailWord_4140109
  simp only [CollatzResearch.WordTrace]
  refine ⟨151002180558099642169247381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100668120372066428112831587 151002180558099642169247381)
  ·
    refine ⟨7078227213660920726683471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151002180558099642169247381 7078227213660920726683471)
    ·
      refine ⟨10617340820491381090025207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078227213660920726683471 10617340820491381090025207)
      ·
        refine ⟨15926011230737071635037811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10617340820491381090025207 15926011230737071635037811)
        ·
          refine ⟨23889016846105607452556717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15926011230737071635037811 23889016846105607452556717)
          ·
            refine ⟨8958381317289602794708769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23889016846105607452556717 8958381317289602794708769)
            ·
              refine ⟨6718785987967202096031577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958381317289602794708769 6718785987967202096031577)
              ·
                refine ⟨5039089490975401572023683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718785987967202096031577 5039089490975401572023683)
                ·
                  refine ⟨7558634236463102358035525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039089490975401572023683 7558634236463102358035525)
                  ·
                    refine ⟨1417243919336831692131661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558634236463102358035525 1417243919336831692131661)
                    ·
                      rfl

theorem cell22_4140109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4140109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140109 prefixEnd_4140109 := by exact prefixLift 4140109
  have htrace : WordTrace (prefixWord ++ tailWord_4140109) baseStart_4140109 baseEnd_4140109 := by
    simpa [prefixWord, tailWord_4140109, baseEnd_4140109] using wordTrace_append hprefix tailTrace_4140109
  have hstable : (prefixWord ++ tailWord_4140109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140109).length < 2 ^ (prefixWord ++ tailWord_4140109).sum := by decide
  have hdescent : baseEnd_4140109 < baseStart_4140109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140120 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_4140120 : Nat := 118140960795 + 4140120 * 2 ^ 59
def prefixEnd_4140120 : Nat := 4983230072969 + 3 ^ 40 * 4140120 * 2
def baseEnd_4140120 : Nat := 1417247684861631330106627

theorem tailTrace_4140120 : CollatzResearch.WordTrace tailWord_4140120 prefixEnd_4140120 1417247684861631330106627 := by
  unfold tailWord_4140120
  simp only [CollatzResearch.WordTrace]
  refine ⟨75501290880529895523948907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100668387840706527365265209 75501290880529895523948907)
  ·
    refine ⟨113251936320794843285923361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75501290880529895523948907 113251936320794843285923361)
    ·
      refine ⟨84938952240596132464442521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113251936320794843285923361 84938952240596132464442521)
      ·
        refine ⟨63704214180447099348331891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84938952240596132464442521 63704214180447099348331891)
        ·
          refine ⟨95556321270670649022497837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63704214180447099348331891 95556321270670649022497837)
          ·
            refine ⟨35833620476501493383436689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95556321270670649022497837 35833620476501493383436689)
            ·
              refine ⟨26875215357376120037577517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35833620476501493383436689 26875215357376120037577517)
              ·
                refine ⟨10078205759016045014091569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26875215357376120037577517 10078205759016045014091569)
                ·
                  refine ⟨7558654319262033760568677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10078205759016045014091569 7558654319262033760568677)
                  ·
                    refine ⟨1417247684861631330106627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558654319262033760568677 1417247684861631330106627)
                    ·
                      rfl

theorem cell22_4140120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_4140120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140120 prefixEnd_4140120 := by exact prefixLift 4140120
  have htrace : WordTrace (prefixWord ++ tailWord_4140120) baseStart_4140120 baseEnd_4140120 := by
    simpa [prefixWord, tailWord_4140120, baseEnd_4140120] using wordTrace_append hprefix tailTrace_4140120
  have hstable : (prefixWord ++ tailWord_4140120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140120).length < 2 ^ (prefixWord ++ tailWord_4140120).sum := by decide
  have hdescent : baseEnd_4140120 < baseStart_4140120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140126 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4140126 : Nat := 118140960795 + 4140126 * 2 ^ 59
def prefixEnd_4140126 : Nat := 4983230072969 + 3 ^ 40 * 4140126 * 2
def baseEnd_4140126 : Nat := 1417249738784249314456609

theorem tailTrace_4140126 : CollatzResearch.WordTrace tailWord_4140126 prefixEnd_4140126 1417249738784249314456609 := by
  unfold tailWord_4140126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18875350074879756759077029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100668533732692036048410821 18875350074879756759077029)
  ·
    refine ⟨3539128139039954392326943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18875350074879756759077029 3539128139039954392326943)
    ·
      refine ⟨5308692208559931588490415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539128139039954392326943 5308692208559931588490415)
      ·
        refine ⟨7963038312839897382735623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308692208559931588490415 7963038312839897382735623)
        ·
          refine ⟨11944557469259846074103435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963038312839897382735623 11944557469259846074103435)
          ·
            refine ⟨17916836203889769111155153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11944557469259846074103435 17916836203889769111155153)
            ·
              refine ⟨13437627152917326833366365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17916836203889769111155153 13437627152917326833366365)
              ·
                refine ⟨5039110182343997562512387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13437627152917326833366365 5039110182343997562512387)
                ·
                  refine ⟨7558665273515996343768581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039110182343997562512387 7558665273515996343768581)
                  ·
                    refine ⟨1417249738784249314456609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7558665273515996343768581 1417249738784249314456609)
                    ·
                      rfl

theorem cell22_4140126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4140126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140126 prefixEnd_4140126 := by exact prefixLift 4140126
  have htrace : WordTrace (prefixWord ++ tailWord_4140126) baseStart_4140126 baseEnd_4140126 := by
    simpa [prefixWord, tailWord_4140126, baseEnd_4140126] using wordTrace_append hprefix tailTrace_4140126
  have hstable : (prefixWord ++ tailWord_4140126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140126).length < 2 ^ (prefixWord ++ tailWord_4140126).sum := by decide
  have hdescent : baseEnd_4140126 < baseStart_4140126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140135 : List Nat := [1, 1, 5, 1, 1, 5, 8]
def baseStart_4140135 : Nat := 118140960795 + 4140135 * 2 ^ 59
def prefixEnd_4140135 : Nat := 4983230072969 + 3 ^ 40 * 4140135 * 2
def baseEnd_4140135 : Nat := 52490845172895418184503

theorem tailTrace_4140135 : CollatzResearch.WordTrace tailWord_4140135 prefixEnd_4140135 52490845172895418184503 := by
  unfold tailWord_4140135
  simp only [CollatzResearch.WordTrace]
  refine ⟨151003128856005448609693859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100668752570670299073129239 151003128856005448609693859)
  ·
    refine ⟨226504693284008172914540789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151003128856005448609693859 226504693284008172914540789)
    ·
      refine ⟨21234814995375766210738199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226504693284008172914540789 21234814995375766210738199)
      ·
        refine ⟨31852222493063649316107299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21234814995375766210738199 31852222493063649316107299)
        ·
          refine ⟨47778333739595473974160949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31852222493063649316107299 47778333739595473974160949)
          ·
            refine ⟨4479218788087075685077589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47778333739595473974160949 4479218788087075685077589)
            ·
              refine ⟨52490845172895418184503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4479218788087075685077589 52490845172895418184503)
              ·
                rfl

theorem cell22_4140135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 8].length) (baseStart_4140135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140135 prefixEnd_4140135 := by exact prefixLift 4140135
  have htrace : WordTrace (prefixWord ++ tailWord_4140135) baseStart_4140135 baseEnd_4140135 := by
    simpa [prefixWord, tailWord_4140135, baseEnd_4140135] using wordTrace_append hprefix tailTrace_4140135
  have hstable : (prefixWord ++ tailWord_4140135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140135).length < 2 ^ (prefixWord ++ tailWord_4140135).sum := by decide
  have hdescent : baseEnd_4140135 < baseStart_4140135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140197 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 5]
def baseStart_4140197 : Nat := 118140960795 + 4140197 * 2 ^ 59
def prefixEnd_4140197 : Nat := 4983230072969 + 3 ^ 40 * 4140197 * 2
def baseEnd_4140197 : Nat := 472424681178409598643797

theorem tailTrace_4140197 : CollatzResearch.WordTrace tailWord_4140197 prefixEnd_4140197 472424681178409598643797 := by
  unfold tailWord_4140197
  simp only [CollatzResearch.WordTrace]
  refine ⟨151005390181780833198450845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100670260121187222132300563 151005390181780833198450845)
  ·
    refine ⟨56627021318167812449419067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151005390181780833198450845 56627021318167812449419067)
    ·
      refine ⟨84940531977251718674128601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56627021318167812449419067 84940531977251718674128601)
      ·
        refine ⟨63705398982938789005596451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84940531977251718674128601 63705398982938789005596451)
        ·
          refine ⟨95558098474408183508394677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63705398982938789005596451 95558098474408183508394677)
          ·
            refine ⟨8958571731975767203912001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95558098474408183508394677 8958571731975767203912001)
            ·
              refine ⟨6718928798981825402934001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8958571731975767203912001 6718928798981825402934001)
              ·
                refine ⟨5039196599236369052200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6718928798981825402934001 5039196599236369052200501)
                ·
                  refine ⟨472424681178409598643797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5039196599236369052200501 472424681178409598643797)
                  ·
                    rfl

theorem cell22_4140197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_4140197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140197 prefixEnd_4140197 := by exact prefixLift 4140197
  have htrace : WordTrace (prefixWord ++ tailWord_4140197) baseStart_4140197 baseEnd_4140197 := by
    simpa [prefixWord, tailWord_4140197, baseEnd_4140197] using wordTrace_append hprefix tailTrace_4140197
  have hstable : (prefixWord ++ tailWord_4140197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140197).length < 2 ^ (prefixWord ++ tailWord_4140197).sum := by decide
  have hdescent : baseEnd_4140197 < baseStart_4140197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140287 : List Nat := [1, 1, 2, 2, 1, 5, 4, 6]
def baseStart_4140287 : Nat := 118140960795 + 4140287 * 2 ^ 59
def prefixEnd_4140287 : Nat := 4983230072969 + 3 ^ 40 * 4140287 * 2
def baseEnd_4140287 : Nat := 157478316930499840131235

theorem tailTrace_4140287 : CollatzResearch.WordTrace tailWord_4140287 prefixEnd_4140287 157478316930499840131235 := by
  unfold tailWord_4140287
  simp only [CollatzResearch.WordTrace]
  refine ⟨151008672751454778569227115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100672448500969852379484743 151008672751454778569227115)
  ·
    refine ⟨226513009127182167853840673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151008672751454778569227115 226513009127182167853840673)
    ·
      refine ⟨169884756845386625890380505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226513009127182167853840673 169884756845386625890380505)
      ·
        refine ⟨127413567634039969417785379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169884756845386625890380505 127413567634039969417785379)
        ·
          refine ⟨191120351451059954126678069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127413567634039969417785379 191120351451059954126678069)
          ·
            refine ⟨17917532948536870699376069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191120351451059954126678069 17917532948536870699376069)
            ·
              refine ⟨3359537427850663256133013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17917532948536870699376069 3359537427850663256133013)
              ·
                refine ⟨157478316930499840131235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3359537427850663256133013 157478316930499840131235)
                ·
                  rfl

theorem cell22_4140287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 6].length) (baseStart_4140287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140287 prefixEnd_4140287 := by exact prefixLift 4140287
  have htrace : WordTrace (prefixWord ++ tailWord_4140287) baseStart_4140287 baseEnd_4140287 := by
    simpa [prefixWord, tailWord_4140287, baseEnd_4140287] using wordTrace_append hprefix tailTrace_4140287
  have hstable : (prefixWord ++ tailWord_4140287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140287).length < 2 ^ (prefixWord ++ tailWord_4140287).sum := by decide
  have hdescent : baseEnd_4140287 < baseStart_4140287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140407 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_4140407 : Nat := 118140960795 + 4140407 * 2 ^ 59
def prefixEnd_4140407 : Nat := 4983230072969 + 3 ^ 40 * 4140407 * 2
def baseEnd_4140407 : Nat := 1417345930826858248180747

theorem tailTrace_4140407 : CollatzResearch.WordTrace tailWord_4140407 prefixEnd_4140407 1417345930826858248180747 := by
  unfold tailWord_4140407
  simp only [CollatzResearch.WordTrace]
  refine ⟨151013049511020039063595475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100675366340680026042396983 151013049511020039063595475)
  ·
    refine ⟨226519574266530058595393213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151013049511020039063595475 226519574266530058595393213)
    ·
      refine ⟨84944840349948771973272455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226519574266530058595393213 84944840349948771973272455)
      ·
        refine ⟨127417260524923157959908683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84944840349948771973272455 127417260524923157959908683)
        ·
          refine ⟨191125890787384736939863025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127417260524923157959908683 191125890787384736939863025)
          ·
            refine ⟨143344418090538552704897269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191125890787384736939863025 143344418090538552704897269)
            ·
              refine ⟨13438539195987989316084119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143344418090538552704897269 13438539195987989316084119)
              ·
                refine ⟨20157808793981983974126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438539195987989316084119 20157808793981983974126179)
                ·
                  refine ⟨30236713190972975961189269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20157808793981983974126179 30236713190972975961189269)
                  ·
                    refine ⟨1417345930826858248180747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30236713190972975961189269 1417345930826858248180747)
                    ·
                      rfl

theorem cell22_4140407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_4140407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140407 prefixEnd_4140407 := by exact prefixLift 4140407
  have htrace : WordTrace (prefixWord ++ tailWord_4140407) baseStart_4140407 baseEnd_4140407 := by
    simpa [prefixWord, tailWord_4140407, baseEnd_4140407] using wordTrace_append hprefix tailTrace_4140407
  have hstable : (prefixWord ++ tailWord_4140407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140407).length < 2 ^ (prefixWord ++ tailWord_4140407).sum := by decide
  have hdescent : baseEnd_4140407 < baseStart_4140407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140456 : List Nat := [2, 1, 6, 1, 2, 1, 1, 8]
def baseStart_4140456 : Nat := 118140960795 + 4140456 * 2 ^ 59
def prefixEnd_4140456 : Nat := 4983230072969 + 3 ^ 40 * 4140456 * 2
def baseEnd_4140456 : Nat := 157484744947582050411733

theorem tailTrace_4140456 : CollatzResearch.WordTrace tailWord_4140456 prefixEnd_4140456 157484744947582050411733 := by
  unfold tailWord_4140456
  simp only [CollatzResearch.WordTrace]
  refine ⟨75507418343921260216064611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100676557791895013621419481 75507418343921260216064611)
  ·
    refine ⟨113261127515881890324096917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75507418343921260216064611 113261127515881890324096917)
    ·
      refine ⟨5309115352306963608942043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113261127515881890324096917 5309115352306963608942043)
      ·
        refine ⟨7963673028460445413413065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309115352306963608942043 7963673028460445413413065)
        ·
          refine ⟨5972754771345334060059799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7963673028460445413413065 5972754771345334060059799)
          ·
            refine ⟨8959132157018001090089699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972754771345334060059799 8959132157018001090089699)
            ·
              refine ⟨13438698235527001635134549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8959132157018001090089699 13438698235527001635134549)
              ·
                refine ⟨157484744947582050411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13438698235527001635134549 157484744947582050411733)
                ·
                  rfl

theorem cell22_4140456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_4140456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140456 prefixEnd_4140456 := by exact prefixLift 4140456
  have htrace : WordTrace (prefixWord ++ tailWord_4140456) baseStart_4140456 baseEnd_4140456 := by
    simpa [prefixWord, tailWord_4140456, baseEnd_4140456] using wordTrace_append hprefix tailTrace_4140456
  have hstable : (prefixWord ++ tailWord_4140456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140456).length < 2 ^ (prefixWord ++ tailWord_4140456).sum := by decide
  have hdescent : baseEnd_4140456 < baseStart_4140456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140497 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4140497 : Nat := 118140960795 + 4140497 * 2 ^ 59
def prefixEnd_4140497 : Nat := 4983230072969 + 3 ^ 40 * 4140497 * 2
def baseEnd_4140497 : Nat := 1417376739666128013430471

theorem tailTrace_4140497 : CollatzResearch.WordTrace tailWord_4140497 prefixEnd_4140497 1417376739666128013430471 := by
  unfold tailWord_4140497
  simp only [CollatzResearch.WordTrace]
  refine ⟨151016332080693984434371745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100677554720462656289581163 151016332080693984434371745)
  ·
    refine ⟨113262249060520488325778809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151016332080693984434371745 113262249060520488325778809)
    ·
      refine ⟨84946686795390366244334107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113262249060520488325778809 84946686795390366244334107)
      ·
        refine ⟨127420030193085549366501161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84946686795390366244334107 127420030193085549366501161)
        ·
          refine ⟨95565022644814162024875871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127420030193085549366501161 95565022644814162024875871)
          ·
            refine ⟨143347533967221243037313807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95565022644814162024875871 143347533967221243037313807)
            ·
              refine ⟨215021300950831864555970711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143347533967221243037313807 215021300950831864555970711)
              ·
                refine ⟨322531951426247796833956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215021300950831864555970711 322531951426247796833956067)
                ·
                  refine ⟨483797927139371695250934101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322531951426247796833956067 483797927139371695250934101)
                  ·
                    refine ⟨1417376739666128013430471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 483797927139371695250934101 1417376739666128013430471)
                    ·
                      rfl

theorem cell22_4140497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4140497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140497 prefixEnd_4140497 := by exact prefixLift 4140497
  have htrace : WordTrace (prefixWord ++ tailWord_4140497) baseStart_4140497 baseEnd_4140497 := by
    simpa [prefixWord, tailWord_4140497, baseEnd_4140497] using wordTrace_append hprefix tailTrace_4140497
  have hstable : (prefixWord ++ tailWord_4140497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140497).length < 2 ^ (prefixWord ++ tailWord_4140497).sum := by decide
  have hdescent : baseEnd_4140497 < baseStart_4140497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140561 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_4140561 : Nat := 118140960795 + 4140561 * 2 ^ 59
def prefixEnd_4140561 : Nat := 4983230072969 + 3 ^ 40 * 4140561 * 2
def baseEnd_4140561 : Nat := 1417398648174053179830275

theorem tailTrace_4140561 : CollatzResearch.WordTrace tailWord_4140561 prefixEnd_4140561 1417398648174053179830275 := by
  unfold tailWord_4140561
  simp only [CollatzResearch.WordTrace]
  refine ⟨151018666352462123364701537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100679110901641415576467691 151018666352462123364701537)
  ·
    refine ⟨113263999764346592523526153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151018666352462123364701537 113263999764346592523526153)
    ·
      refine ⟨84947999823259944392644615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113263999764346592523526153 84947999823259944392644615)
      ·
        refine ⟨127421999734889916588966923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84947999823259944392644615 127421999734889916588966923)
        ·
          refine ⟨191132999602334874883450385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127421999734889916588966923 191132999602334874883450385)
          ·
            refine ⟨143349749701751156162587789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191132999602334874883450385 143349749701751156162587789)
            ·
              refine ⟨53756156138156683560970421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143349749701751156162587789 53756156138156683560970421)
              ·
                refine ⟨5039639637952189083840977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53756156138156683560970421 5039639637952189083840977)
                ·
                  refine ⟨3779729728464141812880733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039639637952189083840977 3779729728464141812880733)
                  ·
                    refine ⟨1417398648174053179830275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779729728464141812880733 1417398648174053179830275)
                    ·
                      rfl

theorem cell22_4140561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_4140561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140561 prefixEnd_4140561 := by exact prefixLift 4140561
  have htrace : WordTrace (prefixWord ++ tailWord_4140561) baseStart_4140561 baseEnd_4140561 := by
    simpa [prefixWord, tailWord_4140561, baseEnd_4140561] using wordTrace_append hprefix tailTrace_4140561
  have hstable : (prefixWord ++ tailWord_4140561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140561).length < 2 ^ (prefixWord ++ tailWord_4140561).sum := by decide
  have hdescent : baseEnd_4140561 < baseStart_4140561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140576 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_4140576 : Nat := 118140960795 + 4140576 * 2 ^ 59
def prefixEnd_4140576 : Nat := 4983230072969 + 3 ^ 40 * 4140576 * 2
def baseEnd_4140576 : Nat := 1417403782980598140705229

theorem tailTrace_4140576 : CollatzResearch.WordTrace tailWord_4140576 prefixEnd_4140576 1417403782980598140705229 := by
  unfold tailWord_4140576
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509606723703890463248791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100679475631605187284331721 75509606723703890463248791)
  ·
    refine ⟨113264410085555835694873187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75509606723703890463248791 113264410085555835694873187)
    ·
      refine ⟨169896615128333753542309781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113264410085555835694873187 169896615128333753542309781)
      ·
        refine ⟨7963903834140644697295771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169896615128333753542309781 7963903834140644697295771)
        ·
          refine ⟨11945855751210967045943657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963903834140644697295771 11945855751210967045943657)
          ·
            refine ⟨8959391813408225284457743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11945855751210967045943657 8959391813408225284457743)
            ·
              refine ⟨13439087720112337926686615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8959391813408225284457743 13439087720112337926686615)
              ·
                refine ⟨20158631580168506890029923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13439087720112337926686615 20158631580168506890029923)
                ·
                  refine ⟨30237947370252760335044885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20158631580168506890029923 30237947370252760335044885)
                  ·
                    refine ⟨1417403782980598140705229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30237947370252760335044885 1417403782980598140705229)
                    ·
                      rfl

theorem cell22_4140576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_4140576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140576 prefixEnd_4140576 := by exact prefixLift 4140576
  have htrace : WordTrace (prefixWord ++ tailWord_4140576) baseStart_4140576 baseEnd_4140576 := by
    simpa [prefixWord, tailWord_4140576, baseEnd_4140576] using wordTrace_append hprefix tailTrace_4140576
  have hstable : (prefixWord ++ tailWord_4140576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140576).length < 2 ^ (prefixWord ++ tailWord_4140576).sum := by decide
  have hdescent : baseEnd_4140576 < baseStart_4140576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140634 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_4140634 : Nat := 118140960795 + 4140634 * 2 ^ 59
def prefixEnd_4140634 : Nat := 4983230072969 + 3 ^ 40 * 4140634 * 2
def baseEnd_4140634 : Nat := 1417423637565905322755051

theorem tailTrace_4140634 : CollatzResearch.WordTrace tailWord_4140634 prefixEnd_4140634 1417423637565905322755051 := by
  unfold tailWord_4140634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37755332220299414208027239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100680885920798437888072637 37755332220299414208027239)
  ·
    refine ⟨56632998330449121312040859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37755332220299414208027239 56632998330449121312040859)
    ·
      refine ⟨84949497495673681968061289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56632998330449121312040859 84949497495673681968061289)
      ·
        refine ⟨63712123121755261476045967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84949497495673681968061289 63712123121755261476045967)
        ·
          refine ⟨95568184682632892214068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63712123121755261476045967 95568184682632892214068951)
          ·
            refine ⟨143352277023949338321103427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95568184682632892214068951 143352277023949338321103427)
            ·
              refine ⟨215028415535924007481655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143352277023949338321103427 215028415535924007481655141)
              ·
                refine ⟨40317827912985751402810339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215028415535924007481655141 40317827912985751402810339)
                ·
                  refine ⟨60476741869478627104215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40317827912985751402810339 60476741869478627104215509)
                  ·
                    refine ⟨1417423637565905322755051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60476741869478627104215509 1417423637565905322755051)
                    ·
                      rfl

theorem cell22_4140634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_4140634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140634 prefixEnd_4140634 := by exact prefixLift 4140634
  have htrace : WordTrace (prefixWord ++ tailWord_4140634) baseStart_4140634 baseEnd_4140634 := by
    simpa [prefixWord, tailWord_4140634, baseEnd_4140634] using wordTrace_append hprefix tailTrace_4140634
  have hstable : (prefixWord ++ tailWord_4140634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140634).length < 2 ^ (prefixWord ++ tailWord_4140634).sum := by decide
  have hdescent : baseEnd_4140634 < baseStart_4140634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140636 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_4140636 : Nat := 118140960795 + 4140636 * 2 ^ 59
def prefixEnd_4140636 : Nat := 4983230072969 + 3 ^ 40 * 4140636 * 2
def baseEnd_4140636 : Nat := 472474774068925994735015

theorem tailTrace_4140636 : CollatzResearch.WordTrace tailWord_4140636 prefixEnd_4140636 472474774068925994735015 := by
  unfold tailWord_4140636
  simp only [CollatzResearch.WordTrace]
  refine ⟨75510700913595205586840881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100680934551460274115787841 75510700913595205586840881)
  ·
    refine ⟨56633025685196404190130661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75510700913595205586840881 56633025685196404190130661)
    ·
      refine ⟨10618692315974325785649499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56633025685196404190130661 10618692315974325785649499)
      ·
        refine ⟨15928038473961488678474249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10618692315974325785649499 15928038473961488678474249)
        ·
          refine ⟨11946028855471116508855687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15928038473961488678474249 11946028855471116508855687)
          ·
            refine ⟨17919043283206674763283531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946028855471116508855687 17919043283206674763283531)
            ·
              refine ⟨26878564924810012144925297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919043283206674763283531 26878564924810012144925297)
              ·
                refine ⟨20158923693607509108693973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26878564924810012144925297 20158923693607509108693973)
                ·
                  refine ⟨472474774068925994735015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20158923693607509108693973 472474774068925994735015)
                  ·
                    rfl

theorem cell22_4140636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_4140636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140636 prefixEnd_4140636 := by exact prefixLift 4140636
  have htrace : WordTrace (prefixWord ++ tailWord_4140636) baseStart_4140636 baseEnd_4140636 := by
    simpa [prefixWord, tailWord_4140636, baseEnd_4140636] using wordTrace_append hprefix tailTrace_4140636
  have hstable : (prefixWord ++ tailWord_4140636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140636).length < 2 ^ (prefixWord ++ tailWord_4140636).sum := by decide
  have hdescent : baseEnd_4140636 < baseStart_4140636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140696 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_4140696 : Nat := 118140960795 + 4140696 * 2 ^ 59
def prefixEnd_4140696 : Nat := 4983230072969 + 3 ^ 40 * 4140696 * 2
def baseEnd_4140696 : Nat := 1417444861432957827704861

theorem tailTrace_4140696 : CollatzResearch.WordTrace tailWord_4140696 prefixEnd_4140696 1417444861432957827704861 := by
  unfold tailWord_4140696
  simp only [CollatzResearch.WordTrace]
  refine ⟨75511795103486520710432971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100682393471315360947243961 75511795103486520710432971)
  ·
    refine ⟨113267692655229781065649457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75511795103486520710432971 113267692655229781065649457)
    ·
      refine ⟨84950769491422335799237093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113267692655229781065649457 84950769491422335799237093)
      ·
        refine ⟨15928269279641687962356955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84950769491422335799237093 15928269279641687962356955)
        ·
          refine ⟨23892403919462531943535433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928269279641687962356955 23892403919462531943535433)
          ·
            refine ⟨17919302939596898957651575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23892403919462531943535433 17919302939596898957651575)
            ·
              refine ⟨26878954409395348436477363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919302939596898957651575 26878954409395348436477363)
              ·
                refine ⟨40318431614093022654716045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26878954409395348436477363 40318431614093022654716045)
                ·
                  refine ⟨15119411855284883495518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40318431614093022654716045 15119411855284883495518517)
                  ·
                    refine ⟨1417444861432957827704861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15119411855284883495518517 1417444861432957827704861)
                    ·
                      rfl

theorem cell22_4140696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_4140696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140696 prefixEnd_4140696 := by exact prefixLift 4140696
  have htrace : WordTrace (prefixWord ++ tailWord_4140696) baseStart_4140696 baseEnd_4140696 := by
    simpa [prefixWord, tailWord_4140696, baseEnd_4140696] using wordTrace_append hprefix tailTrace_4140696
  have hstable : (prefixWord ++ tailWord_4140696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140696).length < 2 ^ (prefixWord ++ tailWord_4140696).sum := by decide
  have hdescent : baseEnd_4140696 < baseStart_4140696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140764 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4140764 : Nat := 118140960795 + 4140764 * 2 ^ 59
def prefixEnd_4140764 : Nat := 4983230072969 + 3 ^ 40 * 4140764 * 2
def baseEnd_4140764 : Nat := 1417468139222628317004653

theorem tailTrace_4140764 : CollatzResearch.WordTrace tailWord_4140764 prefixEnd_4140764 1417468139222628317004653 := by
  unfold tailWord_4140764
  simp only [CollatzResearch.WordTrace]
  refine ⟨75513035185363344517170673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100684046913817792689560897 75513035185363344517170673)
  ·
    refine ⟨56634776389022508387878005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75513035185363344517170673 56634776389022508387878005)
    ·
      refine ⟨5309510286470860161363563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56634776389022508387878005 5309510286470860161363563)
      ·
        refine ⟨7964265429706290242045345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309510286470860161363563 7964265429706290242045345)
        ·
          refine ⟨5973199072279717681534009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964265429706290242045345 5973199072279717681534009)
          ·
            refine ⟨4479899304209788261150507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5973199072279717681534009 4479899304209788261150507)
            ·
              refine ⟨6719848956314682391725761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479899304209788261150507 6719848956314682391725761)
              ·
                refine ⟨5039886717236011793794321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719848956314682391725761 5039886717236011793794321)
                ·
                  refine ⟨3779915037927008845345741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039886717236011793794321 3779915037927008845345741)
                  ·
                    refine ⟨1417468139222628317004653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779915037927008845345741 1417468139222628317004653)
                    ·
                      rfl

theorem cell22_4140764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4140764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140764 prefixEnd_4140764 := by exact prefixLift 4140764
  have htrace : WordTrace (prefixWord ++ tailWord_4140764) baseStart_4140764 baseEnd_4140764 := by
    simpa [prefixWord, tailWord_4140764, baseEnd_4140764] using wordTrace_append hprefix tailTrace_4140764
  have hstable : (prefixWord ++ tailWord_4140764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140764).length < 2 ^ (prefixWord ++ tailWord_4140764).sum := by decide
  have hdescent : baseEnd_4140764 < baseStart_4140764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140833 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 6]
def baseStart_4140833 : Nat := 118140960795 + 4140833 * 2 ^ 59
def prefixEnd_4140833 : Nat := 4983230072969 + 3 ^ 40 * 4140833 * 2
def baseEnd_4140833 : Nat := 472497253110911712343147

theorem tailTrace_4140833 : CollatzResearch.WordTrace tailWord_4140833 prefixEnd_4140833 472497253110911712343147 := by
  unfold tailWord_4140833
  simp only [CollatzResearch.WordTrace]
  refine ⟨151028587007476713818603153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100685724671651142545735435 151028587007476713818603153)
  ·
    refine ⟨113271440255607535363952365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151028587007476713818603153 113271440255607535363952365)
    ·
      refine ⟨42476790095852825761482137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113271440255607535363952365 42476790095852825761482137)
      ·
        refine ⟨31857592571889619321111603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42476790095852825761482137 31857592571889619321111603)
        ·
          refine ⟨47786388857834428981667405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31857592571889619321111603 47786388857834428981667405)
          ·
            refine ⟨17919895821687910868125277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47786388857834428981667405 17919895821687910868125277)
            ·
              refine ⟨6719960933132966575546979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17919895821687910868125277 6719960933132966575546979)
              ·
                refine ⟨10079941399699449863320469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719960933132966575546979 10079941399699449863320469)
                ·
                  refine ⟨472497253110911712343147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10079941399699449863320469 472497253110911712343147)
                  ·
                    rfl

theorem cell22_4140833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_4140833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140833 prefixEnd_4140833 := by exact prefixLift 4140833
  have htrace : WordTrace (prefixWord ++ tailWord_4140833) baseStart_4140833 baseEnd_4140833 := by
    simpa [prefixWord, tailWord_4140833, baseEnd_4140833] using wordTrace_append hprefix tailTrace_4140833
  have hstable : (prefixWord ++ tailWord_4140833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140833).length < 2 ^ (prefixWord ++ tailWord_4140833).sum := by decide
  have hdescent : baseEnd_4140833 < baseStart_4140833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140852 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4140852 : Nat := 118140960795 + 4140852 * 2 ^ 59
def prefixEnd_4140852 : Nat := 4983230072969 + 3 ^ 40 * 4140852 * 2
def baseEnd_4140852 : Nat := 1417498263421025420804383

theorem tailTrace_4140852 : CollatzResearch.WordTrace tailWord_4140852 prefixEnd_4140852 1417498263421025420804383 := by
  unfold tailWord_4140852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75514639997203940031772405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100686186662938586709029873 75514639997203940031772405)
  ·
    refine ⟨7079497499737869377978663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75514639997203940031772405 7079497499737869377978663)
    ·
      refine ⟨10619246249606804066967995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079497499737869377978663 10619246249606804066967995)
      ·
        refine ⟨15928869374410206100451993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619246249606804066967995 15928869374410206100451993)
        ·
          refine ⟨11946652030807654575338995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15928869374410206100451993 11946652030807654575338995)
          ·
            refine ⟨17919978046211481863008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946652030807654575338995 17919978046211481863008493)
            ·
              refine ⟨6719991767329305698628185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17919978046211481863008493 6719991767329305698628185)
              ·
                refine ⟨5039993825496979273971139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719991767329305698628185 5039993825496979273971139)
                ·
                  refine ⟨7559990738245468910956709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039993825496979273971139 7559990738245468910956709)
                  ·
                    refine ⟨1417498263421025420804383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559990738245468910956709 1417498263421025420804383)
                    ·
                      rfl

theorem cell22_4140852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4140852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140852 prefixEnd_4140852 := by exact prefixLift 4140852
  have htrace : WordTrace (prefixWord ++ tailWord_4140852) baseStart_4140852 baseEnd_4140852 := by
    simpa [prefixWord, tailWord_4140852, baseEnd_4140852] using wordTrace_append hprefix tailTrace_4140852
  have hstable : (prefixWord ++ tailWord_4140852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140852).length < 2 ^ (prefixWord ++ tailWord_4140852).sum := by decide
  have hdescent : baseEnd_4140852 < baseStart_4140852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140882 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_4140882 : Nat := 118140960795 + 4140882 * 2 ^ 59
def prefixEnd_4140882 : Nat := 4983230072969 + 3 ^ 40 * 4140882 * 2
def baseEnd_4140882 : Nat := 1417508533034115342554291

theorem tailTrace_4140882 : CollatzResearch.WordTrace tailWord_4140882 prefixEnd_4140882 1417508533034115342554291 := by
  unfold tailWord_4140882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757593546074798796784225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100686916122866130124757933 37757593546074798796784225)
  ·
    refine ⟨28318195159556099097588169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37757593546074798796784225 28318195159556099097588169)
    ·
      refine ⟨21238646369667074323191127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28318195159556099097588169 21238646369667074323191127)
      ·
        refine ⟨31857969554500611484786691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238646369667074323191127 31857969554500611484786691)
        ·
          refine ⟨47786954331750917227180037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31857969554500611484786691 47786954331750917227180037)
          ·
            refine ⟨8960053937203296980096257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47786954331750917227180037 8960053937203296980096257)
            ·
              refine ⟨6720040452902472735072193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8960053937203296980096257 6720040452902472735072193)
              ·
                refine ⟨5040030339676854551304145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720040452902472735072193 5040030339676854551304145)
                ·
                  refine ⟨3780022754757640913478109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040030339676854551304145 3780022754757640913478109)
                  ·
                    refine ⟨1417508533034115342554291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780022754757640913478109 1417508533034115342554291)
                    ·
                      rfl

theorem cell22_4140882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_4140882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140882 prefixEnd_4140882 := by exact prefixLift 4140882
  have htrace : WordTrace (prefixWord ++ tailWord_4140882) baseStart_4140882 baseEnd_4140882 := by
    simpa [prefixWord, tailWord_4140882, baseEnd_4140882] using wordTrace_append hprefix tailTrace_4140882
  have hstable : (prefixWord ++ tailWord_4140882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140882).length < 2 ^ (prefixWord ++ tailWord_4140882).sum := by decide
  have hdescent : baseEnd_4140882 < baseStart_4140882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140884 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4140884 : Nat := 118140960795 + 4140884 * 2 ^ 59
def prefixEnd_4140884 : Nat := 4983230072969 + 3 ^ 40 * 4140884 * 2
def baseEnd_4140884 : Nat := 472503072558329334668095

theorem tailTrace_4140884 : CollatzResearch.WordTrace tailWord_4140884 prefixEnd_4140884 472503072558329334668095 := by
  unfold tailWord_4140884
  simp only [CollatzResearch.WordTrace]
  refine ⟨75515223565145974764354853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100686964753527966352473137 75515223565145974764354853)
  ·
    refine ⟨14159104418464870268316535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75515223565145974764354853 14159104418464870268316535)
    ·
      refine ⟨21238656627697305402474803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159104418464870268316535 21238656627697305402474803)
      ·
        refine ⟨31857984941545958103712205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238656627697305402474803 31857984941545958103712205)
        ·
          refine ⟨11946744353079734288892077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31857984941545958103712205 11946744353079734288892077)
          ·
            refine ⟨4480029132404900358334529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11946744353079734288892077 4480029132404900358334529)
            ·
              refine ⟨3360021849303675268750897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480029132404900358334529 3360021849303675268750897)
              ·
                refine ⟨2520016386977756451563173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360021849303675268750897 2520016386977756451563173)
                ·
                  refine ⟨472503072558329334668095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520016386977756451563173 472503072558329334668095)
                  ·
                    rfl

theorem cell22_4140884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4140884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140884 prefixEnd_4140884 := by exact prefixLift 4140884
  have htrace : WordTrace (prefixWord ++ tailWord_4140884) baseStart_4140884 baseEnd_4140884 := by
    simpa [prefixWord, tailWord_4140884, baseEnd_4140884] using wordTrace_append hprefix tailTrace_4140884
  have hstable : (prefixWord ++ tailWord_4140884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140884).length < 2 ^ (prefixWord ++ tailWord_4140884).sum := by decide
  have hdescent : baseEnd_4140884 < baseStart_4140884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140953 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_4140953 : Nat := 118140960795 + 4140953 * 2 ^ 59
def prefixEnd_4140953 : Nat := 4983230072969 + 3 ^ 40 * 4140953 * 2
def baseEnd_4140953 : Nat := 1417532837785094824029073

theorem tailTrace_4140953 : CollatzResearch.WordTrace tailWord_4140953 prefixEnd_4140953 1417532837785094824029073 := by
  unfold tailWord_4140953
  simp only [CollatzResearch.WordTrace]
  refine ⟨151032963767041974312971513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688642511361316208647675 151032963767041974312971513)
  ·
    refine ⟨113274722825281480734728635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151032963767041974312971513 113274722825281480734728635)
    ·
      refine ⟨169912084237922221102092953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113274722825281480734728635 169912084237922221102092953)
      ·
        refine ⟨127434063178441665826569715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169912084237922221102092953 127434063178441665826569715)
        ·
          refine ⟨191151094767662498739854573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127434063178441665826569715 191151094767662498739854573)
          ·
            refine ⟨71681660537873437027445465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191151094767662498739854573 71681660537873437027445465)
            ·
              refine ⟨53761245403405077770584099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71681660537873437027445465 53761245403405077770584099)
              ·
                refine ⟨80641868105107616655876149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53761245403405077770584099 80641868105107616655876149)
                ·
                  refine ⟨7560175134853839061488389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80641868105107616655876149 7560175134853839061488389)
                  ·
                    refine ⟨1417532837785094824029073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560175134853839061488389 1417532837785094824029073)
                    ·
                      rfl

theorem cell22_4140953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_4140953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140953 prefixEnd_4140953 := by exact prefixLift 4140953
  have htrace : WordTrace (prefixWord ++ tailWord_4140953) baseStart_4140953 baseEnd_4140953 := by
    simpa [prefixWord, tailWord_4140953, baseEnd_4140953] using wordTrace_append hprefix tailTrace_4140953
  have hstable : (prefixWord ++ tailWord_4140953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140953).length < 2 ^ (prefixWord ++ tailWord_4140953).sum := by decide
  have hdescent : baseEnd_4140953 < baseStart_4140953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140957 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 5]
def baseStart_4140957 : Nat := 118140960795 + 4140957 * 2 ^ 59
def prefixEnd_4140957 : Nat := 4983230072969 + 3 ^ 40 * 4140957 * 2
def baseEnd_4140957 : Nat := 472511402355613382309687

theorem tailTrace_4140957 : CollatzResearch.WordTrace tailWord_4140957 prefixEnd_4140957 472511402355613382309687 := by
  unfold tailWord_4140957
  simp only [CollatzResearch.WordTrace]
  refine ⟨151033109659027482996117125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100688739772684988664078083 151033109659027482996117125)
  ·
    refine ⟨28318708061067653061771961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151033109659027482996117125 28318708061067653061771961)
    ·
      refine ⟨21239031045800739796328971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28318708061067653061771961 21239031045800739796328971)
      ·
        refine ⟨31858546568701109694493457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239031045800739796328971 31858546568701109694493457)
        ·
          refine ⟨23893909926525832270870093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31858546568701109694493457 23893909926525832270870093)
          ·
            refine ⟨8960216222447187101576285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23893909926525832270870093 8960216222447187101576285)
            ·
              refine ⟨3360081083417695163091107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8960216222447187101576285 3360081083417695163091107)
              ·
                refine ⟨5040121625126542744636661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360081083417695163091107 5040121625126542744636661)
                ·
                  refine ⟨472511402355613382309687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040121625126542744636661 472511402355613382309687)
                  ·
                    rfl

theorem cell22_4140957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_4140957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140957 prefixEnd_4140957 := by exact prefixLift 4140957
  have htrace : WordTrace (prefixWord ++ tailWord_4140957) baseStart_4140957 baseEnd_4140957 := by
    simpa [prefixWord, tailWord_4140957, baseEnd_4140957] using wordTrace_append hprefix tailTrace_4140957
  have hstable : (prefixWord ++ tailWord_4140957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140957).length < 2 ^ (prefixWord ++ tailWord_4140957).sum := by decide
  have hdescent : baseEnd_4140957 < baseStart_4140957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4140983 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_4140983 : Nat := 118140960795 + 4140983 * 2 ^ 59
def prefixEnd_4140983 : Nat := 4983230072969 + 3 ^ 40 * 4140983 * 2
def baseEnd_4140983 : Nat := 1417543107398184745778981

theorem tailTrace_4140983 : CollatzResearch.WordTrace tailWord_4140983 prefixEnd_4140983 1417543107398184745778981 := by
  unfold tailWord_4140983
  simp only [CollatzResearch.WordTrace]
  refine ⟨151034057956933289436563603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100689371971288859624375735 151034057956933289436563603)
  ·
    refine ⟨226551086935399934154845405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151034057956933289436563603 226551086935399934154845405)
    ·
      refine ⟨84956657600774975308067027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226551086935399934154845405 84956657600774975308067027)
      ·
        refine ⟨127434986401162462962100541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84956657600774975308067027 127434986401162462962100541)
        ·
          refine ⟨47788119900435923610787703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127434986401162462962100541 47788119900435923610787703)
          ·
            refine ⟨71682179850653885416181555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47788119900435923610787703 71682179850653885416181555)
            ·
              refine ⟨107523269775980828124272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71682179850653885416181555 107523269775980828124272333)
              ·
                refine ⟨40321226165992810546602125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107523269775980828124272333 40321226165992810546602125)
                ·
                  refine ⟨15120459812247303954975797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40321226165992810546602125 15120459812247303954975797)
                  ·
                    refine ⟨1417543107398184745778981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15120459812247303954975797 1417543107398184745778981)
                    ·
                      rfl

theorem cell22_4140983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_4140983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4140983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4140983 prefixEnd_4140983 := by exact prefixLift 4140983
  have htrace : WordTrace (prefixWord ++ tailWord_4140983) baseStart_4140983 baseEnd_4140983 := by
    simpa [prefixWord, tailWord_4140983, baseEnd_4140983] using wordTrace_append hprefix tailTrace_4140983
  have hstable : (prefixWord ++ tailWord_4140983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4140983).length < 2 ^ (prefixWord ++ tailWord_4140983).sum := by decide
  have hdescent : baseEnd_4140983 < baseStart_4140983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4140983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141021 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4141021 : Nat := 118140960795 + 4141021 * 2 ^ 59
def prefixEnd_4141021 : Nat := 4983230072969 + 3 ^ 40 * 4141021 * 2
def baseEnd_4141021 : Nat := 1417556115574765313328865

theorem tailTrace_4141021 : CollatzResearch.WordTrace tailWord_4141021 prefixEnd_4141021 1417556115574765313328865 := by
  unfold tailWord_4141021
  simp only [CollatzResearch.WordTrace]
  refine ⟨151035443930795621926446917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100690295953863747950964611 151035443930795621926446917)
  ·
    refine ⟨28319145737024179111208797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151035443930795621926446917 28319145737024179111208797)
    ·
      refine ⟨10619679651384067166703299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28319145737024179111208797 10619679651384067166703299)
      ·
        refine ⟨15929519477076100750054949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619679651384067166703299 15929519477076100750054949)
        ·
          refine ⟨2986784901951768890635303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15929519477076100750054949 2986784901951768890635303)
          ·
            refine ⟨4480177352927653335952955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986784901951768890635303 4480177352927653335952955)
            ·
              refine ⟨6720266029391480003929433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480177352927653335952955 6720266029391480003929433)
              ·
                refine ⟨5040199522043610002947075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720266029391480003929433 5040199522043610002947075)
                ·
                  refine ⟨7560299283065415004420613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040199522043610002947075 7560299283065415004420613)
                  ·
                    refine ⟨1417556115574765313328865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560299283065415004420613 1417556115574765313328865)
                    ·
                      rfl

theorem cell22_4141021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4141021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141021 prefixEnd_4141021 := by exact prefixLift 4141021
  have htrace : WordTrace (prefixWord ++ tailWord_4141021) baseStart_4141021 baseEnd_4141021 := by
    simpa [prefixWord, tailWord_4141021, baseEnd_4141021] using wordTrace_append hprefix tailTrace_4141021
  have hstable : (prefixWord ++ tailWord_4141021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141021).length < 2 ^ (prefixWord ++ tailWord_4141021).sum := by decide
  have hdescent : baseEnd_4141021 < baseStart_4141021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141043 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_4141043 : Nat := 118140960795 + 4141043 * 2 ^ 59
def prefixEnd_4141043 : Nat := 4983230072969 + 3 ^ 40 * 4141043 * 2
def baseEnd_4141043 : Nat := 1417563646624364589278797

theorem tailTrace_4141043 : CollatzResearch.WordTrace tailWord_4141043 prefixEnd_4141043 1417563646624364589278797 := by
  unfold tailWord_4141043
  simp only [CollatzResearch.WordTrace]
  refine ⟨151036246336715919683747783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100690830891143946455831855 151036246336715919683747783)
  ·
    refine ⟨226554369505073879525621675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151036246336715919683747783 226554369505073879525621675)
    ·
      refine ⟨339831554257610819288432513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226554369505073879525621675 339831554257610819288432513)
      ·
        refine ⟨254873665693208114466324385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339831554257610819288432513 254873665693208114466324385)
        ·
          refine ⟨191155249269906085849743289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254873665693208114466324385 191155249269906085849743289)
          ·
            refine ⟨143366436952429564387307467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191155249269906085849743289 143366436952429564387307467)
            ·
              refine ⟨215049655428644346580961201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143366436952429564387307467 215049655428644346580961201)
              ·
                refine ⟨161287241571483259935720901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215049655428644346580961201 161287241571483259935720901)
                ·
                  refine ⟨30241357794653111237947669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161287241571483259935720901 30241357794653111237947669)
                  ·
                    refine ⟨1417563646624364589278797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30241357794653111237947669 1417563646624364589278797)
                    ·
                      rfl

theorem cell22_4141043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_4141043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141043 prefixEnd_4141043 := by exact prefixLift 4141043
  have htrace : WordTrace (prefixWord ++ tailWord_4141043) baseStart_4141043 baseEnd_4141043 := by
    simpa [prefixWord, tailWord_4141043, baseEnd_4141043] using wordTrace_append hprefix tailTrace_4141043
  have hstable : (prefixWord ++ tailWord_4141043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141043).length < 2 ^ (prefixWord ++ tailWord_4141043).sum := by decide
  have hdescent : baseEnd_4141043 < baseStart_4141043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141075 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 5]
def baseStart_4141075 : Nat := 118140960795 + 4141075 * 2 ^ 59
def prefixEnd_4141075 : Nat := 4983230072969 + 3 ^ 40 * 4141075 * 2
def baseEnd_4141075 : Nat := 472524866959442390826233

theorem tailTrace_4141075 : CollatzResearch.WordTrace tailWord_4141075 prefixEnd_4141075 472524866959442390826233 := by
  unfold tailWord_4141075
  simp only [CollatzResearch.WordTrace]
  refine ⟨151037413472599989148912679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100691608981733326099275119 151037413472599989148912679)
  ·
    refine ⟨226556120208899983723369019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151037413472599989148912679 226556120208899983723369019)
    ·
      refine ⟨339834180313349975585053529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226556120208899983723369019 339834180313349975585053529)
      ·
        refine ⟨254875635235012481688790147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339834180313349975585053529 254875635235012481688790147)
        ·
          refine ⟨382313452852518722533185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254875635235012481688790147 382313452852518722533185221)
          ·
            refine ⟨71683772409847260474972229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382313452852518722533185221 71683772409847260474972229)
            ·
              refine ⟨13440707326846361339057293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71683772409847260474972229 13440707326846361339057293)
              ·
                refine ⟨5040265247567385502146485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440707326846361339057293 5040265247567385502146485)
                ·
                  refine ⟨472524866959442390826233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040265247567385502146485 472524866959442390826233)
                  ·
                    rfl

theorem cell22_4141075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 5].length) (baseStart_4141075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141075 prefixEnd_4141075 := by exact prefixLift 4141075
  have htrace : WordTrace (prefixWord ++ tailWord_4141075) baseStart_4141075 baseEnd_4141075 := by
    simpa [prefixWord, tailWord_4141075, baseEnd_4141075] using wordTrace_append hprefix tailTrace_4141075
  have hstable : (prefixWord ++ tailWord_4141075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141075).length < 2 ^ (prefixWord ++ tailWord_4141075).sum := by decide
  have hdescent : baseEnd_4141075 < baseStart_4141075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141079 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 3, 3]
def baseStart_4141079 : Nat := 118140960795 + 4141079 * 2 ^ 59
def prefixEnd_4141079 : Nat := 4983230072969 + 3 ^ 40 * 4141079 * 2
def baseEnd_4141079 : Nat := 1417575970160072495378687

theorem tailTrace_4141079 : CollatzResearch.WordTrace tailWord_4141079 prefixEnd_4141079 1417575970160072495378687 := by
  unfold tailWord_4141079
  simp only [CollatzResearch.WordTrace]
  refine ⟨151037559364585497832058291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100691706243056998554705527 151037559364585497832058291)
  ·
    refine ⟨226556339046878246748087437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151037559364585497832058291 226556339046878246748087437)
    ·
      refine ⟨84958627142579342530532789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226556339046878246748087437 84958627142579342530532789)
      ·
        refine ⟨7964871294616813362237449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84958627142579342530532789 7964871294616813362237449)
        ·
          refine ⟨5973653470962610021678087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964871294616813362237449 5973653470962610021678087)
          ·
            refine ⟨8960480206443915032517131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973653470962610021678087 8960480206443915032517131)
            ·
              refine ⟨13440720309665872548775697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960480206443915032517131 13440720309665872548775697)
              ·
                refine ⟨10080540232249404411581773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13440720309665872548775697 10080540232249404411581773)
                ·
                  refine ⟨3780202587093526654343165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10080540232249404411581773 3780202587093526654343165)
                  ·
                    refine ⟨1417575970160072495378687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780202587093526654343165 1417575970160072495378687)
                    ·
                      rfl

theorem cell22_4141079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_4141079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141079 prefixEnd_4141079 := by exact prefixLift 4141079
  have htrace : WordTrace (prefixWord ++ tailWord_4141079) baseStart_4141079 baseEnd_4141079 := by
    simpa [prefixWord, tailWord_4141079, baseEnd_4141079] using wordTrace_append hprefix tailTrace_4141079
  have hstable : (prefixWord ++ tailWord_4141079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141079).length < 2 ^ (prefixWord ++ tailWord_4141079).sum := by decide
  have hdescent : baseEnd_4141079 < baseStart_4141079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141090 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4141090 : Nat := 118140960795 + 4141090 * 2 ^ 59
def prefixEnd_4141090 : Nat := 4983230072969 + 3 ^ 40 * 4141090 * 2
def baseEnd_4141090 : Nat := 1417579735684872133353653

theorem tailTrace_4141090 : CollatzResearch.WordTrace tailWord_4141090 prefixEnd_4141090 1417579735684872133353653 := by
  unfold tailWord_4141090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759490141886411677677181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100691973711697097807139149 37759490141886411677677181)
  ·
    refine ⟨14159808803207404379128943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37759490141886411677677181 14159808803207404379128943)
    ·
      refine ⟨21239713204811106568693415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159808803207404379128943 21239713204811106568693415)
      ·
        refine ⟨31859569807216659853040123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239713204811106568693415 31859569807216659853040123)
        ·
          refine ⟨47789354710824989779560185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31859569807216659853040123 47789354710824989779560185)
          ·
            refine ⟨35842016033118742334670139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47789354710824989779560185 35842016033118742334670139)
            ·
              refine ⟨53763024049678113502005209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35842016033118742334670139 53763024049678113502005209)
              ·
                refine ⟨40322268037258585126503907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53763024049678113502005209 40322268037258585126503907)
                ·
                  refine ⟨60483402055887877689755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40322268037258585126503907 60483402055887877689755861)
                  ·
                    refine ⟨1417579735684872133353653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60483402055887877689755861 1417579735684872133353653)
                    ·
                      rfl

theorem cell22_4141090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4141090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141090 prefixEnd_4141090 := by exact prefixLift 4141090
  have htrace : WordTrace (prefixWord ++ tailWord_4141090) baseStart_4141090 baseEnd_4141090 := by
    simpa [prefixWord, tailWord_4141090, baseEnd_4141090] using wordTrace_append hprefix tailTrace_4141090
  have hstable : (prefixWord ++ tailWord_4141090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141090).length < 2 ^ (prefixWord ++ tailWord_4141090).sum := by decide
  have hdescent : baseEnd_4141090 < baseStart_4141090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141120 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_4141120 : Nat := 118140960795 + 4141120 * 2 ^ 59
def prefixEnd_4141120 : Nat := 4983230072969 + 3 ^ 40 * 4141120 * 2
def baseEnd_4141120 : Nat := 472530001765987351701187

theorem tailTrace_4141120 : CollatzResearch.WordTrace tailWord_4141120 prefixEnd_4141120 472530001765987351701187 := by
  unfold tailWord_4141120
  simp only [CollatzResearch.WordTrace]
  refine ⟨75519527378718480917150407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100692703171624641222867209 75519527378718480917150407)
  ·
    refine ⟨113279291068077721375725611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75519527378718480917150407 113279291068077721375725611)
    ·
      refine ⟨169918936602116582063588417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113279291068077721375725611 169918936602116582063588417)
      ·
        refine ⟨127439202451587436547691313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169918936602116582063588417 127439202451587436547691313)
        ·
          refine ⟨95579401838690577410768485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127439202451587436547691313 95579401838690577410768485)
          ·
            refine ⟨17921137844754483264519091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95579401838690577410768485 17921137844754483264519091)
            ·
              refine ⟨26881706767131724896778637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921137844754483264519091 26881706767131724896778637)
              ·
                refine ⟨10080640037674396836291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26881706767131724896778637 10080640037674396836291989)
                ·
                  refine ⟨472530001765987351701187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10080640037674396836291989 472530001765987351701187)
                  ·
                    rfl

theorem cell22_4141120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_4141120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141120 prefixEnd_4141120 := by exact prefixLift 4141120
  have htrace : WordTrace (prefixWord ++ tailWord_4141120) baseStart_4141120 baseEnd_4141120 := by
    simpa [prefixWord, tailWord_4141120, baseEnd_4141120] using wordTrace_append hprefix tailTrace_4141120
  have hstable : (prefixWord ++ tailWord_4141120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141120).length < 2 ^ (prefixWord ++ tailWord_4141120).sum := by decide
  have hdescent : baseEnd_4141120 < baseStart_4141120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141126 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4141126 : Nat := 118140960795 + 4141126 * 2 ^ 59
def prefixEnd_4141126 : Nat := 4983230072969 + 3 ^ 40 * 4141126 * 2
def baseEnd_4141126 : Nat := 472530686406860013151181

theorem tailTrace_4141126 : CollatzResearch.WordTrace tailWord_4141126 prefixEnd_4141126 472530686406860013151181 := by
  unfold tailWord_4141126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719977299856725776844351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100692849063610149906012821 4719977299856725776844351)
  ·
    refine ⟨7079965949785088665266527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4719977299856725776844351 7079965949785088665266527)
    ·
      refine ⟨10619948924677632997899791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079965949785088665266527 10619948924677632997899791)
      ·
        refine ⟨15929923387016449496849687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619948924677632997899791 15929923387016449496849687)
        ·
          refine ⟨23894885080524674245274531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15929923387016449496849687 23894885080524674245274531)
          ·
            refine ⟨35842327620787011367911797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23894885080524674245274531 35842327620787011367911797)
            ·
              refine ⟨3360218214448782315741731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35842327620787011367911797 3360218214448782315741731)
              ·
                refine ⟨5040327321673173473612597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360218214448782315741731 5040327321673173473612597)
                ·
                  refine ⟨472530686406860013151181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040327321673173473612597 472530686406860013151181)
                  ·
                    rfl

theorem cell22_4141126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4141126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141126 prefixEnd_4141126 := by exact prefixLift 4141126
  have htrace : WordTrace (prefixWord ++ tailWord_4141126) baseStart_4141126 baseEnd_4141126 := by
    simpa [prefixWord, tailWord_4141126, baseEnd_4141126] using wordTrace_append hprefix tailTrace_4141126
  have hstable : (prefixWord ++ tailWord_4141126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141126).length < 2 ^ (prefixWord ++ tailWord_4141126).sum := by decide
  have hdescent : baseEnd_4141126 < baseStart_4141126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141152 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_4141152 : Nat := 118140960795 + 4141152 * 2 ^ 59
def prefixEnd_4141152 : Nat := 4983230072969 + 3 ^ 40 * 4141152 * 2
def baseEnd_4141152 : Nat := 1417600959551924638303463

theorem tailTrace_4141152 : CollatzResearch.WordTrace tailWord_4141152 prefixEnd_4141152 1417600959551924638303463 := by
  unfold tailWord_4141152
  simp only [CollatzResearch.WordTrace]
  refine ⟨75520110946660515649732855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100693481262214020866310473 75520110946660515649732855)
  ·
    refine ⟨113280166419990773474599283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75520110946660515649732855 113280166419990773474599283)
    ·
      refine ⟨169920249629986160211898925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113280166419990773474599283 169920249629986160211898925)
      ·
        refine ⟨63720093611244810079462097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169920249629986160211898925 63720093611244810079462097)
        ·
          refine ⟨47790070208433607559596573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63720093611244810079462097 47790070208433607559596573)
          ·
            refine ⟨17921276328162602834848715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47790070208433607559596573 17921276328162602834848715)
            ·
              refine ⟨26881914492243904252273073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921276328162602834848715 26881914492243904252273073)
              ·
                refine ⟨20161435869182928189204805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26881914492243904252273073 20161435869182928189204805)
                ·
                  refine ⟨3780269225471799035475901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20161435869182928189204805 3780269225471799035475901)
                  ·
                    refine ⟨1417600959551924638303463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780269225471799035475901 1417600959551924638303463)
                    ·
                      rfl

theorem cell22_4141152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_4141152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141152 prefixEnd_4141152 := by exact prefixLift 4141152
  have htrace : WordTrace (prefixWord ++ tailWord_4141152) baseStart_4141152 baseEnd_4141152 := by
    simpa [prefixWord, tailWord_4141152, baseEnd_4141152] using wordTrace_append hprefix tailTrace_4141152
  have hstable : (prefixWord ++ tailWord_4141152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141152).length < 2 ^ (prefixWord ++ tailWord_4141152).sum := by decide
  have hdescent : baseEnd_4141152 < baseStart_4141152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141167 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_4141167 : Nat := 118140960795 + 4141167 * 2 ^ 59
def prefixEnd_4141167 : Nat := 4983230072969 + 3 ^ 40 * 4141167 * 2
def baseEnd_4141167 : Nat := 1417606094358469599178417

theorem tailTrace_4141167 : CollatzResearch.WordTrace tailWord_4141167 prefixEnd_4141167 1417606094358469599178417 := by
  unfold tailWord_4141167
  simp only [CollatzResearch.WordTrace]
  refine ⟨151040768988266688861261755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100693845992177792574174503 151040768988266688861261755)
  ·
    refine ⟨226561153482400033291892633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151040768988266688861261755 226561153482400033291892633)
    ·
      refine ⟨169920865111800024968919475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226561153482400033291892633 169920865111800024968919475)
      ·
        refine ⟨254881297667700037453379213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169920865111800024968919475 254881297667700037453379213)
        ·
          refine ⟨95580486625387514045017205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254881297667700037453379213 95580486625387514045017205)
          ·
            refine ⟨8960670621130079441720363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95580486625387514045017205 8960670621130079441720363)
            ·
              refine ⟨13441005931695119162580545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960670621130079441720363 13441005931695119162580545)
              ·
                refine ⟨10080754448771339371935409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13441005931695119162580545 10080754448771339371935409)
                ·
                  refine ⟨7560565836578504528951557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080754448771339371935409 7560565836578504528951557)
                  ·
                    refine ⟨1417606094358469599178417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560565836578504528951557 1417606094358469599178417)
                    ·
                      rfl

theorem cell22_4141167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_4141167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141167 prefixEnd_4141167 := by exact prefixLift 4141167
  have htrace : WordTrace (prefixWord ++ tailWord_4141167) baseStart_4141167 baseEnd_4141167 := by
    simpa [prefixWord, tailWord_4141167, baseEnd_4141167] using wordTrace_append hprefix tailTrace_4141167
  have hstable : (prefixWord ++ tailWord_4141167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141167).length < 2 ^ (prefixWord ++ tailWord_4141167).sum := by decide
  have hdescent : baseEnd_4141167 < baseStart_4141167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141304 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_4141304 : Nat := 118140960795 + 4141304 * 2 ^ 59
def prefixEnd_4141304 : Nat := 4983230072969 + 3 ^ 40 * 4141304 * 2
def baseEnd_4141304 : Nat := 1417652992258246908502997

theorem tailTrace_4141304 : CollatzResearch.WordTrace tailWord_4141304 prefixEnd_4141304 1417652992258246908502997 := by
  unfold tailWord_4141304
  simp only [CollatzResearch.WordTrace]
  refine ⟨75522882894385180629499483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100697177192513574172665977 75522882894385180629499483)
  ·
    refine ⟨113284324341577770944249225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75522882894385180629499483 113284324341577770944249225)
    ·
      refine ⟨84963243256183328208186919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113284324341577770944249225 84963243256183328208186919)
      ·
        refine ⟨127444864884274992312280379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84963243256183328208186919 127444864884274992312280379)
        ·
          refine ⟨191167297326412488468420569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127444864884274992312280379 191167297326412488468420569)
          ·
            refine ⟨143375472994809366351315427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191167297326412488468420569 143375472994809366351315427)
            ·
              refine ⟨215063209492214049526973141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143375472994809366351315427 215063209492214049526973141)
              ·
                refine ⟨5040543972473766785788433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215063209492214049526973141 5040543972473766785788433)
                ·
                  refine ⟨3780407979355325089341325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040543972473766785788433 3780407979355325089341325)
                  ·
                    refine ⟨1417652992258246908502997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780407979355325089341325 1417652992258246908502997)
                    ·
                      rfl

theorem cell22_4141304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_4141304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141304 prefixEnd_4141304 := by exact prefixLift 4141304
  have htrace : WordTrace (prefixWord ++ tailWord_4141304) baseStart_4141304 baseEnd_4141304 := by
    simpa [prefixWord, tailWord_4141304, baseEnd_4141304] using wordTrace_append hprefix tailTrace_4141304
  have hstable : (prefixWord ++ tailWord_4141304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141304).length < 2 ^ (prefixWord ++ tailWord_4141304).sum := by decide
  have hdescent : baseEnd_4141304 < baseStart_4141304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141347 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_4141347 : Nat := 118140960795 + 4141347 * 2 ^ 59
def prefixEnd_4141347 : Nat := 4983230072969 + 3 ^ 40 * 4141347 * 2
def baseEnd_4141347 : Nat := 1417667712037009129677865

theorem tailTrace_4141347 : CollatzResearch.WordTrace tailWord_4141347 prefixEnd_4141347 1417667712037009129677865 := by
  unfold tailWord_4141347
  simp only [CollatzResearch.WordTrace]
  refine ⟨151047334127614579602814295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100698222751743053068542863 151047334127614579602814295)
  ·
    refine ⟨226571001191421869404221443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151047334127614579602814295 226571001191421869404221443)
    ·
      refine ⟨339856501787132804106332165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226571001191421869404221443 339856501787132804106332165)
      ·
        refine ⟨63723094085087400769937281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339856501787132804106332165 63723094085087400769937281)
        ·
          refine ⟨47792320563815550577452961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63723094085087400769937281 47792320563815550577452961)
          ·
            refine ⟨35844240422861662933089721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47792320563815550577452961 35844240422861662933089721)
            ·
              refine ⟨26883180317146247199817291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35844240422861662933089721 26883180317146247199817291)
              ·
                refine ⟨40324770475719370799725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26883180317146247199817291 40324770475719370799725937)
                ·
                  refine ⟨30243577856789528099794453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40324770475719370799725937 30243577856789528099794453)
                  ·
                    refine ⟨1417667712037009129677865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30243577856789528099794453 1417667712037009129677865)
                    ·
                      rfl

theorem cell22_4141347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_4141347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141347 prefixEnd_4141347 := by exact prefixLift 4141347
  have htrace : WordTrace (prefixWord ++ tailWord_4141347) baseStart_4141347 baseEnd_4141347 := by
    simpa [prefixWord, tailWord_4141347, baseEnd_4141347] using wordTrace_append hprefix tailTrace_4141347
  have hstable : (prefixWord ++ tailWord_4141347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141347).length < 2 ^ (prefixWord ++ tailWord_4141347).sum := by decide
  have hdescent : baseEnd_4141347 < baseStart_4141347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141396 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4141396 : Nat := 118140960795 + 4141396 * 2 ^ 59
def prefixEnd_4141396 : Nat := 4983230072969 + 3 ^ 40 * 4141396 * 2
def baseEnd_4141396 : Nat := 472561495246129778400905

theorem tailTrace_4141396 : CollatzResearch.WordTrace tailWord_4141396 prefixEnd_4141396 472561495246129778400905 := by
  unfold tailWord_4141396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524560652218530485674021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100699414202958040647565361 75524560652218530485674021)
  ·
    refine ⟨14160855122290974466063879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75524560652218530485674021 14160855122290974466063879)
    ·
      refine ⟨21241282683436461699095819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160855122290974466063879 21241282683436461699095819)
      ·
        refine ⟨31861924025154692548643729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21241282683436461699095819 31861924025154692548643729)
        ·
          refine ⟨23896443018866019411482797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31861924025154692548643729 23896443018866019411482797)
          ·
            refine ⟨8961166132074757279306049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23896443018866019411482797 8961166132074757279306049)
            ·
              refine ⟨6720874599056067959479537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961166132074757279306049 6720874599056067959479537)
              ·
                refine ⟨5040655949292050969609653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720874599056067959479537 5040655949292050969609653)
                ·
                  refine ⟨472561495246129778400905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040655949292050969609653 472561495246129778400905)
                  ·
                    rfl

theorem cell22_4141396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4141396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141396 prefixEnd_4141396 := by exact prefixLift 4141396
  have htrace : WordTrace (prefixWord ++ tailWord_4141396) baseStart_4141396 baseEnd_4141396 := by
    simpa [prefixWord, tailWord_4141396, baseEnd_4141396] using wordTrace_append hprefix tailTrace_4141396
  have hstable : (prefixWord ++ tailWord_4141396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141396).length < 2 ^ (prefixWord ++ tailWord_4141396).sum := by decide
  have hdescent : baseEnd_4141396 < baseStart_4141396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141424 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_4141424 : Nat := 118140960795 + 4141424 * 2 ^ 59
def prefixEnd_4141424 : Nat := 4983230072969 + 3 ^ 40 * 4141424 * 2
def baseEnd_4141424 : Nat := 472564690236868865167543

theorem tailTrace_4141424 : CollatzResearch.WordTrace tailWord_4141424 prefixEnd_4141424 472564690236868865167543 := by
  unfold tailWord_4141424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75525071274167810876683663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100700095032223747835578217 75525071274167810876683663)
  ·
    refine ⟨113287606911251716315025495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75525071274167810876683663 113287606911251716315025495)
    ·
      refine ⟨169931410366877574472538243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113287606911251716315025495 169931410366877574472538243)
      ·
        refine ⟨254897115550316361708807365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169931410366877574472538243 254897115550316361708807365)
        ·
          refine ⟨47793209165684317820401381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254897115550316361708807365 47793209165684317820401381)
          ·
            refine ⟨8961226718565809591325259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47793209165684317820401381 8961226718565809591325259)
            ·
              refine ⟨13441840077848714386987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961226718565809591325259 13441840077848714386987889)
              ·
                refine ⟨10081380058386535790240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13441840077848714386987889 10081380058386535790240917)
                ·
                  refine ⟨472564690236868865167543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10081380058386535790240917 472564690236868865167543)
                  ·
                    rfl

theorem cell22_4141424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_4141424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141424 prefixEnd_4141424 := by exact prefixLift 4141424
  have htrace : WordTrace (prefixWord ++ tailWord_4141424) baseStart_4141424 baseEnd_4141424 := by
    simpa [prefixWord, tailWord_4141424, baseEnd_4141424] using wordTrace_append hprefix tailTrace_4141424
  have hstable : (prefixWord ++ tailWord_4141424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141424).length < 2 ^ (prefixWord ++ tailWord_4141424).sum := by decide
  have hdescent : baseEnd_4141424 < baseStart_4141424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141439 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 6, 3]
def baseStart_4141439 : Nat := 118140960795 + 4141439 * 2 ^ 59
def prefixEnd_4141439 : Nat := 4983230072969 + 3 ^ 40 * 4141439 * 2
def baseEnd_4141439 : Nat := 1417699205517151556377583

theorem tailTrace_4141439 : CollatzResearch.WordTrace tailWord_4141439 prefixEnd_4141439 1417699205517151556377583 := by
  unfold tailWord_4141439
  simp only [CollatzResearch.WordTrace]
  refine ⟨151050689643281279315163371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100700459762187519543442247 151050689643281279315163371)
  ·
    refine ⟨226576034464921918972745057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151050689643281279315163371 226576034464921918972745057)
    ·
      refine ⟨169932025848691439229558793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226576034464921918972745057 169932025848691439229558793)
      ·
        refine ⟨127449019386518579422169095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169932025848691439229558793 127449019386518579422169095)
        ·
          refine ⟨191173529079777869133253643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127449019386518579422169095 191173529079777869133253643)
          ·
            refine ⟨286760293619666803699880465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191173529079777869133253643 286760293619666803699880465)
            ·
              refine ⟨215070220214750102774910349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286760293619666803699880465 215070220214750102774910349)
              ·
                refine ⟨80651332580531288540591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215070220214750102774910349 80651332580531288540591381)
                ·
                  refine ⟨3780531214712404150340221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80651332580531288540591381 3780531214712404150340221)
                  ·
                    refine ⟨1417699205517151556377583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780531214712404150340221 1417699205517151556377583)
                    ·
                      rfl

theorem cell22_4141439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_4141439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141439 prefixEnd_4141439 := by exact prefixLift 4141439
  have htrace : WordTrace (prefixWord ++ tailWord_4141439) baseStart_4141439 baseEnd_4141439 := by
    simpa [prefixWord, tailWord_4141439, baseEnd_4141439] using wordTrace_append hprefix tailTrace_4141439
  have hstable : (prefixWord ++ tailWord_4141439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141439).length < 2 ^ (prefixWord ++ tailWord_4141439).sum := by decide
  have hdescent : baseEnd_4141439 < baseStart_4141439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141514 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_4141514 : Nat := 118140960795 + 4141514 * 2 ^ 59
def prefixEnd_4141514 : Nat := 4983230072969 + 3 ^ 40 * 4141514 * 2
def baseEnd_4141514 : Nat := 472574959849958786917451

theorem tailTrace_4141514 : CollatzResearch.WordTrace tailWord_4141514 prefixEnd_4141514 472574959849958786917451 := by
  unfold tailWord_4141514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763356279502391781035899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100702283412006378082762397 37763356279502391781035899)
  ·
    refine ⟨56645034419253587671553849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37763356279502391781035899 56645034419253587671553849)
    ·
      refine ⟨42483775814440190753665387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56645034419253587671553849 42483775814440190753665387)
      ·
        refine ⟨63725663721660286130498081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42483775814440190753665387 63725663721660286130498081)
        ·
          refine ⟨47794247791245214597873561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63725663721660286130498081 47794247791245214597873561)
          ·
            refine ⟨35845685843433910948405171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47794247791245214597873561 35845685843433910948405171)
            ·
              refine ⟨53768528765150866422607757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35845685843433910948405171 53768528765150866422607757)
              ·
                refine ⟨20163198286931574908477909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53768528765150866422607757 20163198286931574908477909)
                ·
                  refine ⟨472574959849958786917451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20163198286931574908477909 472574959849958786917451)
                  ·
                    rfl

theorem cell22_4141514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_4141514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141514 prefixEnd_4141514 := by exact prefixLift 4141514
  have htrace : WordTrace (prefixWord ++ tailWord_4141514) baseStart_4141514 baseEnd_4141514 := by
    simpa [prefixWord, tailWord_4141514, baseEnd_4141514] using wordTrace_append hprefix tailTrace_4141514
  have hstable : (prefixWord ++ tailWord_4141514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141514).length < 2 ^ (prefixWord ++ tailWord_4141514).sum := by decide
  have hdescent : baseEnd_4141514 < baseStart_4141514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141529 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_4141529 : Nat := 118140960795 + 4141529 * 2 ^ 59
def prefixEnd_4141529 : Nat := 4983230072969 + 3 ^ 40 * 4141529 * 2
def baseEnd_4141529 : Nat := 1417730014356421321627307

theorem tailTrace_4141529 : CollatzResearch.WordTrace tailWord_4141529 prefixEnd_4141529 1417730014356421321627307 := by
  unfold tailWord_4141529
  simp only [CollatzResearch.WordTrace]
  refine ⟨151053972212955224685939641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100702648141970149790626427 151053972212955224685939641)
  ·
    refine ⟨113290479159716418514454731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151053972212955224685939641 113290479159716418514454731)
    ·
      refine ⟨169935718739574627771682097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113290479159716418514454731 169935718739574627771682097)
      ·
        refine ⟨127451789054680970828761573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169935718739574627771682097 127451789054680970828761573)
        ·
          refine ⟨23897210447752682030392795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127451789054680970828761573 23897210447752682030392795)
          ·
            refine ⟨35845815671629023045589193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23897210447752682030392795 35845815671629023045589193)
            ·
              refine ⟨26884361753721767284191895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35845815671629023045589193 26884361753721767284191895)
              ·
                refine ⟨40326542630582650926287843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26884361753721767284191895 40326542630582650926287843)
                ·
                  refine ⟨60489813945873976389431765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40326542630582650926287843 60489813945873976389431765)
                  ·
                    refine ⟨1417730014356421321627307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60489813945873976389431765 1417730014356421321627307)
                    ·
                      rfl

theorem cell22_4141529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_4141529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141529 prefixEnd_4141529 := by exact prefixLift 4141529
  have htrace : WordTrace (prefixWord ++ tailWord_4141529) baseStart_4141529 baseEnd_4141529 := by
    simpa [prefixWord, tailWord_4141529, baseEnd_4141529] using wordTrace_append hprefix tailTrace_4141529
  have hstable : (prefixWord ++ tailWord_4141529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141529).length < 2 ^ (prefixWord ++ tailWord_4141529).sum := by decide
  have hdescent : baseEnd_4141529 < baseStart_4141529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141561 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_4141561 : Nat := 118140960795 + 4141561 * 2 ^ 59
def prefixEnd_4141561 : Nat := 4983230072969 + 3 ^ 40 * 4141561 * 2
def baseEnd_4141561 : Nat := 1417740968610383904827209

theorem tailTrace_4141561 : CollatzResearch.WordTrace tailWord_4141561 prefixEnd_4141561 1417740968610383904827209 := by
  unfold tailWord_4141561
  simp only [CollatzResearch.WordTrace]
  refine ⟨151055139348839294151104537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100703426232559529434069691 151055139348839294151104537)
  ·
    refine ⟨113291354511629470613328403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151055139348839294151104537 113291354511629470613328403)
    ·
      refine ⟨169937031767444205919992605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113291354511629470613328403 169937031767444205919992605)
      ·
        refine ⟨63726386912791577219997227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169937031767444205919992605 63726386912791577219997227)
        ·
          refine ⟨95589580369187365829995841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63726386912791577219997227 95589580369187365829995841)
          ·
            refine ⟨71692185276890524372496881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95589580369187365829995841 71692185276890524372496881)
            ·
              refine ⟨53769138957667893279372661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71692185276890524372496881 53769138957667893279372661)
              ·
                refine ⟨5040856777281364994941187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53769138957667893279372661 5040856777281364994941187)
                ·
                  refine ⟨7561285165922047492411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040856777281364994941187 7561285165922047492411781)
                  ·
                    refine ⟨1417740968610383904827209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561285165922047492411781 1417740968610383904827209)
                    ·
                      rfl

theorem cell22_4141561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_4141561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141561 prefixEnd_4141561 := by exact prefixLift 4141561
  have htrace : WordTrace (prefixWord ++ tailWord_4141561) baseStart_4141561 baseEnd_4141561 := by
    simpa [prefixWord, tailWord_4141561, baseEnd_4141561] using wordTrace_append hprefix tailTrace_4141561
  have hstable : (prefixWord ++ tailWord_4141561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141561).length < 2 ^ (prefixWord ++ tailWord_4141561).sum := by decide
  have hdescent : baseEnd_4141561 < baseStart_4141561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141608 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4141608 : Nat := 118140960795 + 4141608 * 2 ^ 59
def prefixEnd_4141608 : Nat := 4983230072969 + 3 ^ 40 * 4141608 * 2
def baseEnd_4141608 : Nat := 1417757057670891448902065

theorem tailTrace_4141608 : CollatzResearch.WordTrace tailWord_4141608 prefixEnd_4141608 1417757057670891448902065 := by
  unfold tailWord_4141608
  simp only [CollatzResearch.WordTrace]
  refine ⟨75528426789834510589032739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100704569053112680785376985 75528426789834510589032739)
  ·
    refine ⟨113292640184751765883549109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75528426789834510589032739 113292640184751765883549109)
    ·
      refine ⟨10621185017320478051582729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113292640184751765883549109 10621185017320478051582729)
      ·
        refine ⟨7965888762990358538687047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10621185017320478051582729 7965888762990358538687047)
        ·
          refine ⟨11948833144485537808030571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965888762990358538687047 11948833144485537808030571)
          ·
            refine ⟨17923249716728306712045857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11948833144485537808030571 17923249716728306712045857)
            ·
              refine ⟨13442437287546230034034393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923249716728306712045857 13442437287546230034034393)
              ·
                refine ⟨10081827965659672525525795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13442437287546230034034393 10081827965659672525525795)
                ·
                  refine ⟨15122741948489508788288693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10081827965659672525525795 15122741948489508788288693)
                  ·
                    refine ⟨1417757057670891448902065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15122741948489508788288693 1417757057670891448902065)
                    ·
                      rfl

theorem cell22_4141608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4141608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141608 prefixEnd_4141608 := by exact prefixLift 4141608
  have htrace : WordTrace (prefixWord ++ tailWord_4141608) baseStart_4141608 baseEnd_4141608 := by
    simpa [prefixWord, tailWord_4141608, baseEnd_4141608] using wordTrace_append hprefix tailTrace_4141608
  have hstable : (prefixWord ++ tailWord_4141608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141608).length < 2 ^ (prefixWord ++ tailWord_4141608).sum := by decide
  have hdescent : baseEnd_4141608 < baseStart_4141608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141610 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_4141610 : Nat := 118140960795 + 4141610 * 2 ^ 59
def prefixEnd_4141610 : Nat := 4983230072969 + 3 ^ 40 * 4141610 * 2
def baseEnd_4141610 : Nat := 472585914103921370117353

theorem tailTrace_4141610 : CollatzResearch.WordTrace tailWord_4141610 prefixEnd_4141610 472585914103921370117353 := by
  unfold tailWord_4141610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37764231631415443879909571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100704617683774517013092189 37764231631415443879909571)
  ·
    refine ⟨56646347447123165819864357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37764231631415443879909571 56646347447123165819864357)
    ·
      refine ⟨10621190146335593591224567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56646347447123165819864357 10621190146335593591224567)
      ·
        refine ⟨15931785219503390386836851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621190146335593591224567 15931785219503390386836851)
        ·
          refine ⟨23897677829255085580255277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15931785219503390386836851 23897677829255085580255277)
          ·
            refine ⟨8961629185970657092595729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23897677829255085580255277 8961629185970657092595729)
            ·
              refine ⟨6721221889477992819446797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961629185970657092595729 6721221889477992819446797)
              ·
                refine ⟨2520458208554247307292549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6721221889477992819446797 2520458208554247307292549)
                ·
                  refine ⟨472585914103921370117353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520458208554247307292549 472585914103921370117353)
                  ·
                    rfl

theorem cell22_4141610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_4141610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141610 prefixEnd_4141610 := by exact prefixLift 4141610
  have htrace : WordTrace (prefixWord ++ tailWord_4141610) baseStart_4141610 baseEnd_4141610 := by
    simpa [prefixWord, tailWord_4141610, baseEnd_4141610] using wordTrace_append hprefix tailTrace_4141610
  have hstable : (prefixWord ++ tailWord_4141610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141610).length < 2 ^ (prefixWord ++ tailWord_4141610).sum := by decide
  have hdescent : baseEnd_4141610 < baseStart_4141610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141653 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_4141653 : Nat := 118140960795 + 4141653 * 2 ^ 59
def prefixEnd_4141653 : Nat := 4983230072969 + 3 ^ 40 * 4141653 * 2
def baseEnd_4141653 : Nat := 1417772462090526331526927

theorem tailTrace_4141653 : CollatzResearch.WordTrace tailWord_4141653 prefixEnd_4141653 1417772462090526331526927 := by
  unfold tailWord_4141653
  simp only [CollatzResearch.WordTrace]
  refine ⟨151058494864505993863453613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100705663243003995908969075 151058494864505993863453613)
  ·
    refine ⟨56646935574189747698795105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151058494864505993863453613 56646935574189747698795105)
    ·
      refine ⟨42485201680642310774096329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56646935574189747698795105 42485201680642310774096329)
      ·
        refine ⟨31863901260481733080572247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42485201680642310774096329 31863901260481733080572247)
        ·
          refine ⟨47795851890722599620858371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31863901260481733080572247 47795851890722599620858371)
          ·
            refine ⟨71693777836083899431287557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47795851890722599620858371 71693777836083899431287557)
            ·
              refine ⟨13442583344265731143366417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71693777836083899431287557 13442583344265731143366417)
              ·
                refine ⟨10081937508199298357524813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13442583344265731143366417 10081937508199298357524813)
                ·
                  refine ⟨3780726565574736884071805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10081937508199298357524813 3780726565574736884071805)
                  ·
                    refine ⟨1417772462090526331526927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780726565574736884071805 1417772462090526331526927)
                    ·
                      rfl

theorem cell22_4141653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_4141653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141653 prefixEnd_4141653 := by exact prefixLift 4141653
  have htrace : WordTrace (prefixWord ++ tailWord_4141653) baseStart_4141653 baseEnd_4141653 := by
    simpa [prefixWord, tailWord_4141653, baseEnd_4141653] using wordTrace_append hprefix tailTrace_4141653
  have hstable : (prefixWord ++ tailWord_4141653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141653).length < 2 ^ (prefixWord ++ tailWord_4141653).sum := by decide
  have hdescent : baseEnd_4141653 < baseStart_4141653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141700 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_4141700 : Nat := 118140960795 + 4141700 * 2 ^ 59
def prefixEnd_4141700 : Nat := 4983230072969 + 3 ^ 40 * 4141700 * 2
def baseEnd_4141700 : Nat := 472596183717011291867261

theorem tailTrace_4141700 : CollatzResearch.WordTrace tailWord_4141700 prefixEnd_4141700 472596183717011291867261 := by
  unfold tailWord_4141700
  simp only [CollatzResearch.WordTrace]
  refine ⟨75530104547667860445207277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100706806063557147260276369 75530104547667860445207277)
  ·
    refine ⟨28323789205375447666952729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75530104547667860445207277 28323789205375447666952729)
    ·
      refine ⟨21242841904031585750214547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28323789205375447666952729 21242841904031585750214547)
      ·
        refine ⟨31864262856047378625321821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21242841904031585750214547 31864262856047378625321821)
        ·
          refine ⟨11949098571017766984495683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31864262856047378625321821 11949098571017766984495683)
          ·
            refine ⟨17923647856526650476743525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949098571017766984495683 17923647856526650476743525)
            ·
              refine ⟨3360683973098746964389411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17923647856526650476743525 3360683973098746964389411)
              ·
                refine ⟨5041025959648120446584117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360683973098746964389411 5041025959648120446584117)
                ·
                  refine ⟨472596183717011291867261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041025959648120446584117 472596183717011291867261)
                  ·
                    rfl

theorem cell22_4141700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_4141700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141700 prefixEnd_4141700 := by exact prefixLift 4141700
  have htrace : WordTrace (prefixWord ++ tailWord_4141700) baseStart_4141700 baseEnd_4141700 := by
    simpa [prefixWord, tailWord_4141700, baseEnd_4141700] using wordTrace_append hprefix tailTrace_4141700
  have hstable : (prefixWord ++ tailWord_4141700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141700).length < 2 ^ (prefixWord ++ tailWord_4141700).sum := by decide
  have hdescent : baseEnd_4141700 < baseStart_4141700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141738 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4141738 : Nat := 118140960795 + 4141738 * 2 ^ 59
def prefixEnd_4141738 : Nat := 4983230072969 + 3 ^ 40 * 4141738 * 2
def baseEnd_4141738 : Nat := 1417801559327614443151667

theorem tailTrace_4141738 : CollatzResearch.WordTrace tailWord_4141738 prefixEnd_4141738 1417801559327614443151667 := by
  unfold tailWord_4141738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37765398767299513345074467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100707730046132035586865245 37765398767299513345074467)
  ·
    refine ⟨56648098150949270017611701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37765398767299513345074467 56648098150949270017611701)
    ·
      refine ⟨5310759201651494064151097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56648098150949270017611701 5310759201651494064151097)
      ·
        refine ⟨3983069401238620548113323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5310759201651494064151097 3983069401238620548113323)
        ·
          refine ⟨5974604101857930822169985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983069401238620548113323 5974604101857930822169985)
          ·
            refine ⟨4480953076393448116627489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974604101857930822169985 4480953076393448116627489)
            ·
              refine ⟨3360714807295086087470617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480953076393448116627489 3360714807295086087470617)
              ·
                refine ⟨2520536105471314565602963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360714807295086087470617 2520536105471314565602963)
                ·
                  refine ⟨3780804158206971848404445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520536105471314565602963 3780804158206971848404445)
                  ·
                    refine ⟨1417801559327614443151667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780804158206971848404445 1417801559327614443151667)
                    ·
                      rfl

theorem cell22_4141738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4141738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141738 prefixEnd_4141738 := by exact prefixLift 4141738
  have htrace : WordTrace (prefixWord ++ tailWord_4141738) baseStart_4141738 baseEnd_4141738 := by
    simpa [prefixWord, tailWord_4141738, baseEnd_4141738] using wordTrace_append hprefix tailTrace_4141738
  have hstable : (prefixWord ++ tailWord_4141738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141738).length < 2 ^ (prefixWord ++ tailWord_4141738).sum := by decide
  have hdescent : baseEnd_4141738 < baseStart_4141738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141758 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4141758 : Nat := 118140960795 + 4141758 * 2 ^ 59
def prefixEnd_4141758 : Nat := 4983230072969 + 3 ^ 40 * 4141758 * 2
def baseEnd_4141758 : Nat := 1417808405736341057651605

theorem tailTrace_4141758 : CollatzResearch.WordTrace tailWord_4141758 prefixEnd_4141758 1417808405736341057651605 := by
  unfold tailWord_4141758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882790566140699599503241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100708216352750397864017285 18882790566140699599503241)
  ·
    refine ⟨14162092924605524699627431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18882790566140699599503241 14162092924605524699627431)
    ·
      refine ⟨21243139386908287049441147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162092924605524699627431 21243139386908287049441147)
      ·
        refine ⟨31864709080362430574161721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243139386908287049441147 31864709080362430574161721)
        ·
          refine ⟨23898531810271822930621291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31864709080362430574161721 23898531810271822930621291)
          ·
            refine ⟨35847797715407734395931937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898531810271822930621291 35847797715407734395931937)
            ·
              refine ⟨26885848286555800796948953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35847797715407734395931937 26885848286555800796948953)
              ·
                refine ⟨20164386214916850597711715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26885848286555800796948953 20164386214916850597711715)
                ·
                  refine ⟨30246579322375275896567573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164386214916850597711715 30246579322375275896567573)
                  ·
                    refine ⟨1417808405736341057651605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30246579322375275896567573 1417808405736341057651605)
                    ·
                      rfl

theorem cell22_4141758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4141758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141758 prefixEnd_4141758 := by exact prefixLift 4141758
  have htrace : WordTrace (prefixWord ++ tailWord_4141758) baseStart_4141758 baseEnd_4141758 := by
    simpa [prefixWord, tailWord_4141758, baseEnd_4141758] using wordTrace_append hprefix tailTrace_4141758
  have hstable : (prefixWord ++ tailWord_4141758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141758).length < 2 ^ (prefixWord ++ tailWord_4141758).sum := by decide
  have hdescent : baseEnd_4141758 < baseStart_4141758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141760 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_4141760 : Nat := 118140960795 + 4141760 * 2 ^ 59
def prefixEnd_4141760 : Nat := 4983230072969 + 3 ^ 40 * 4141760 * 2
def baseEnd_4141760 : Nat := 1417809090377213719101599

theorem tailTrace_4141760 : CollatzResearch.WordTrace tailWord_4141760 prefixEnd_4141760 1417809090377213719101599 := by
  unfold tailWord_4141760
  simp only [CollatzResearch.WordTrace]
  refine ⟨75531198737559175568799367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100708264983412234091732489 75531198737559175568799367)
  ·
    refine ⟨113296798106338763353199051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75531198737559175568799367 113296798106338763353199051)
    ·
      refine ⟨169945197159508145029798577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113296798106338763353199051 169945197159508145029798577)
      ·
        refine ⟨127458897869631108772348933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169945197159508145029798577 127458897869631108772348933)
        ·
          refine ⟨23898543350555832894815425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127458897869631108772348933 23898543350555832894815425)
          ·
            refine ⟨17923907512916874671111569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23898543350555832894815425 17923907512916874671111569)
            ·
              refine ⟨13442930634687656003333677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923907512916874671111569 13442930634687656003333677)
              ·
                refine ⟨5041098988007871001250129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13442930634687656003333677 5041098988007871001250129)
                ·
                  refine ⟨3780824241005903250937597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041098988007871001250129 3780824241005903250937597)
                  ·
                    refine ⟨1417809090377213719101599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780824241005903250937597 1417809090377213719101599)
                    ·
                      rfl

theorem cell22_4141760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_4141760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141760 prefixEnd_4141760 := by exact prefixLift 4141760
  have htrace : WordTrace (prefixWord ++ tailWord_4141760) baseStart_4141760 baseEnd_4141760 := by
    simpa [prefixWord, tailWord_4141760, baseEnd_4141760] using wordTrace_append hprefix tailTrace_4141760
  have hstable : (prefixWord ++ tailWord_4141760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141760).length < 2 ^ (prefixWord ++ tailWord_4141760).sum := by decide
  have hdescent : baseEnd_4141760 < baseStart_4141760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141781 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_4141781 : Nat := 118140960795 + 4141781 * 2 ^ 59
def prefixEnd_4141781 : Nat := 4983230072969 + 3 ^ 40 * 4141781 * 2
def baseEnd_4141781 : Nat := 1417816279106376664326535

theorem tailTrace_4141781 : CollatzResearch.WordTrace tailWord_4141781 prefixEnd_4141781 1417816279106376664326535 := by
  unfold tailWord_4141781
  simp only [CollatzResearch.WordTrace]
  refine ⟨151063163408042271724113197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100708775605361514482742131 151063163408042271724113197)
  ·
    refine ⟨56648686278015851896542449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151063163408042271724113197 56648686278015851896542449)
    ·
      refine ⟨42486514708511888922406837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56648686278015851896542449 42486514708511888922406837)
      ·
        refine ⟨3983110753922989586475641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42486514708511888922406837 3983110753922989586475641)
        ·
          refine ⟨2987333065442242189856731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983110753922989586475641 2987333065442242189856731)
          ·
            refine ⟨4480999598163363284785097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987333065442242189856731 4480999598163363284785097)
            ·
              refine ⟨3360749698622522463588823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480999598163363284785097 3360749698622522463588823)
              ·
                refine ⟨5041124547933783695383235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360749698622522463588823 5041124547933783695383235)
                ·
                  refine ⟨7561686821900675543074853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041124547933783695383235 7561686821900675543074853)
                  ·
                    refine ⟨1417816279106376664326535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561686821900675543074853 1417816279106376664326535)
                    ·
                      rfl

theorem cell22_4141781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_4141781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141781 prefixEnd_4141781 := by exact prefixLift 4141781
  have htrace : WordTrace (prefixWord ++ tailWord_4141781) baseStart_4141781 baseEnd_4141781 := by
    simpa [prefixWord, tailWord_4141781, baseEnd_4141781] using wordTrace_append hprefix tailTrace_4141781
  have hstable : (prefixWord ++ tailWord_4141781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141781).length < 2 ^ (prefixWord ++ tailWord_4141781).sum := by decide
  have hdescent : baseEnd_4141781 < baseStart_4141781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141818 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_4141818 : Nat := 118140960795 + 4141818 * 2 ^ 59
def prefixEnd_4141818 : Nat := 4983230072969 + 3 ^ 40 * 4141818 * 2
def baseEnd_4141818 : Nat := 472609648320840300383807

theorem tailTrace_4141818 : CollatzResearch.WordTrace tailWord_4141818 prefixEnd_4141818 472609648320840300383807 := by
  unfold tailWord_4141818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37766128227227056760802527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100709675272605484695473405 37766128227227056760802527)
  ·
    refine ⟨56649192340840585141203791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37766128227227056760802527 56649192340840585141203791)
    ·
      refine ⟨84973788511260877711805687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56649192340840585141203791 84973788511260877711805687)
      ·
        refine ⟨127460682766891316567708531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84973788511260877711805687 127460682766891316567708531)
        ·
          refine ⟨191191024150336974851562797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127460682766891316567708531 191191024150336974851562797)
          ·
            refine ⟨71696634056376365569336049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191191024150336974851562797 71696634056376365569336049)
            ·
              refine ⟨53772475542282274177002037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71696634056376365569336049 53772475542282274177002037)
              ·
                refine ⟨5041169582088963204093941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53772475542282274177002037 5041169582088963204093941)
                ·
                  refine ⟨472609648320840300383807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041169582088963204093941 472609648320840300383807)
                  ·
                    rfl

theorem cell22_4141818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_4141818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141818 prefixEnd_4141818 := by exact prefixLift 4141818
  have htrace : WordTrace (prefixWord ++ tailWord_4141818) baseStart_4141818 baseEnd_4141818 := by
    simpa [prefixWord, tailWord_4141818, baseEnd_4141818] using wordTrace_append hprefix tailTrace_4141818
  have hstable : (prefixWord ++ tailWord_4141818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141818).length < 2 ^ (prefixWord ++ tailWord_4141818).sum := by decide
  have hdescent : baseEnd_4141818 < baseStart_4141818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141822 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4141822 : Nat := 118140960795 + 4141822 * 2 ^ 59
def prefixEnd_4141822 : Nat := 4983230072969 + 3 ^ 40 * 4141822 * 2
def baseEnd_4141822 : Nat := 1417830314244266224051409

theorem tailTrace_4141822 : CollatzResearch.WordTrace tailWord_4141822 prefixEnd_4141822 1417830314244266224051409 := by
  unfold tailWord_4141822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883082350111716965794465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100709772533929157150903813 18883082350111716965794465)
  ·
    refine ⟨14162311762583787724345849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18883082350111716965794465 14162311762583787724345849)
    ·
      refine ⟨10621733821937840793259387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14162311762583787724345849 10621733821937840793259387)
      ·
        refine ⟨15932600732906761189889081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621733821937840793259387 15932600732906761189889081)
        ·
          refine ⟨11949450549680070892416811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15932600732906761189889081 11949450549680070892416811)
          ·
            refine ⟨17924175824520106338625217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949450549680070892416811 17924175824520106338625217)
            ·
              refine ⟨13443131868390079753968913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17924175824520106338625217 13443131868390079753968913)
              ·
                refine ⟨10082348901292559815476685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443131868390079753968913 10082348901292559815476685)
                ·
                  refine ⟨3780880837984709930803757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10082348901292559815476685 3780880837984709930803757)
                  ·
                    refine ⟨1417830314244266224051409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780880837984709930803757 1417830314244266224051409)
                    ·
                      rfl

theorem cell22_4141822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4141822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141822 prefixEnd_4141822 := by exact prefixLift 4141822
  have htrace : WordTrace (prefixWord ++ tailWord_4141822) baseStart_4141822 baseEnd_4141822 := by
    simpa [prefixWord, tailWord_4141822, baseEnd_4141822] using wordTrace_append hprefix tailTrace_4141822
  have hstable : (prefixWord ++ tailWord_4141822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141822).length < 2 ^ (prefixWord ++ tailWord_4141822).sum := by decide
  have hdescent : baseEnd_4141822 < baseStart_4141822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141848 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_4141848 : Nat := 118140960795 + 4141848 * 2 ^ 59
def prefixEnd_4141848 : Nat := 4983230072969 + 3 ^ 40 * 4141848 * 2
def baseEnd_4141848 : Nat := 1417839214575610822901329

theorem tailTrace_4141848 : CollatzResearch.WordTrace tailWord_4141848 prefixEnd_4141848 1417839214575610822901329 := by
  unfold tailWord_4141848
  simp only [CollatzResearch.WordTrace]
  refine ⟨75532803549399771083401099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100710404732533028111201465 75532803549399771083401099)
  ·
    refine ⟨113299205324099656625101649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75532803549399771083401099 113299205324099656625101649)
    ·
      refine ⟨84974403993074742468826237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113299205324099656625101649 84974403993074742468826237)
      ·
        refine ⟨31865401497403028425809839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84974403993074742468826237 31865401497403028425809839)
        ·
          refine ⟨47798102246104542638714759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31865401497403028425809839 47798102246104542638714759)
          ·
            refine ⟨71697153369156813958072139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47798102246104542638714759 71697153369156813958072139)
            ·
              refine ⟨107545730053735220937108209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71697153369156813958072139 107545730053735220937108209)
              ·
                refine ⟨80659297540301415702831157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107545730053735220937108209 80659297540301415702831157)
                ·
                  refine ⟨7561809144403257722140421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80659297540301415702831157 7561809144403257722140421)
                  ·
                    refine ⟨1417839214575610822901329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561809144403257722140421 1417839214575610822901329)
                    ·
                      rfl

theorem cell22_4141848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_4141848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141848 prefixEnd_4141848 := by exact prefixLift 4141848
  have htrace : WordTrace (prefixWord ++ tailWord_4141848) baseStart_4141848 baseEnd_4141848 := by
    simpa [prefixWord, tailWord_4141848, baseEnd_4141848] using wordTrace_append hprefix tailTrace_4141848
  have hstable : (prefixWord ++ tailWord_4141848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141848).length < 2 ^ (prefixWord ++ tailWord_4141848).sum := by decide
  have hdescent : baseEnd_4141848 < baseStart_4141848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141869 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 5]
def baseStart_4141869 : Nat := 118140960795 + 4141869 * 2 ^ 59
def prefixEnd_4141869 : Nat := 4983230072969 + 3 ^ 40 * 4141869 * 2
def baseEnd_4141869 : Nat := 472615467768257922708755

theorem tailTrace_4141869 : CollatzResearch.WordTrace tailWord_4141869 prefixEnd_4141869 472615467768257922708755 := by
  unfold tailWord_4141869
  simp only [CollatzResearch.WordTrace]
  refine ⟨151066373031723462753316661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100710915354482308502211107 151066373031723462753316661)
  ·
    refine ⟨14162472471724074633123437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151066373031723462753316661 14162472471724074633123437)
    ·
      refine ⟨5310927176896527987421289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14162472471724074633123437 5310927176896527987421289)
      ·
        refine ⟨3983195382672395990565967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5310927176896527987421289 3983195382672395990565967)
        ·
          refine ⟨5974793074008593985848951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983195382672395990565967 5974793074008593985848951)
          ·
            refine ⟨8962189611012890978773427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974793074008593985848951 8962189611012890978773427)
            ·
              refine ⟨13443284416519336468160141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962189611012890978773427 13443284416519336468160141)
              ·
                refine ⟨5041231656194751175560053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13443284416519336468160141 5041231656194751175560053)
                ·
                  refine ⟨472615467768257922708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041231656194751175560053 472615467768257922708755)
                  ·
                    rfl

theorem cell22_4141869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_4141869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141869 prefixEnd_4141869 := by exact prefixLift 4141869
  have htrace : WordTrace (prefixWord ++ tailWord_4141869) baseStart_4141869 baseEnd_4141869 := by
    simpa [prefixWord, tailWord_4141869, baseEnd_4141869] using wordTrace_append hprefix tailTrace_4141869
  have hstable : (prefixWord ++ tailWord_4141869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141869).length < 2 ^ (prefixWord ++ tailWord_4141869).sum := by decide
  have hdescent : baseEnd_4141869 < baseStart_4141869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141908 : List Nat := [2, 4, 1, 1, 14]
def baseStart_4141908 : Nat := 118140960795 + 4141908 * 2 ^ 59
def prefixEnd_4141908 : Nat := 4983230072969 + 3 ^ 40 * 4141908 * 2
def baseEnd_4141908 : Nat := 5834813801653459532515

theorem tailTrace_4141908 : CollatzResearch.WordTrace tailWord_4141908 prefixEnd_4141908 5834813801653459532515 := by
  unfold tailWord_4141908
  simp only [CollatzResearch.WordTrace]
  refine ⟨75533897739291086206993189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100711863652388114942657585 75533897739291086206993189)
  ·
    refine ⟨14162605826117078663811223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75533897739291086206993189 14162605826117078663811223)
    ·
      refine ⟨21243908739175617995716835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162605826117078663811223 21243908739175617995716835)
      ·
        refine ⟨31865863108763426993575253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243908739175617995716835 31865863108763426993575253)
        ·
          refine ⟨5834813801653459532515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 31865863108763426993575253 5834813801653459532515)
          ·
            rfl

theorem cell22_4141908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 14].length) (baseStart_4141908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141908 prefixEnd_4141908 := by exact prefixLift 4141908
  have htrace : WordTrace (prefixWord ++ tailWord_4141908) baseStart_4141908 baseEnd_4141908 := by
    simpa [prefixWord, tailWord_4141908, baseEnd_4141908] using wordTrace_append hprefix tailTrace_4141908
  have hstable : (prefixWord ++ tailWord_4141908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141908).length < 2 ^ (prefixWord ++ tailWord_4141908).sum := by decide
  have hdescent : baseEnd_4141908 < baseStart_4141908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4141914 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_4141914 : Nat := 118140960795 + 4141914 * 2 ^ 59
def prefixEnd_4141914 : Nat := 4983230072969 + 3 ^ 40 * 4141914 * 2
def baseEnd_4141914 : Nat := 472620602574802883583709

theorem tailTrace_4141914 : CollatzResearch.WordTrace tailWord_4141914 prefixEnd_4141914 472620602574802883583709 := by
  unfold tailWord_4141914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767003579140108859676199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100712009544373623625803197 37767003579140108859676199)
  ·
    refine ⟨56650505368710163289514299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37767003579140108859676199 56650505368710163289514299)
    ·
      refine ⟨84975758053065244934271449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56650505368710163289514299 84975758053065244934271449)
      ·
        refine ⟨63731818539798933700703587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84975758053065244934271449 63731818539798933700703587)
        ·
          refine ⟨95597727809698400551055381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63731818539798933700703587 95597727809698400551055381)
          ·
            refine ⟨4481143491079612525830721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95597727809698400551055381 4481143491079612525830721)
            ·
              refine ⟨3360857618309709394373041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481143491079612525830721 3360857618309709394373041)
              ·
                refine ⟨2520643213732282045779781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360857618309709394373041 2520643213732282045779781)
                ·
                  refine ⟨472620602574802883583709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520643213732282045779781 472620602574802883583709)
                  ·
                    rfl

theorem cell22_4141914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_4141914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4141914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4141914 prefixEnd_4141914 := by exact prefixLift 4141914
  have htrace : WordTrace (prefixWord ++ tailWord_4141914) baseStart_4141914 baseEnd_4141914 := by
    simpa [prefixWord, tailWord_4141914, baseEnd_4141914] using wordTrace_append hprefix tailTrace_4141914
  have hstable : (prefixWord ++ tailWord_4141914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4141914).length < 2 ^ (prefixWord ++ tailWord_4141914).sum := by decide
  have hdescent : baseEnd_4141914 < baseStart_4141914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4141914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142098 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4142098 : Nat := 118140960795 + 4142098 * 2 ^ 59
def prefixEnd_4142098 : Nat := 4983230072969 + 3 ^ 40 * 4142098 * 2
def baseEnd_4142098 : Nat := 1417924794684693504150563

theorem tailTrace_4142098 : CollatzResearch.WordTrace tailWord_4142098 prefixEnd_4142098 1417924794684693504150563 := by
  unfold tailWord_4142098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768681336973458715850737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100716483565262556575601965 37768681336973458715850737)
  ·
    refine ⟨28326511002730094036888053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37768681336973458715850737 28326511002730094036888053)
    ·
      refine ⟨2655610406505946315958255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28326511002730094036888053 2655610406505946315958255)
      ·
        refine ⟨3983415609758919473937383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655610406505946315958255 3983415609758919473937383)
        ·
          refine ⟨5975123414638379210906075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983415609758919473937383 5975123414638379210906075)
          ·
            refine ⟨8962685121957568816359113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975123414638379210906075 8962685121957568816359113)
            ·
              refine ⟨6722013841468176612269335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8962685121957568816359113 6722013841468176612269335)
              ·
                refine ⟨10083020762202264918404003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722013841468176612269335 10083020762202264918404003)
                ·
                  refine ⟨15124531143303397377606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083020762202264918404003 15124531143303397377606005)
                  ·
                    refine ⟨1417924794684693504150563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15124531143303397377606005 1417924794684693504150563)
                    ·
                      rfl

theorem cell22_4142098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4142098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142098 prefixEnd_4142098 := by exact prefixLift 4142098
  have htrace : WordTrace (prefixWord ++ tailWord_4142098) baseStart_4142098 baseEnd_4142098 := by
    simpa [prefixWord, tailWord_4142098, baseEnd_4142098] using wordTrace_append hprefix tailTrace_4142098
  have hstable : (prefixWord ++ tailWord_4142098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142098).length < 2 ^ (prefixWord ++ tailWord_4142098).sum := by decide
  have hdescent : baseEnd_4142098 < baseStart_4142098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142137 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_4142137 : Nat := 118140960795 + 4142137 * 2 ^ 59
def prefixEnd_4142137 : Nat := 4983230072969 + 3 ^ 40 * 4142137 * 2
def baseEnd_4142137 : Nat := 1417938145181710402425443

theorem tailTrace_4142137 : CollatzResearch.WordTrace tailWord_4142137 prefixEnd_4142137 1417938145181710402425443 := by
  unfold tailWord_4142137
  simp only [CollatzResearch.WordTrace]
  refine ⟨151076147794752544524072665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100717431863168363016048443 151076147794752544524072665)
  ·
    refine ⟨113307110846064408393054499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151076147794752544524072665 113307110846064408393054499)
    ·
      refine ⟨169960666269096612589581749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113307110846064408393054499 169960666269096612589581749)
      ·
        refine ⟨15933812462727807430273289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169960666269096612589581749 15933812462727807430273289)
        ·
          refine ⟨11950359347045855572704967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15933812462727807430273289 11950359347045855572704967)
          ·
            refine ⟨17925539020568783359057451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950359347045855572704967 17925539020568783359057451)
            ·
              refine ⟨26888308530853175038586177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17925539020568783359057451 26888308530853175038586177)
              ·
                refine ⟨20166231398139881278939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26888308530853175038586177 20166231398139881278939633)
                ·
                  refine ⟨15124673548604910959204725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20166231398139881278939633 15124673548604910959204725)
                  ·
                    refine ⟨1417938145181710402425443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15124673548604910959204725 1417938145181710402425443)
                    ·
                      rfl

theorem cell22_4142137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_4142137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142137 prefixEnd_4142137 := by exact prefixLift 4142137
  have htrace : WordTrace (prefixWord ++ tailWord_4142137) baseStart_4142137 baseEnd_4142137 := by
    simpa [prefixWord, tailWord_4142137, baseEnd_4142137] using wordTrace_append hprefix tailTrace_4142137
  have hstable : (prefixWord ++ tailWord_4142137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142137).length < 2 ^ (prefixWord ++ tailWord_4142137).sum := by decide
  have hdescent : baseEnd_4142137 < baseStart_4142137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142199 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 2, 3]
def baseStart_4142199 : Nat := 118140960795 + 4142199 * 2 ^ 59
def prefixEnd_4142199 : Nat := 4983230072969 + 3 ^ 40 * 4142199 * 2
def baseEnd_4142199 : Nat := 1417959369048762907375253

theorem tailTrace_4142199 : CollatzResearch.WordTrace tailWord_4142199 prefixEnd_4142199 1417959369048762907375253 := by
  unfold tailWord_4142199
  simp only [CollatzResearch.WordTrace]
  refine ⟨151078409120527929112829651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100718939413685286075219767 151078409120527929112829651)
  ·
    refine ⟨226617613680791893669244477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151078409120527929112829651 226617613680791893669244477)
    ·
      refine ⟨84981605130296960125966679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226617613680791893669244477 84981605130296960125966679)
      ·
        refine ⟨127472407695445440188950019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84981605130296960125966679 127472407695445440188950019)
        ·
          refine ⟨191208611543168160283425029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127472407695445440188950019 191208611543168160283425029)
          ·
            refine ⟨35851614664344030053142193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191208611543168160283425029 35851614664344030053142193)
            ·
              refine ⟨26888710998258022539856645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35851614664344030053142193 26888710998258022539856645)
              ·
                refine ⟨5041633312173379226223121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26888710998258022539856645 5041633312173379226223121)
                ·
                  refine ⟨3781224984130034419667341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041633312173379226223121 3781224984130034419667341)
                  ·
                    refine ⟨1417959369048762907375253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781224984130034419667341 1417959369048762907375253)
                    ·
                      rfl

theorem cell22_4142199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_4142199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142199 prefixEnd_4142199 := by exact prefixLift 4142199
  have htrace : WordTrace (prefixWord ++ tailWord_4142199) baseStart_4142199 baseEnd_4142199 := by
    simpa [prefixWord, tailWord_4142199, baseEnd_4142199] using wordTrace_append hprefix tailTrace_4142199
  have hstable : (prefixWord ++ tailWord_4142199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142199).length < 2 ^ (prefixWord ++ tailWord_4142199).sum := by decide
  have hdescent : baseEnd_4142199 < baseStart_4142199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142201 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 6]
def baseStart_4142201 : Nat := 118140960795 + 4142201 * 2 ^ 59
def prefixEnd_4142201 : Nat := 4983230072969 + 3 ^ 40 * 4142201 * 2
def baseEnd_4142201 : Nat := 472653351229878522941749

theorem tailTrace_4142201 : CollatzResearch.WordTrace tailWord_4142201 prefixEnd_4142201 472653351229878522941749 := by
  unfold tailWord_4142201
  simp only [CollatzResearch.WordTrace]
  refine ⟨151078482066520683454402457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100718988044347122302934971 151078482066520683454402457)
  ·
    refine ⟨113308861549890512590801843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151078482066520683454402457 113308861549890512590801843)
    ·
      refine ⟨169963292324835768886202765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113308861549890512590801843 169963292324835768886202765)
      ·
        refine ⟨63736234621813413332326037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169963292324835768886202765 63736234621813413332326037)
        ·
          refine ⟨2987635997897503749952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63736234621813413332326037 2987635997897503749952783)
          ·
            refine ⟨4481453996846255624929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987635997897503749952783 4481453996846255624929175)
            ·
              refine ⟨6722180995269383437393763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4481453996846255624929175 6722180995269383437393763)
              ·
                refine ⟨10083271492904075156090645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722180995269383437393763 10083271492904075156090645)
                ·
                  refine ⟨472653351229878522941749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10083271492904075156090645 472653351229878522941749)
                  ·
                    rfl

theorem cell22_4142201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_4142201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142201 prefixEnd_4142201 := by exact prefixLift 4142201
  have htrace : WordTrace (prefixWord ++ tailWord_4142201) baseStart_4142201 baseEnd_4142201 := by
    simpa [prefixWord, tailWord_4142201, baseEnd_4142201] using wordTrace_append hprefix tailTrace_4142201
  have hstable : (prefixWord ++ tailWord_4142201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142201).length < 2 ^ (prefixWord ++ tailWord_4142201).sum := by decide
  have hdescent : baseEnd_4142201 < baseStart_4142201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142212 : List Nat := [2, 3, 2, 1, 2, 2, 1, 9]
def baseStart_4142212 : Nat := 118140960795 + 4142212 * 2 ^ 59
def prefixEnd_4142212 : Nat := 4983230072969 + 3 ^ 40 * 4142212 * 2
def baseEnd_4142212 : Nat := 157551535468270578533357

theorem tailTrace_4142212 : CollatzResearch.WordTrace tailWord_4142212 prefixEnd_4142212 157551535468270578533357 := by
  unfold tailWord_4142212
  simp only [CollatzResearch.WordTrace]
  refine ⟨75539441634740416166526445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100719255512987221555368593 75539441634740416166526445)
  ·
    refine ⟨28327290613027656062447417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75539441634740416166526445 28327290613027656062447417)
    ·
      refine ⟨21245467959770742046835563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28327290613027656062447417 21245467959770742046835563)
      ·
        refine ⟨31868201939656113070253345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21245467959770742046835563 31868201939656113070253345)
        ·
          refine ⟨23901151454742084802690009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31868201939656113070253345 23901151454742084802690009)
          ·
            refine ⟨17925863591056563602017507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23901151454742084802690009 17925863591056563602017507)
            ·
              refine ⟨26888795386584845403026261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17925863591056563602017507 26888795386584845403026261)
              ·
                refine ⟨157551535468270578533357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26888795386584845403026261 157551535468270578533357)
                ·
                  rfl

theorem cell22_4142212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_4142212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142212 prefixEnd_4142212 := by exact prefixLift 4142212
  have htrace : WordTrace (prefixWord ++ tailWord_4142212) baseStart_4142212 baseEnd_4142212 := by
    simpa [prefixWord, tailWord_4142212, baseEnd_4142212] using wordTrace_append hprefix tailTrace_4142212
  have hstable : (prefixWord ++ tailWord_4142212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142212).length < 2 ^ (prefixWord ++ tailWord_4142212).sum := by decide
  have hdescent : baseEnd_4142212 < baseStart_4142212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142370 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4142370 : Nat := 118140960795 + 4142370 * 2 ^ 59
def prefixEnd_4142370 : Nat := 4983230072969 + 3 ^ 40 * 4142370 * 2
def baseEnd_4142370 : Nat := 472672635281125153783243

theorem tailTrace_4142370 : CollatzResearch.WordTrace tailWord_4142370 prefixEnd_4142370 472672635281125153783243 := by
  unfold tailWord_4142370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37771161500727106329326141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100723097335272283544869709 37771161500727106329326141)
  ·
    refine ⟨14164185562772664873497303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37771161500727106329326141 14164185562772664873497303)
    ·
      refine ⟨21246278344158997310245955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14164185562772664873497303 21246278344158997310245955)
      ·
        refine ⟨31869417516238495965368933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21246278344158997310245955 31869417516238495965368933)
        ·
          refine ⟨5975515784294717993506675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31869417516238495965368933 5975515784294717993506675)
          ·
            refine ⟨8963273676442076990260013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975515784294717993506675 8963273676442076990260013)
            ·
              refine ⟨3361227628665778871347505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8963273676442076990260013 3361227628665778871347505)
              ·
                refine ⟨2520920721499334153510629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361227628665778871347505 2520920721499334153510629)
                ·
                  refine ⟨472672635281125153783243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520920721499334153510629 472672635281125153783243)
                  ·
                    rfl

theorem cell22_4142370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4142370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142370 prefixEnd_4142370 := by exact prefixLift 4142370
  have htrace : WordTrace (prefixWord ++ tailWord_4142370) baseStart_4142370 baseEnd_4142370 := by
    simpa [prefixWord, tailWord_4142370, baseEnd_4142370] using wordTrace_append hprefix tailTrace_4142370
  have hstable : (prefixWord ++ tailWord_4142370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142370).length < 2 ^ (prefixWord ++ tailWord_4142370).sum := by decide
  have hdescent : baseEnd_4142370 < baseStart_4142370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142379 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 9, 3]
def baseStart_4142379 : Nat := 118140960795 + 4142379 * 2 ^ 59
def prefixEnd_4142379 : Nat := 4983230072969 + 3 ^ 40 * 4142379 * 2
def baseEnd_4142379 : Nat := 1418020986727302437874701

theorem tailTrace_4142379 : CollatzResearch.WordTrace tailWord_4142379 prefixEnd_4142379 1418020986727302437874701 := by
  unfold tailWord_4142379
  simp only [CollatzResearch.WordTrace]
  refine ⟨151084974259875819854382191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100723316173250546569588127 151084974259875819854382191)
  ·
    refine ⟨226627461389813729781573287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151084974259875819854382191 226627461389813729781573287)
    ·
      refine ⟨339941192084720594672359931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226627461389813729781573287 339941192084720594672359931)
      ·
        refine ⟨509911788127080892008539897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339941192084720594672359931 509911788127080892008539897)
        ·
          refine ⟨382433841095310669006404923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509911788127080892008539897 382433841095310669006404923)
          ·
            refine ⟨573650761642966003509607385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382433841095310669006404923 573650761642966003509607385)
            ·
              refine ⟨430238071232224502632205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573650761642966003509607385 430238071232224502632205539)
              ·
                refine ⟨645357106848336753948308309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430238071232224502632205539 645357106848336753948308309)
                ·
                  refine ⟨3781389297939473167665869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 645357106848336753948308309 3781389297939473167665869)
                  ·
                    refine ⟨1418020986727302437874701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781389297939473167665869 1418020986727302437874701)
                    ·
                      rfl

theorem cell22_4142379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 3].length) (baseStart_4142379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142379 prefixEnd_4142379 := by exact prefixLift 4142379
  have htrace : WordTrace (prefixWord ++ tailWord_4142379) baseStart_4142379 baseEnd_4142379 := by
    simpa [prefixWord, tailWord_4142379, baseEnd_4142379] using wordTrace_append hprefix tailTrace_4142379
  have hstable : (prefixWord ++ tailWord_4142379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142379).length < 2 ^ (prefixWord ++ tailWord_4142379).sum := by decide
  have hdescent : baseEnd_4142379 < baseStart_4142379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142381 : List Nat := [1, 5, 3, 1, 1, 1, 1, 9]
def baseStart_4142381 : Nat := 118140960795 + 4142381 * 2 ^ 59
def prefixEnd_4142381 : Nat := 4983230072969 + 3 ^ 40 * 4142381 * 2
def baseEnd_4142381 : Nat := 157557963485352788813855

theorem tailTrace_4142381 : CollatzResearch.WordTrace tailWord_4142381 prefixEnd_4142381 157557963485352788813855 := by
  unfold tailWord_4142381
  simp only [CollatzResearch.WordTrace]
  refine ⟨151085047205868574195954997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100723364803912382797303331 151085047205868574195954997)
  ·
    refine ⟨14164223175550178830870781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151085047205868574195954997 14164223175550178830870781)
    ·
      refine ⟨5311583690831317061576543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14164223175550178830870781 5311583690831317061576543)
      ·
        refine ⟨7967375536246975592364815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311583690831317061576543 7967375536246975592364815)
        ·
          refine ⟨11951063304370463388547223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967375536246975592364815 11951063304370463388547223)
          ·
            refine ⟨17926594956555695082820835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951063304370463388547223 17926594956555695082820835)
            ·
              refine ⟨26889892434833542624231253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926594956555695082820835 26889892434833542624231253)
              ·
                refine ⟨157557963485352788813855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26889892434833542624231253 157557963485352788813855)
                ·
                  rfl

theorem cell22_4142381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 9].length) (baseStart_4142381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142381 prefixEnd_4142381 := by exact prefixLift 4142381
  have htrace : WordTrace (prefixWord ++ tailWord_4142381) baseStart_4142381 baseEnd_4142381 := by
    simpa [prefixWord, tailWord_4142381, baseEnd_4142381] using wordTrace_append hprefix tailTrace_4142381
  have hstable : (prefixWord ++ tailWord_4142381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142381).length < 2 ^ (prefixWord ++ tailWord_4142381).sum := by decide
  have hdescent : baseEnd_4142381 < baseStart_4142381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142385 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_4142385 : Nat := 118140960795 + 4142385 * 2 ^ 59
def prefixEnd_4142385 : Nat := 4983230072969 + 3 ^ 40 * 4142385 * 2
def baseEnd_4142385 : Nat := 1418023040649920422224683

theorem tailTrace_4142385 : CollatzResearch.WordTrace tailWord_4142385 prefixEnd_4142385 1418023040649920422224683 := by
  unfold tailWord_4142385
  simp only [CollatzResearch.WordTrace]
  refine ⟨151085193097854082879100609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100723462065236055252733739 151085193097854082879100609)
  ·
    refine ⟨113313894823390562159325457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151085193097854082879100609 113313894823390562159325457)
    ·
      refine ⟨84985421117542921619494093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113313894823390562159325457 84985421117542921619494093)
      ·
        refine ⟨31869532919078595607310285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84985421117542921619494093 31869532919078595607310285)
        ·
          refine ⟨11951074844654473352741357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31869532919078595607310285 11951074844654473352741357)
          ·
            refine ⟨4481653066745427507278009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11951074844654473352741357 4481653066745427507278009)
            ·
              refine ⟨3361239800059070630458507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481653066745427507278009 3361239800059070630458507)
              ·
                refine ⟨5041859700088605945687761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361239800059070630458507 5041859700088605945687761)
                ·
                  refine ⟨3781394775066454459265821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041859700088605945687761 3781394775066454459265821)
                  ·
                    refine ⟨1418023040649920422224683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781394775066454459265821 1418023040649920422224683)
                    ·
                      rfl

theorem cell22_4142385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_4142385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142385 prefixEnd_4142385 := by exact prefixLift 4142385
  have htrace : WordTrace (prefixWord ++ tailWord_4142385) baseStart_4142385 baseEnd_4142385 := by
    simpa [prefixWord, tailWord_4142385, baseEnd_4142385] using wordTrace_append hprefix tailTrace_4142385
  have hstable : (prefixWord ++ tailWord_4142385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142385).length < 2 ^ (prefixWord ++ tailWord_4142385).sum := by decide
  have hdescent : baseEnd_4142385 < baseStart_4142385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142424 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_4142424 : Nat := 118140960795 + 4142424 * 2 ^ 59
def prefixEnd_4142424 : Nat := 4983230072969 + 3 ^ 40 * 4142424 * 2
def baseEnd_4142424 : Nat := 1418036391146937320499563

theorem tailTrace_4142424 : CollatzResearch.WordTrace tailWord_4142424 prefixEnd_4142424 1418036391146937320499563 := by
  unfold tailWord_4142424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75543307772356396269885163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100724410363141861693180217 75543307772356396269885163)
  ·
    refine ⟨113314961658534594404827745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75543307772356396269885163 113314961658534594404827745)
    ·
      refine ⟨84986221243900945803620809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113314961658534594404827745 84986221243900945803620809)
      ·
        refine ⟨63739665932925709352715607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84986221243900945803620809 63739665932925709352715607)
        ·
          refine ⟨95609498899388564029073411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63739665932925709352715607 95609498899388564029073411)
          ·
            refine ⟨143414248349082846043610117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95609498899388564029073411 143414248349082846043610117)
            ·
              refine ⟨26890171565453033633176897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143414248349082846043610117 26890171565453033633176897)
              ·
                refine ⟨20167628674089775224882673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26890171565453033633176897 20167628674089775224882673)
                ·
                  refine ⟨15125721505567331418662005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20167628674089775224882673 15125721505567331418662005)
                  ·
                    refine ⟨1418036391146937320499563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15125721505567331418662005 1418036391146937320499563)
                    ·
                      rfl

theorem cell22_4142424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_4142424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142424 prefixEnd_4142424 := by exact prefixLift 4142424
  have htrace : WordTrace (prefixWord ++ tailWord_4142424) baseStart_4142424 baseEnd_4142424 := by
    simpa [prefixWord, tailWord_4142424, baseEnd_4142424] using wordTrace_append hprefix tailTrace_4142424
  have hstable : (prefixWord ++ tailWord_4142424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142424).length < 2 ^ (prefixWord ++ tailWord_4142424).sum := by decide
  have hdescent : baseEnd_4142424 < baseStart_4142424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142473 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_4142473 : Nat := 118140960795 + 4142473 * 2 ^ 59
def prefixEnd_4142473 : Nat := 4983230072969 + 3 ^ 40 * 4142473 * 2
def baseEnd_4142473 : Nat := 1418053164848317526024413

theorem tailTrace_4142473 : CollatzResearch.WordTrace tailWord_4142473 prefixEnd_4142473 1418053164848317526024413 := by
  unfold tailWord_4142473
  simp only [CollatzResearch.WordTrace]
  refine ⟨151088402721535273908304073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100725601814356849272202715 151088402721535273908304073)
  ·
    refine ⟨113316302041151455431228055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151088402721535273908304073 113316302041151455431228055)
    ·
      refine ⟨169974453061727183146842083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113316302041151455431228055 169974453061727183146842083)
      ·
        refine ⟨254961679592590774720263125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169974453061727183146842083 254961679592590774720263125)
        ·
          refine ⟨5975664365451346282506167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254961679592590774720263125 5975664365451346282506167)
          ·
            refine ⟨8963496548177019423759251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975664365451346282506167 8963496548177019423759251)
            ·
              refine ⟨13445244822265529135638877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8963496548177019423759251 13445244822265529135638877)
              ·
                refine ⟨5041966808349573425864579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13445244822265529135638877 5041966808349573425864579)
                ·
                  refine ⟨7562950212524360138796869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041966808349573425864579 7562950212524360138796869)
                  ·
                    refine ⟨1418053164848317526024413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7562950212524360138796869 1418053164848317526024413)
                    ·
                      rfl

theorem cell22_4142473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_4142473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142473 prefixEnd_4142473 := by exact prefixLift 4142473
  have htrace : WordTrace (prefixWord ++ tailWord_4142473) baseStart_4142473 baseEnd_4142473 := by
    simpa [prefixWord, tailWord_4142473, baseEnd_4142473] using wordTrace_append hprefix tailTrace_4142473
  have hstable : (prefixWord ++ tailWord_4142473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142473).length < 2 ^ (prefixWord ++ tailWord_4142473).sum := by decide
  have hdescent : baseEnd_4142473 < baseStart_4142473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142488 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_4142488 : Nat := 118140960795 + 4142488 * 2 ^ 59
def prefixEnd_4142488 : Nat := 4983230072969 + 3 ^ 40 * 4142488 * 2
def baseEnd_4142488 : Nat := 472686099884954162299789

theorem tailTrace_4142488 : CollatzResearch.WordTrace tailWord_4142488 prefixEnd_4142488 472686099884954162299789 := by
  unfold tailWord_4142488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75544474908240465735050059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100725966544320620980066745 75544474908240465735050059)
  ·
    refine ⟨113316712362360698602575089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75544474908240465735050059 113316712362360698602575089)
    ·
      refine ⟨84987534271770523951931317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113316712362360698602575089 84987534271770523951931317)
      ·
        refine ⟨7967581337978486620493561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84987534271770523951931317 7967581337978486620493561)
        ·
          refine ⟨5975686003483864965370171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7967581337978486620493561 5975686003483864965370171)
          ·
            refine ⟨8963529005225797448055257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975686003483864965370171 8963529005225797448055257)
            ·
              refine ⟨6722646753919348086041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8963529005225797448055257 6722646753919348086041443)
              ·
                refine ⟨10083970130879022129062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722646753919348086041443 10083970130879022129062165)
                ·
                  refine ⟨472686099884954162299789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10083970130879022129062165 472686099884954162299789)
                  ·
                    rfl

theorem cell22_4142488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_4142488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142488 prefixEnd_4142488 := by exact prefixLift 4142488
  have htrace : WordTrace (prefixWord ++ tailWord_4142488) baseStart_4142488 baseEnd_4142488 := by
    simpa [prefixWord, tailWord_4142488, baseEnd_4142488] using wordTrace_append hprefix tailTrace_4142488
  have hstable : (prefixWord ++ tailWord_4142488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142488).length < 2 ^ (prefixWord ++ tailWord_4142488).sum := by decide
  have hdescent : baseEnd_4142488 < baseStart_4142488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142499 : List Nat := [1, 1, 1, 4, 1, 3, 2, 9]
def baseStart_4142499 : Nat := 118140960795 + 4142499 * 2 ^ 59
def prefixEnd_4142499 : Nat := 4983230072969 + 3 ^ 40 * 4142499 * 2
def baseEnd_4142499 : Nat := 157562451686629124986037

theorem tailTrace_4142499 : CollatzResearch.WordTrace tailWord_4142499 prefixEnd_4142499 157562451686629124986037 := by
  unfold tailWord_4142499
  simp only [CollatzResearch.WordTrace]
  refine ⟨151089351019441080348750551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100726234012960720232500367 151089351019441080348750551)
  ·
    refine ⟨226634026529161620523125827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151089351019441080348750551 226634026529161620523125827)
    ·
      refine ⟨339951039793742430784688741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226634026529161620523125827 339951039793742430784688741)
      ·
        refine ⟨63740819961326705772129139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339951039793742430784688741 63740819961326705772129139)
        ·
          refine ⟨95611229941990058658193709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63740819961326705772129139 95611229941990058658193709)
          ·
            refine ⟨35854211228246271996822641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95611229941990058658193709 35854211228246271996822641)
            ·
              refine ⟨26890658421184703997616981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35854211228246271996822641 26890658421184703997616981)
              ·
                refine ⟨157562451686629124986037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26890658421184703997616981 157562451686629124986037)
                ·
                  rfl

theorem cell22_4142499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 9].length) (baseStart_4142499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142499 prefixEnd_4142499 := by exact prefixLift 4142499
  have htrace : WordTrace (prefixWord ++ tailWord_4142499) baseStart_4142499 baseEnd_4142499 := by
    simpa [prefixWord, tailWord_4142499, baseEnd_4142499] using wordTrace_append hprefix tailTrace_4142499
  have hstable : (prefixWord ++ tailWord_4142499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142499).length < 2 ^ (prefixWord ++ tailWord_4142499).sum := by decide
  have hdescent : baseEnd_4142499 < baseStart_4142499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142531 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 5, 3]
def baseStart_4142531 : Nat := 118140960795 + 4142531 * 2 ^ 59
def prefixEnd_4142531 : Nat := 4983230072969 + 3 ^ 40 * 4142531 * 2
def baseEnd_4142531 : Nat := 1418073019433624708074235

theorem tailTrace_4142531 : CollatzResearch.WordTrace tailWord_4142531 prefixEnd_4142531 1418073019433624708074235 := by
  unfold tailWord_4142531
  simp only [CollatzResearch.WordTrace]
  refine ⟨151090518155325149813915447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100727012103550099875943631 151090518155325149813915447)
  ·
    refine ⟨226635777232987724720873171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151090518155325149813915447 226635777232987724720873171)
    ·
      refine ⟨339953665849481587081309757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226635777232987724720873171 339953665849481587081309757)
      ·
        refine ⟨127482624693555595155491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339953665849481587081309757 127482624693555595155491159)
        ·
          refine ⟨191223937040333392733236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127482624693555595155491159 191223937040333392733236739)
          ·
            refine ⟨286835905560500089099855109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191223937040333392733236739 286835905560500089099855109)
            ·
              refine ⟨53781732292593766706222833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286835905560500089099855109 53781732292593766706222833)
              ·
                refine ⟨40336299219445325029667125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53781732292593766706222833 40336299219445325029667125)
                ·
                  refine ⟨3781528051822999221531293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40336299219445325029667125 3781528051822999221531293)
                  ·
                    refine ⟨1418073019433624708074235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781528051822999221531293 1418073019433624708074235)
                    ·
                      rfl

theorem cell22_4142531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 3].length) (baseStart_4142531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142531 prefixEnd_4142531 := by exact prefixLift 4142531
  have htrace : WordTrace (prefixWord ++ tailWord_4142531) baseStart_4142531 baseEnd_4142531 := by
    simpa [prefixWord, tailWord_4142531, baseEnd_4142531] using wordTrace_append hprefix tailTrace_4142531
  have hstable : (prefixWord ++ tailWord_4142531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142531).length < 2 ^ (prefixWord ++ tailWord_4142531).sum := by decide
  have hdescent : baseEnd_4142531 < baseStart_4142531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142599 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 1, 3]
def baseStart_4142599 : Nat := 118140960795 + 4142599 * 2 ^ 59
def prefixEnd_4142599 : Nat := 4983230072969 + 3 ^ 40 * 4142599 * 2
def baseEnd_4142599 : Nat := 1418096297223295197374027

theorem tailTrace_4142599 : CollatzResearch.WordTrace tailWord_4142599 prefixEnd_4142599 1418096297223295197374027 := by
  unfold tailWord_4142599
  simp only [CollatzResearch.WordTrace]
  refine ⟨151092998319078797427390851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100728665546052531618260567 151092998319078797427390851)
  ·
    refine ⟨226639497478618196141086277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151092998319078797427390851 226639497478618196141086277)
    ·
      refine ⟨42494905777240911776453677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226639497478618196141086277 42494905777240911776453677)
      ·
        refine ⟨15935589666465341916170129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42494905777240911776453677 15935589666465341916170129)
        ·
          refine ⟨11951692249849006437127597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15935589666465341916170129 11951692249849006437127597)
          ·
            refine ⟨4481884593693377413922849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11951692249849006437127597 4481884593693377413922849)
            ·
              refine ⟨3361413445270033060442137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481884593693377413922849 3361413445270033060442137)
              ·
                refine ⟨2521060083952524795331603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361413445270033060442137 2521060083952524795331603)
                ·
                  refine ⟨3781590125928787192997405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521060083952524795331603 3781590125928787192997405)
                  ·
                    refine ⟨1418096297223295197374027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781590125928787192997405 1418096297223295197374027)
                    ·
                      rfl

theorem cell22_4142599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_4142599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142599 prefixEnd_4142599 := by exact prefixLift 4142599
  have htrace : WordTrace (prefixWord ++ tailWord_4142599) baseStart_4142599 baseEnd_4142599 := by
    simpa [prefixWord, tailWord_4142599, baseEnd_4142599] using wordTrace_append hprefix tailTrace_4142599
  have hstable : (prefixWord ++ tailWord_4142599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142599).length < 2 ^ (prefixWord ++ tailWord_4142599).sum := by decide
  have hdescent : baseEnd_4142599 < baseStart_4142599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142655 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 2, 3]
def baseStart_4142655 : Nat := 118140960795 + 4142655 * 2 ^ 59
def prefixEnd_4142655 : Nat := 4983230072969 + 3 ^ 40 * 4142655 * 2
def baseEnd_4142655 : Nat := 1418115467167729717973855

theorem tailTrace_4142655 : CollatzResearch.WordTrace tailWord_4142655 prefixEnd_4142655 1418115467167729717973855 := by
  unfold tailWord_4142655
  simp only [CollatzResearch.WordTrace]
  refine ⟨151095040806875918991429419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100730027204583945994286279 151095040806875918991429419)
  ·
    refine ⟨226642561210313878487144129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151095040806875918991429419 226642561210313878487144129)
    ·
      refine ⟨169981920907735408865358097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226642561210313878487144129 169981920907735408865358097)
      ·
        refine ⟨127486440680801556649018573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169981920907735408865358097 127486440680801556649018573)
        ·
          refine ⟨47807415255300583743381965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127486440680801556649018573 47807415255300583743381965)
          ·
            refine ⟨17927780720737718903768237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47807415255300583743381965 17927780720737718903768237)
            ·
              refine ⟨6722917770276644588913089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17927780720737718903768237 6722917770276644588913089)
              ·
                refine ⟨5042188327707483441684817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722917770276644588913089 5042188327707483441684817)
                ·
                  refine ⟨3781641245780612581263613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042188327707483441684817 3781641245780612581263613)
                  ·
                    refine ⟨1418115467167729717973855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781641245780612581263613 1418115467167729717973855)
                    ·
                      rfl

theorem cell22_4142655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_4142655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142655 prefixEnd_4142655 := by exact prefixLift 4142655
  have htrace : WordTrace (prefixWord ++ tailWord_4142655) baseStart_4142655 baseEnd_4142655 := by
    simpa [prefixWord, tailWord_4142655, baseEnd_4142655] using wordTrace_append hprefix tailTrace_4142655
  have hstable : (prefixWord ++ tailWord_4142655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142655).length < 2 ^ (prefixWord ++ tailWord_4142655).sum := by decide
  have hdescent : baseEnd_4142655 < baseStart_4142655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142681 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_4142681 : Nat := 118140960795 + 4142681 * 2 ^ 59
def prefixEnd_4142681 : Nat := 4983230072969 + 3 ^ 40 * 4142681 * 2
def baseEnd_4142681 : Nat := 1418124367499074316823775

theorem tailTrace_4142681 : CollatzResearch.WordTrace tailWord_4142681 prefixEnd_4142681 1418124367499074316823775 := by
  unfold tailWord_4142681
  simp only [CollatzResearch.WordTrace]
  refine ⟨151095989104781725431875897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100730659403187816954583931 151095989104781725431875897)
  ·
    refine ⟨113321991828586294073906923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151095989104781725431875897 113321991828586294073906923)
    ·
      refine ⟨169982987742879441110860385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113321991828586294073906923 169982987742879441110860385)
      ·
        refine ⟨127487240807159580833145289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169982987742879441110860385 127487240807159580833145289)
        ·
          refine ⟨95615430605369685624858967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127487240807159580833145289 95615430605369685624858967)
          ·
            refine ⟨143423145908054528437288451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95615430605369685624858967 143423145908054528437288451)
            ·
              refine ⟨215134718862081792655932677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143423145908054528437288451 215134718862081792655932677)
              ·
                refine ⟨40337759786640336122987377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215134718862081792655932677 40337759786640336122987377)
                ·
                  refine ⟨30253319839980252092240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40337759786640336122987377 30253319839980252092240533)
                  ·
                    refine ⟨1418124367499074316823775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30253319839980252092240533 1418124367499074316823775)
                    ·
                      rfl

theorem cell22_4142681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_4142681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142681 prefixEnd_4142681 := by exact prefixLift 4142681
  have htrace : WordTrace (prefixWord ++ tailWord_4142681) baseStart_4142681 baseEnd_4142681 := by
    simpa [prefixWord, tailWord_4142681, baseEnd_4142681] using wordTrace_append hprefix tailTrace_4142681
  have hstable : (prefixWord ++ tailWord_4142681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142681).length < 2 ^ (prefixWord ++ tailWord_4142681).sum := by decide
  have hdescent : baseEnd_4142681 < baseStart_4142681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142713 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 5]
def baseStart_4142713 : Nat := 118140960795 + 4142713 * 2 ^ 59
def prefixEnd_4142713 : Nat := 4983230072969 + 3 ^ 40 * 4142713 * 2
def baseEnd_4142713 : Nat := 472711773917678966674559

theorem tailTrace_4142713 : CollatzResearch.WordTrace tailWord_4142713 prefixEnd_4142713 472711773917678966674559 := by
  unfold tailWord_4142713
  simp only [CollatzResearch.WordTrace]
  refine ⟨151097156240665794897040793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100731437493777196598027195 151097156240665794897040793)
  ·
    refine ⟨113322867180499346172780595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151097156240665794897040793 113322867180499346172780595)
    ·
      refine ⟨169984300770749019259170893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113322867180499346172780595 169984300770749019259170893)
      ·
        refine ⟨63744112789030882222189085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169984300770749019259170893 63744112789030882222189085)
        ·
          refine ⟨23904042295886580833320907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63744112789030882222189085 23904042295886580833320907)
          ·
            refine ⟨35856063443829871249981361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23904042295886580833320907 35856063443829871249981361)
            ·
              refine ⟨26892047582872403437486021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35856063443829871249981361 26892047582872403437486021)
              ·
                refine ⟨5042258921788575644528629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26892047582872403437486021 5042258921788575644528629)
                ·
                  refine ⟨472711773917678966674559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042258921788575644528629 472711773917678966674559)
                  ·
                    rfl

theorem cell22_4142713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_4142713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142713 prefixEnd_4142713 := by exact prefixLift 4142713
  have htrace : WordTrace (prefixWord ++ tailWord_4142713) baseStart_4142713 baseEnd_4142713 := by
    simpa [prefixWord, tailWord_4142713, baseEnd_4142713] using wordTrace_append hprefix tailTrace_4142713
  have hstable : (prefixWord ++ tailWord_4142713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142713).length < 2 ^ (prefixWord ++ tailWord_4142713).sum := by decide
  have hdescent : baseEnd_4142713 < baseStart_4142713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142717 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_4142717 : Nat := 118140960795 + 4142717 * 2 ^ 59
def prefixEnd_4142717 : Nat := 4983230072969 + 3 ^ 40 * 4142717 * 2
def baseEnd_4142717 : Nat := 1418136691034782222923665

theorem tailTrace_4142717 : CollatzResearch.WordTrace tailWord_4142717 prefixEnd_4142717 1418136691034782222923665 := by
  unfold tailWord_4142717
  simp only [CollatzResearch.WordTrace]
  refine ⟨151097302132651303580186405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100731534755100869053457603 151097302132651303580186405)
  ·
    refine ⟨28330744149872119421284951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151097302132651303580186405 28330744149872119421284951)
    ·
      refine ⟨42496116224808179131927427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330744149872119421284951 42496116224808179131927427)
      ·
        refine ⟨63744174337212268697891141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42496116224808179131927427 63744174337212268697891141)
        ·
          refine ⟨11952032688227300380854589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63744174337212268697891141 11952032688227300380854589)
          ·
            refine ⟨4482012258085237642820471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11952032688227300380854589 4482012258085237642820471)
            ·
              refine ⟨6723018387127856464230707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482012258085237642820471 6723018387127856464230707)
              ·
                refine ⟨10084527580691784696346061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723018387127856464230707 10084527580691784696346061)
                ·
                  refine ⟨3781697842759419261129773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10084527580691784696346061 3781697842759419261129773)
                  ·
                    refine ⟨1418136691034782222923665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781697842759419261129773 1418136691034782222923665)
                    ·
                      rfl

theorem cell22_4142717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_4142717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142717 prefixEnd_4142717 := by exact prefixLift 4142717
  have htrace : WordTrace (prefixWord ++ tailWord_4142717) baseStart_4142717 baseEnd_4142717 := by
    simpa [prefixWord, tailWord_4142717, baseEnd_4142717] using wordTrace_append hprefix tailTrace_4142717
  have hstable : (prefixWord ++ tailWord_4142717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142717).length < 2 ^ (prefixWord ++ tailWord_4142717).sum := by decide
  have hdescent : baseEnd_4142717 < baseStart_4142717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142730 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_4142730 : Nat := 118140960795 + 4142730 * 2 ^ 59
def prefixEnd_4142730 : Nat := 4983230072969 + 3 ^ 40 * 4142730 * 2
def baseEnd_4142730 : Nat := 472713713733484840782875

theorem tailTrace_4142730 : CollatzResearch.WordTrace tailWord_4142730 prefixEnd_4142730 472713713733484840782875 := by
  unfold tailWord_4142730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774444070401051700102411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100731850854402804533606429 37774444070401051700102411)
  ·
    refine ⟨56661666105601577550153617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37774444070401051700102411 56661666105601577550153617)
    ·
      refine ⟨42496249579201183162615213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56661666105601577550153617 42496249579201183162615213)
      ·
        refine ⟨15936093592200443685980705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42496249579201183162615213 15936093592200443685980705)
        ·
          refine ⟨11952070194150332764485529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15936093592200443685980705 11952070194150332764485529)
          ·
            refine ⟨8964052645612749573364147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952070194150332764485529 8964052645612749573364147)
            ·
              refine ⟨13446078968419124360046221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964052645612749573364147 13446078968419124360046221)
              ·
                refine ⟨5042279613157171635017333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13446078968419124360046221 5042279613157171635017333)
                ·
                  refine ⟨472713713733484840782875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042279613157171635017333 472713713733484840782875)
                  ·
                    rfl

theorem cell22_4142730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_4142730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142730 prefixEnd_4142730 := by exact prefixLift 4142730
  have htrace : WordTrace (prefixWord ++ tailWord_4142730) baseStart_4142730 baseEnd_4142730 := by
    simpa [prefixWord, tailWord_4142730, baseEnd_4142730] using wordTrace_append hprefix tailTrace_4142730
  have hstable : (prefixWord ++ tailWord_4142730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142730).length < 2 ^ (prefixWord ++ tailWord_4142730).sum := by decide
  have hdescent : baseEnd_4142730 < baseStart_4142730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142824 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4142824 : Nat := 118140960795 + 4142824 * 2 ^ 59
def prefixEnd_4142824 : Nat := 4983230072969 + 3 ^ 40 * 4142824 * 2
def baseEnd_4142824 : Nat := 1418173319321469610498337

theorem tailTrace_4142824 : CollatzResearch.WordTrace tailWord_4142824 prefixEnd_4142824 1418173319321469610498337 := by
  unfold tailWord_4142824
  simp only [CollatzResearch.WordTrace]
  refine ⟨75550602371631830427165763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100734136495509107236221017 75550602371631830427165763)
  ·
    refine ⟨113325903557447745640748645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75550602371631830427165763 113325903557447745640748645)
    ·
      refine ⟨21248606917021452307640371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113325903557447745640748645 21248606917021452307640371)
      ·
        refine ⟨31872910375532178461460557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21248606917021452307640371 31872910375532178461460557)
        ·
          refine ⟨11952341390824566923047709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31872910375532178461460557 11952341390824566923047709)
          ·
            refine ⟨4482128021559212596142891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11952341390824566923047709 4482128021559212596142891)
            ·
              refine ⟨6723192032338818894214337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482128021559212596142891 6723192032338818894214337)
              ·
                refine ⟨5042394024254114170660753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723192032338818894214337 5042394024254114170660753)
                ·
                  refine ⟨3781795518190585627995565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042394024254114170660753 3781795518190585627995565)
                  ·
                    refine ⟨1418173319321469610498337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781795518190585627995565 1418173319321469610498337)
                    ·
                      rfl

theorem cell22_4142824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4142824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142824 prefixEnd_4142824 := by exact prefixLift 4142824
  have htrace : WordTrace (prefixWord ++ tailWord_4142824) baseStart_4142824 baseEnd_4142824 := by
    simpa [prefixWord, tailWord_4142824, baseEnd_4142824] using wordTrace_append hprefix tailTrace_4142824
  have hstable : (prefixWord ++ tailWord_4142824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142824).length < 2 ^ (prefixWord ++ tailWord_4142824).sum := by decide
  have hdescent : baseEnd_4142824 < baseStart_4142824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142835 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 3]
def baseStart_4142835 : Nat := 118140960795 + 4142835 * 2 ^ 59
def prefixEnd_4142835 : Nat := 4983230072969 + 3 ^ 40 * 4142835 * 2
def baseEnd_4142835 : Nat := 1418177084846269248473303

theorem tailTrace_4142835 : CollatzResearch.WordTrace tailWord_4142835 prefixEnd_4142835 1418177084846269248473303 := by
  unfold tailWord_4142835
  simp only [CollatzResearch.WordTrace]
  refine ⟨151101605946223809732981959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100734403964149206488654639 151101605946223809732981959)
  ·
    refine ⟨226652408919335714599472939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151101605946223809732981959 226652408919335714599472939)
    ·
      refine ⟨339978613379003571899209409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226652408919335714599472939 339978613379003571899209409)
      ·
        refine ⟨254983960034252678924407057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339978613379003571899209409 254983960034252678924407057)
        ·
          refine ⟨191237970025689509193305293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254983960034252678924407057 191237970025689509193305293)
          ·
            refine ⟨71714238759633565947489485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191237970025689509193305293 71714238759633565947489485)
            ·
              refine ⟨26892839534862587230308557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71714238759633565947489485 26892839534862587230308557)
              ·
                refine ⟨10084814825573470211365709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26892839534862587230308557 10084814825573470211365709)
                ·
                  refine ⟨3781805559590051329262141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10084814825573470211365709 3781805559590051329262141)
                  ·
                    refine ⟨1418177084846269248473303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781805559590051329262141 1418177084846269248473303)
                    ·
                      rfl

theorem cell22_4142835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3].length) (baseStart_4142835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142835 prefixEnd_4142835 := by exact prefixLift 4142835
  have htrace : WordTrace (prefixWord ++ tailWord_4142835) baseStart_4142835 baseEnd_4142835 := by
    simpa [prefixWord, tailWord_4142835, baseEnd_4142835] using wordTrace_append hprefix tailTrace_4142835
  have hstable : (prefixWord ++ tailWord_4142835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142835).length < 2 ^ (prefixWord ++ tailWord_4142835).sum := by decide
  have hdescent : baseEnd_4142835 < baseStart_4142835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142852 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4142852 : Nat := 118140960795 + 4142852 * 2 ^ 59
def prefixEnd_4142852 : Nat := 4983230072969 + 3 ^ 40 * 4142852 * 2
def baseEnd_4142852 : Nat := 1418182904293686870798251

theorem tailTrace_4142852 : CollatzResearch.WordTrace tailWord_4142852 prefixEnd_4142852 1418182904293686870798251 := by
  unfold tailWord_4142852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75551112993581110818175405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100734817324774814424233873 75551112993581110818175405)
  ·
    refine ⟨28331667372592916556815777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75551112993581110818175405 28331667372592916556815777)
    ·
      refine ⟨21248750529444687417611833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28331667372592916556815777 21248750529444687417611833)
      ·
        refine ⟨15936562897083515563208875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21248750529444687417611833 15936562897083515563208875)
        ·
          refine ⟨23904844345625273344813313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936562897083515563208875 23904844345625273344813313)
          ·
            refine ⟨17928633259218955008609985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23904844345625273344813313 17928633259218955008609985)
            ·
              refine ⟨13446474944414216256457489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17928633259218955008609985 13446474944414216256457489)
              ·
                refine ⟨10084856208310662192343117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13446474944414216256457489 10084856208310662192343117)
                ·
                  refine ⟨3781821078116498322128669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10084856208310662192343117 3781821078116498322128669)
                  ·
                    refine ⟨1418182904293686870798251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781821078116498322128669 1418182904293686870798251)
                    ·
                      rfl

theorem cell22_4142852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4142852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142852 prefixEnd_4142852 := by exact prefixLift 4142852
  have htrace : WordTrace (prefixWord ++ tailWord_4142852) baseStart_4142852 baseEnd_4142852 := by
    simpa [prefixWord, tailWord_4142852, baseEnd_4142852] using wordTrace_append hprefix tailTrace_4142852
  have hstable : (prefixWord ++ tailWord_4142852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142852).length < 2 ^ (prefixWord ++ tailWord_4142852).sum := by decide
  have hdescent : baseEnd_4142852 < baseStart_4142852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142863 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_4142863 : Nat := 118140960795 + 4142863 * 2 ^ 59
def prefixEnd_4142863 : Nat := 4983230072969 + 3 ^ 40 * 4142863 * 2
def baseEnd_4142863 : Nat := 1418186669818486508773217

theorem tailTrace_4142863 : CollatzResearch.WordTrace tailWord_4142863 prefixEnd_4142863 1418186669818486508773217 := by
  unfold tailWord_4142863
  simp only [CollatzResearch.WordTrace]
  refine ⟨151102627190122370515001243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100735084793414913676667495 151102627190122370515001243)
  ·
    refine ⟨226653940785183555772501865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151102627190122370515001243 226653940785183555772501865)
    ·
      refine ⟨169990455588887666829376399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226653940785183555772501865 169990455588887666829376399)
      ·
        refine ⟨254985683383331500244064599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169990455588887666829376399 254985683383331500244064599)
        ·
          refine ⟨382478525074997250366096899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254985683383331500244064599 382478525074997250366096899)
          ·
            refine ⟨573717787612495875549145349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382478525074997250366096899 573717787612495875549145349)
            ·
              refine ⟨107572085177342976665464753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573717787612495875549145349 107572085177342976665464753)
              ·
                refine ⟨80679063883007232499098565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107572085177342976665464753 80679063883007232499098565)
                ·
                  refine ⟨15127324478063856093580981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80679063883007232499098565 15127324478063856093580981)
                  ·
                    refine ⟨1418186669818486508773217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15127324478063856093580981 1418186669818486508773217)
                    ·
                      rfl

theorem cell22_4142863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_4142863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142863 prefixEnd_4142863 := by exact prefixLift 4142863
  have htrace : WordTrace (prefixWord ++ tailWord_4142863) baseStart_4142863 baseEnd_4142863 := by
    simpa [prefixWord, tailWord_4142863, baseEnd_4142863] using wordTrace_append hprefix tailTrace_4142863
  have hstable : (prefixWord ++ tailWord_4142863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142863).length < 2 ^ (prefixWord ++ tailWord_4142863).sum := by decide
  have hdescent : baseEnd_4142863 < baseStart_4142863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142869 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_4142869 : Nat := 118140960795 + 4142869 * 2 ^ 59
def prefixEnd_4142869 : Nat := 4983230072969 + 3 ^ 40 * 4142869 * 2
def baseEnd_4142869 : Nat := 1418188723741104493123199

theorem tailTrace_4142869 : CollatzResearch.WordTrace tailWord_4142869 prefixEnd_4142869 1418188723741104493123199 := by
  unfold tailWord_4142869
  simp only [CollatzResearch.WordTrace]
  refine ⟨151102846028100633539719661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100735230685400422359813107 151102846028100633539719661)
  ·
    refine ⟨56663567260537737577394873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151102846028100633539719661 56663567260537737577394873)
    ·
      refine ⟨42497675445403303183046155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56663567260537737577394873 42497675445403303183046155)
      ·
        refine ⟨63746513168104954774569233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42497675445403303183046155 63746513168104954774569233)
        ·
          refine ⟨47809884876078716080926925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63746513168104954774569233 47809884876078716080926925)
          ·
            refine ⟨17928706828529518530347597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47809884876078716080926925 17928706828529518530347597)
            ·
              refine ⟨6723265060698569448880349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17928706828529518530347597 6723265060698569448880349)
              ·
                refine ⟨2521224397761963543330131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723265060698569448880349 2521224397761963543330131)
                ·
                  refine ⟨3781836596642945314995197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521224397761963543330131 3781836596642945314995197)
                  ·
                    refine ⟨1418188723741104493123199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781836596642945314995197 1418188723741104493123199)
                    ·
                      rfl

theorem cell22_4142869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_4142869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142869 prefixEnd_4142869 := by exact prefixLift 4142869
  have htrace : WordTrace (prefixWord ++ tailWord_4142869) baseStart_4142869 baseEnd_4142869 := by
    simpa [prefixWord, tailWord_4142869, baseEnd_4142869] using wordTrace_append hprefix tailTrace_4142869
  have hstable : (prefixWord ++ tailWord_4142869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142869).length < 2 ^ (prefixWord ++ tailWord_4142869).sum := by decide
  have hdescent : baseEnd_4142869 < baseStart_4142869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142899 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 5]
def baseStart_4142899 : Nat := 118140960795 + 4142899 * 2 ^ 59
def prefixEnd_4142899 : Nat := 4983230072969 + 3 ^ 40 * 4142899 * 2
def baseEnd_4142899 : Nat := 472732997784731471624369

theorem tailTrace_4142899 : CollatzResearch.WordTrace tailWord_4142899 prefixEnd_4142899 472732997784731471624369 := by
  unfold tailWord_4142899
  simp only [CollatzResearch.WordTrace]
  refine ⟨151103940217991948663311751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100735960145327965775541167 151103940217991948663311751)
  ·
    refine ⟨226655910326987922994967627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151103940217991948663311751 226655910326987922994967627)
    ·
      refine ⟨339983865490481884492451441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226655910326987922994967627 339983865490481884492451441)
      ·
        refine ⟨254987899117861413369338581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339983865490481884492451441 254987899117861413369338581)
        ·
          refine ⟨5976278885574876875843873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254987899117861413369338581 5976278885574876875843873)
          ·
            refine ⟨4482209164181157656882905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976278885574876875843873 4482209164181157656882905)
            ·
              refine ⟨3361656873135868242662179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482209164181157656882905 3361656873135868242662179)
              ·
                refine ⟨5042485309703802363993269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361656873135868242662179 5042485309703802363993269)
                ·
                  refine ⟨472732997784731471624369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042485309703802363993269 472732997784731471624369)
                  ·
                    rfl

theorem cell22_4142899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 5].length) (baseStart_4142899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142899 prefixEnd_4142899 := by exact prefixLift 4142899
  have htrace : WordTrace (prefixWord ++ tailWord_4142899) baseStart_4142899 baseEnd_4142899 := by
    simpa [prefixWord, tailWord_4142899, baseEnd_4142899] using wordTrace_append hprefix tailTrace_4142899
  have hstable : (prefixWord ++ tailWord_4142899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142899).length < 2 ^ (prefixWord ++ tailWord_4142899).sum := by decide
  have hdescent : baseEnd_4142899 < baseStart_4142899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142929 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_4142929 : Nat := 118140960795 + 4142929 * 2 ^ 59
def prefixEnd_4142929 : Nat := 4983230072969 + 3 ^ 40 * 4142929 * 2
def baseEnd_4142929 : Nat := 1418209262967284336623015

theorem tailTrace_4142929 : CollatzResearch.WordTrace tailWord_4142929 prefixEnd_4142929 1418209262967284336623015 := by
  unfold tailWord_4142929
  simp only [CollatzResearch.WordTrace]
  refine ⟨151105034407883263786903841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100736689605255509191269227 151105034407883263786903841)
  ·
    refine ⟨113328775805912447840177881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151105034407883263786903841 113328775805912447840177881)
    ·
      refine ⟨84996581854434335880133411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113328775805912447840177881 84996581854434335880133411)
      ·
        refine ⟨127494872781651503820200117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84996581854434335880133411 127494872781651503820200117)
        ·
          refine ⟨11952644323279828483143761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127494872781651503820200117 11952644323279828483143761)
          ·
            refine ⟨8964483242459871362357821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952644323279828483143761 8964483242459871362357821)
            ·
              refine ⟨3361681215922451760884183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8964483242459871362357821 3361681215922451760884183)
              ·
                refine ⟨5042521823883677641326275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361681215922451760884183 5042521823883677641326275)
                ·
                  refine ⟨7563782735825516461989413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042521823883677641326275 7563782735825516461989413)
                  ·
                    refine ⟨1418209262967284336623015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7563782735825516461989413 1418209262967284336623015)
                    ·
                      rfl

theorem cell22_4142929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_4142929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142929 prefixEnd_4142929 := by exact prefixLift 4142929
  have htrace : WordTrace (prefixWord ++ tailWord_4142929) baseStart_4142929 baseEnd_4142929 := by
    simpa [prefixWord, tailWord_4142929, baseEnd_4142929] using wordTrace_append hprefix tailTrace_4142929
  have hstable : (prefixWord ++ tailWord_4142929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142929).length < 2 ^ (prefixWord ++ tailWord_4142929).sum := by decide
  have hdescent : baseEnd_4142929 < baseStart_4142929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142944 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_4142944 : Nat := 118140960795 + 4142944 * 2 ^ 59
def prefixEnd_4142944 : Nat := 4983230072969 + 3 ^ 40 * 4142944 * 2
def baseEnd_4142944 : Nat := 472738132591276432499323

theorem tailTrace_4142944 : CollatzResearch.WordTrace tailWord_4142944 prefixEnd_4142944 472738132591276432499323 := by
  unfold tailWord_4142944
  simp only [CollatzResearch.WordTrace]
  refine ⟨75552790751414460674349943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100737054335219280899133257 75552790751414460674349943)
  ·
    refine ⟨113329186127121691011524915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75552790751414460674349943 113329186127121691011524915)
    ·
      refine ⟨169993779190682536517287373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113329186127121691011524915 169993779190682536517287373)
      ·
        refine ⟨63747667196505951193982765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169993779190682536517287373 63747667196505951193982765)
        ·
          refine ⟨23905375198689731697743537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63747667196505951193982765 23905375198689731697743537)
          ·
            refine ⟨17929031399017298773307653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23905375198689731697743537 17929031399017298773307653)
            ·
              refine ⟨3361693387315743519995185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17929031399017298773307653 3361693387315743519995185)
              ·
                refine ⟨2521270040486807639996389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3361693387315743519995185 2521270040486807639996389)
                ·
                  refine ⟨472738132591276432499323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521270040486807639996389 472738132591276432499323)
                  ·
                    rfl

theorem cell22_4142944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_4142944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142944 prefixEnd_4142944 := by exact prefixLift 4142944
  have htrace : WordTrace (prefixWord ++ tailWord_4142944) baseStart_4142944 baseEnd_4142944 := by
    simpa [prefixWord, tailWord_4142944, baseEnd_4142944] using wordTrace_append hprefix tailTrace_4142944
  have hstable : (prefixWord ++ tailWord_4142944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142944).length < 2 ^ (prefixWord ++ tailWord_4142944).sum := by decide
  have hdescent : baseEnd_4142944 < baseStart_4142944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4142974 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4142974 : Nat := 118140960795 + 4142974 * 2 ^ 59
def prefixEnd_4142974 : Nat := 4983230072969 + 3 ^ 40 * 4142974 * 2
def baseEnd_4142974 : Nat := 1418224667386919219247877

theorem tailTrace_4142974 : CollatzResearch.WordTrace tailWord_4142974 prefixEnd_4142974 1418224667386919219247877 := by
  unfold tailWord_4142974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888334461590029559036497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100737783795146824314861317 18888334461590029559036497)
  ·
    refine ⟨14166250846192522169277373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18888334461590029559036497 14166250846192522169277373)
    ·
      refine ⟨5312344067322195813479015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14166250846192522169277373 5312344067322195813479015)
      ·
        refine ⟨7968516100983293720218523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312344067322195813479015 7968516100983293720218523)
        ·
          refine ⟨11952774151474940580327785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968516100983293720218523 11952774151474940580327785)
          ·
            refine ⟨8964580613606205435245839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952774151474940580327785 8964580613606205435245839)
            ·
              refine ⟨13446870920409308152868759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964580613606205435245839 13446870920409308152868759)
              ·
                refine ⟨20170306380613962229303139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446870920409308152868759 20170306380613962229303139)
                ·
                  refine ⟨30255459570920943343954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20170306380613962229303139 30255459570920943343954709)
                  ·
                    refine ⟨1418224667386919219247877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30255459570920943343954709 1418224667386919219247877)
                    ·
                      rfl

theorem cell22_4142974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4142974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4142974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4142974 prefixEnd_4142974 := by exact prefixLift 4142974
  have htrace : WordTrace (prefixWord ++ tailWord_4142974) baseStart_4142974 baseEnd_4142974 := by
    simpa [prefixWord, tailWord_4142974, baseEnd_4142974] using wordTrace_append hprefix tailTrace_4142974
  have hstable : (prefixWord ++ tailWord_4142974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4142974).length < 2 ^ (prefixWord ++ tailWord_4142974).sum := by decide
  have hdescent : baseEnd_4142974 < baseStart_4142974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4142974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143004 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_4143004 : Nat := 118140960795 + 4143004 * 2 ^ 59
def prefixEnd_4143004 : Nat := 4983230072969 + 3 ^ 40 * 4143004 * 2
def baseEnd_4143004 : Nat := 1418234937000009140997785

theorem tailTrace_4143004 : CollatzResearch.WordTrace tailWord_4143004 prefixEnd_4143004 1418234937000009140997785 := by
  unfold tailWord_4143004
  simp only [CollatzResearch.WordTrace]
  refine ⟨75553884941305775797942033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100738513255074367730589377 75553884941305775797942033)
  ·
    refine ⟨56665413705979331848456525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75553884941305775797942033 56665413705979331848456525)
    ·
      refine ⟨21249530139742249443171197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56665413705979331848456525 21249530139742249443171197)
      ·
        refine ⟨7968573802403343541189199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21249530139742249443171197 7968573802403343541189199)
        ·
          refine ⟨11952860703605015311783799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968573802403343541189199 11952860703605015311783799)
          ·
            refine ⟨17929291055407522967675699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952860703605015311783799 17929291055407522967675699)
            ·
              refine ⟨26893936583111284451513549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17929291055407522967675699 26893936583111284451513549)
              ·
                refine ⟨10085226218666731669317581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26893936583111284451513549 10085226218666731669317581)
                ·
                  refine ⟨3781959832000024375994093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10085226218666731669317581 3781959832000024375994093)
                  ·
                    refine ⟨1418234937000009140997785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781959832000024375994093 1418234937000009140997785)
                    ·
                      rfl

theorem cell22_4143004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_4143004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143004 prefixEnd_4143004 := by exact prefixLift 4143004
  have htrace : WordTrace (prefixWord ++ tailWord_4143004) baseStart_4143004 baseEnd_4143004 := by
    simpa [prefixWord, tailWord_4143004, baseEnd_4143004] using wordTrace_append hprefix tailTrace_4143004
  have hstable : (prefixWord ++ tailWord_4143004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143004).length < 2 ^ (prefixWord ++ tailWord_4143004).sum := by decide
  have hdescent : baseEnd_4143004 < baseStart_4143004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143038 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4143038 : Nat := 118140960795 + 4143038 * 2 ^ 59
def prefixEnd_4143038 : Nat := 4983230072969 + 3 ^ 40 * 4143038 * 2
def baseEnd_4143038 : Nat := 1418246575894844385647681

theorem tailTrace_4143038 : CollatzResearch.WordTrace tailWord_4143038 prefixEnd_4143038 1418246575894844385647681 := by
  unfold tailWord_4143038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888626245561046925327721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100739339976325583601747845 18888626245561046925327721)
  ·
    refine ⟨14166469684170785193995791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18888626245561046925327721 14166469684170785193995791)
    ·
      refine ⟨21249704526256177790993687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166469684170785193995791 21249704526256177790993687)
      ·
        refine ⟨31874556789384266686490531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21249704526256177790993687 31874556789384266686490531)
        ·
          refine ⟨47811835184076400029735797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31874556789384266686490531 47811835184076400029735797)
          ·
            refine ⟨4482359548507162502787731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47811835184076400029735797 4482359548507162502787731)
            ·
              refine ⟨6723539322760743754181597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482359548507162502787731 6723539322760743754181597)
              ·
                refine ⟨2521327246035278907818099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723539322760743754181597 2521327246035278907818099)
                ·
                  refine ⟨3781990869052918361727149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521327246035278907818099 3781990869052918361727149)
                  ·
                    refine ⟨1418246575894844385647681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781990869052918361727149 1418246575894844385647681)
                    ·
                      rfl

theorem cell22_4143038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4143038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143038 prefixEnd_4143038 := by exact prefixLift 4143038
  have htrace : WordTrace (prefixWord ++ tailWord_4143038) baseStart_4143038 baseEnd_4143038 := by
    simpa [prefixWord, tailWord_4143038, baseEnd_4143038] using wordTrace_append hprefix tailTrace_4143038
  have hstable : (prefixWord ++ tailWord_4143038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143038).length < 2 ^ (prefixWord ++ tailWord_4143038).sum := by decide
  have hdescent : baseEnd_4143038 < baseStart_4143038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143068 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_4143068 : Nat := 118140960795 + 4143068 * 2 ^ 59
def prefixEnd_4143068 : Nat := 4983230072969 + 3 ^ 40 * 4143068 * 2
def baseEnd_4143068 : Nat := 472752281835978102465863

theorem tailTrace_4143068 : CollatzResearch.WordTrace tailWord_4143068 prefixEnd_4143068 472752281835978102465863 := by
  unfold tailWord_4143068
  simp only [CollatzResearch.WordTrace]
  refine ⟨75555052077189845263106929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100740069436253127017475905 75555052077189845263106929)
  ·
    refine ⟨56666289057892383947330197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75555052077189845263106929 56666289057892383947330197)
    ·
      refine ⟨2656232299588705497531103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56666289057892383947330197 2656232299588705497531103)
      ·
        refine ⟨3984348449383058246296655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656232299588705497531103 3984348449383058246296655)
        ·
          refine ⟨5976522674074587369444983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984348449383058246296655 5976522674074587369444983)
          ·
            refine ⟨8964784011111881054167475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976522674074587369444983 8964784011111881054167475)
            ·
              refine ⟨13447176016667821581251213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964784011111881054167475 13447176016667821581251213)
              ·
                refine ⟨5042691006250433092969205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13447176016667821581251213 5042691006250433092969205)
                ·
                  refine ⟨472752281835978102465863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042691006250433092969205 472752281835978102465863)
                  ·
                    rfl

theorem cell22_4143068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_4143068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143068 prefixEnd_4143068 := by exact prefixLift 4143068
  have htrace : WordTrace (prefixWord ++ tailWord_4143068) baseStart_4143068 baseEnd_4143068 := by
    simpa [prefixWord, tailWord_4143068, baseEnd_4143068] using wordTrace_append hprefix tailTrace_4143068
  have hstable : (prefixWord ++ tailWord_4143068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143068).length < 2 ^ (prefixWord ++ tailWord_4143068).sum := by decide
  have hdescent : baseEnd_4143068 < baseStart_4143068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143111 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 2, 3]
def baseStart_4143111 : Nat := 118140960795 + 4143111 * 2 ^ 59
def prefixEnd_4143111 : Nat := 4983230072969 + 3 ^ 40 * 4143111 * 2
def baseEnd_4143111 : Nat := 1418271565286696528572457

theorem tailTrace_4143111 : CollatzResearch.WordTrace tailWord_4143111 prefixEnd_4143111 1418271565286696528572457 := by
  unfold tailWord_4143111
  simp only [CollatzResearch.WordTrace]
  refine ⟨151111672493223908870029187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100741114995482605913352791 151111672493223908870029187)
  ·
    refine ⟨226667508739835863305043781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151111672493223908870029187 226667508739835863305043781)
    ·
      refine ⟨42500157888719224369695709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226667508739835863305043781 42500157888719224369695709)
      ·
        refine ⟨15937559208269709138635891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42500157888719224369695709 15937559208269709138635891)
        ·
          refine ⟨23906338812404563707953837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15937559208269709138635891 23906338812404563707953837)
          ·
            refine ⟨8964877054651711390482689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23906338812404563707953837 8964877054651711390482689)
            ·
              refine ⟨6723657790988783542862017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964877054651711390482689 6723657790988783542862017)
              ·
                refine ⟨5042743343241587657146513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723657790988783542862017 5042743343241587657146513)
                ·
                  refine ⟨3782057507431190742859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042743343241587657146513 3782057507431190742859885)
                  ·
                    refine ⟨1418271565286696528572457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782057507431190742859885 1418271565286696528572457)
                    ·
                      rfl

theorem cell22_4143111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_4143111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143111 prefixEnd_4143111 := by exact prefixLift 4143111
  have htrace : WordTrace (prefixWord ++ tailWord_4143111) baseStart_4143111 baseEnd_4143111 := by
    simpa [prefixWord, tailWord_4143111, baseEnd_4143111] using wordTrace_append hprefix tailTrace_4143111
  have hstable : (prefixWord ++ tailWord_4143111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143111).length < 2 ^ (prefixWord ++ tailWord_4143111).sum := by decide
  have hdescent : baseEnd_4143111 < baseStart_4143111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143139 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 3, 3]
def baseStart_4143139 : Nat := 118140960795 + 4143139 * 2 ^ 59
def prefixEnd_4143139 : Nat := 4983230072969 + 3 ^ 40 * 4143139 * 2
def baseEnd_4143139 : Nat := 1418281150258913788872371

theorem tailTrace_4143139 : CollatzResearch.WordTrace tailWord_4143139 prefixEnd_4143139 1418281150258913788872371 := by
  unfold tailWord_4143139
  simp only [CollatzResearch.WordTrace]
  refine ⟨151112693737122469652048471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100741795824748313101365647 151112693737122469652048471)
  ·
    refine ⟨226669040605683704478072707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151112693737122469652048471 226669040605683704478072707)
    ·
      refine ⟨340003560908525556717109061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226669040605683704478072707 340003560908525556717109061)
      ·
        refine ⟨63750667670348541884457949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340003560908525556717109061 63750667670348541884457949)
        ·
          refine ⟨23906500376380703206671731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63750667670348541884457949 23906500376380703206671731)
          ·
            refine ⟨35859750564571054810007597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906500376380703206671731 35859750564571054810007597)
            ·
              refine ⟨13447406461714145553752849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35859750564571054810007597 13447406461714145553752849)
              ·
                refine ⟨10085554846285609165314637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13447406461714145553752849 10085554846285609165314637)
                ·
                  refine ⟨3782083067357103436992989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10085554846285609165314637 3782083067357103436992989)
                  ·
                    refine ⟨1418281150258913788872371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782083067357103436992989 1418281150258913788872371)
                    ·
                      rfl

theorem cell22_4143139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 3].length) (baseStart_4143139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143139 prefixEnd_4143139 := by exact prefixLift 4143139
  have htrace : WordTrace (prefixWord ++ tailWord_4143139) baseStart_4143139 baseEnd_4143139 := by
    simpa [prefixWord, tailWord_4143139, baseEnd_4143139] using wordTrace_append hprefix tailTrace_4143139
  have hstable : (prefixWord ++ tailWord_4143139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143139).length < 2 ^ (prefixWord ++ tailWord_4143139).sum := by decide
  have hdescent : baseEnd_4143139 < baseStart_4143139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143143 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4143143 : Nat := 118140960795 + 4143143 * 2 ^ 59
def prefixEnd_4143143 : Nat := 4983230072969 + 3 ^ 40 * 4143143 * 2
def baseEnd_4143143 : Nat := 1418282519540659111772359

theorem tailTrace_4143143 : CollatzResearch.WordTrace tailWord_4143143 prefixEnd_4143143 1418282519540659111772359 := by
  unfold tailWord_4143143
  simp only [CollatzResearch.WordTrace]
  refine ⟨151112839629107978335194083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100741893086071985556796055 151112839629107978335194083)
  ·
    refine ⟨226669259443661967502791125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151112839629107978335194083 226669259443661967502791125)
    ·
      refine ⟨5312560768210827363346667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 226669259443661967502791125 5312560768210827363346667)
      ·
        refine ⟨7968841152316241045020001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312560768210827363346667 7968841152316241045020001)
        ·
          refine ⟨5976630864237180783765001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7968841152316241045020001 5976630864237180783765001)
          ·
            refine ⟨4482473148177885587823751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976630864237180783765001 4482473148177885587823751)
            ·
              refine ⟨6723709722266828381735627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482473148177885587823751 6723709722266828381735627)
              ·
                refine ⟨10085564583400242572603441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723709722266828381735627 10085564583400242572603441)
                ·
                  refine ⟨7564173437550181929452581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085564583400242572603441 7564173437550181929452581)
                  ·
                    refine ⟨1418282519540659111772359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564173437550181929452581 1418282519540659111772359)
                    ·
                      rfl

theorem cell22_4143143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4143143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143143 prefixEnd_4143143 := by exact prefixLift 4143143
  have htrace : WordTrace (prefixWord ++ tailWord_4143143) baseStart_4143143 baseEnd_4143143 := by
    simpa [prefixWord, tailWord_4143143, baseEnd_4143143] using wordTrace_append hprefix tailTrace_4143143
  have hstable : (prefixWord ++ tailWord_4143143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143143).length < 2 ^ (prefixWord ++ tailWord_4143143).sum := by decide
  have hdescent : baseEnd_4143143 < baseStart_4143143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143167 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_4143167 : Nat := 118140960795 + 4143167 * 2 ^ 59
def prefixEnd_4143167 : Nat := 4983230072969 + 3 ^ 40 * 4143167 * 2
def baseEnd_4143167 : Nat := 1418290735231131049172285

theorem tailTrace_4143167 : CollatzResearch.WordTrace tailWord_4143167 prefixEnd_4143167 1418290735231131049172285 := by
  unfold tailWord_4143167
  simp only [CollatzResearch.WordTrace]
  refine ⟨151113714981021030434067755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100742476654014020289378503 151113714981021030434067755)
  ·
    refine ⟨226670572471531545651101633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151113714981021030434067755 226670572471531545651101633)
    ·
      refine ⟨170002929353648659238326225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226670572471531545651101633 170002929353648659238326225)
      ·
        refine ⟨127502197015236494428744669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170002929353648659238326225 127502197015236494428744669)
        ·
          refine ⟨47813323880713685410779251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127502197015236494428744669 47813323880713685410779251)
          ·
            refine ⟨71719985821070528116168877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47813323880713685410779251 71719985821070528116168877)
            ·
              refine ⟨26894994682901448043563329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71719985821070528116168877 26894994682901448043563329)
              ·
                refine ⟨20171246012176086032672497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26894994682901448043563329 20171246012176086032672497)
                ·
                  refine ⟨15128434509132064524504373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20171246012176086032672497 15128434509132064524504373)
                  ·
                    refine ⟨1418290735231131049172285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15128434509132064524504373 1418290735231131049172285)
                    ·
                      rfl

theorem cell22_4143167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_4143167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143167 prefixEnd_4143167 := by exact prefixLift 4143167
  have htrace : WordTrace (prefixWord ++ tailWord_4143167) baseStart_4143167 baseEnd_4143167 := by
    simpa [prefixWord, tailWord_4143167, baseEnd_4143167] using wordTrace_append hprefix tailTrace_4143167
  have hstable : (prefixWord ++ tailWord_4143167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143167).length < 2 ^ (prefixWord ++ tailWord_4143167).sum := by decide
  have hdescent : baseEnd_4143167 < baseStart_4143167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143169 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 7]
def baseStart_4143169 : Nat := 118140960795 + 4143169 * 2 ^ 59
def prefixEnd_4143169 : Nat := 4983230072969 + 3 ^ 40 * 4143169 * 2
def baseEnd_4143169 : Nat := 472763806624001236874093

theorem tailTrace_4143169 : CollatzResearch.WordTrace tailWord_4143169 prefixEnd_4143169 472763806624001236874093 := by
  unfold tailWord_4143169
  simp only [CollatzResearch.WordTrace]
  refine ⟨151113787927013784775640561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100742525284675856517093707 151113787927013784775640561)
  ·
    refine ⟨113335340945260338581730421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151113787927013784775640561 113335340945260338581730421)
    ·
      refine ⟨10625188213618156742037227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113335340945260338581730421 10625188213618156742037227)
      ·
        refine ⟨15937782320427235113055841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10625188213618156742037227 15937782320427235113055841)
        ·
          refine ⟨11953336740320426334791881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15937782320427235113055841 11953336740320426334791881)
          ·
            refine ⟨8965002555240319751093911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953336740320426334791881 8965002555240319751093911)
            ·
              refine ⟨13447503832860479626640867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965002555240319751093911 13447503832860479626640867)
              ·
                refine ⟨20171255749290719439961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13447503832860479626640867 20171255749290719439961301)
                ·
                  refine ⟨472763806624001236874093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20171255749290719439961301 472763806624001236874093)
                  ·
                    rfl

theorem cell22_4143169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_4143169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143169 prefixEnd_4143169 := by exact prefixLift 4143169
  have htrace : WordTrace (prefixWord ++ tailWord_4143169) baseStart_4143169 baseEnd_4143169 := by
    simpa [prefixWord, tailWord_4143169, baseEnd_4143169] using wordTrace_append hprefix tailTrace_4143169
  have hstable : (prefixWord ++ tailWord_4143169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143169).length < 2 ^ (prefixWord ++ tailWord_4143169).sum := by decide
  have hdescent : baseEnd_4143169 < baseStart_4143169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143257 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_4143257 : Nat := 118140960795 + 4143257 * 2 ^ 59
def prefixEnd_4143257 : Nat := 4983230072969 + 3 ^ 40 * 4143257 * 2
def baseEnd_4143257 : Nat := 1418321544070400814422009

theorem tailTrace_4143257 : CollatzResearch.WordTrace tailWord_4143257 prefixEnd_4143257 1418321544070400814422009 := by
  unfold tailWord_4143257
  simp only [CollatzResearch.WordTrace]
  refine ⟨151116997550694975804844025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100744665033796650536562683 151116997550694975804844025)
  ·
    refine ⟨113337748163021231853633019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151116997550694975804844025 113337748163021231853633019)
    ·
      refine ⟨170006622244531847780449529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113337748163021231853633019 170006622244531847780449529)
      ·
        refine ⟨127504966683398885835337147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170006622244531847780449529 127504966683398885835337147)
        ·
          refine ⟨191257450025098328753005721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127504966683398885835337147 191257450025098328753005721)
          ·
            refine ⟨143443087518823746564754291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191257450025098328753005721 143443087518823746564754291)
            ·
              refine ⟨215164631278235619847131437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143443087518823746564754291 215164631278235619847131437)
              ·
                refine ⟨80686736729338357442674289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215164631278235619847131437 80686736729338357442674289)
                ·
                  refine ⟨60515052547003768082005717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80686736729338357442674289 60515052547003768082005717)
                  ·
                    refine ⟨1418321544070400814422009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60515052547003768082005717 1418321544070400814422009)
                    ·
                      rfl

theorem cell22_4143257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_4143257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143257 prefixEnd_4143257 := by exact prefixLift 4143257
  have htrace : WordTrace (prefixWord ++ tailWord_4143257) baseStart_4143257 baseEnd_4143257 := by
    simpa [prefixWord, tailWord_4143257, baseEnd_4143257] using wordTrace_append hprefix tailTrace_4143257
  have hstable : (prefixWord ++ tailWord_4143257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143257).length < 2 ^ (prefixWord ++ tailWord_4143257).sum := by decide
  have hdescent : baseEnd_4143257 < baseStart_4143257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143261 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4143261 : Nat := 118140960795 + 4143261 * 2 ^ 59
def prefixEnd_4143261 : Nat := 4983230072969 + 3 ^ 40 * 4143261 * 2
def baseEnd_4143261 : Nat := 1418322913352146137321997

theorem tailTrace_4143261 : CollatzResearch.WordTrace tailWord_4143261 prefixEnd_4143261 1418322913352146137321997 := by
  unfold tailWord_4143261
  simp only [CollatzResearch.WordTrace]
  refine ⟨151117143442680484487989637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100744762295120322991993091 151117143442680484487989637)
  ·
    refine ⟨28334464395502590841498057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151117143442680484487989637 28334464395502590841498057)
    ·
      refine ⟨21250848296626943131123543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28334464395502590841498057 21250848296626943131123543)
      ·
        refine ⟨31876272444940414696685315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250848296626943131123543 31876272444940414696685315)
        ·
          refine ⟨47814408667410622045027973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31876272444940414696685315 47814408667410622045027973)
          ·
            refine ⟨8965201625139491633442745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47814408667410622045027973 8965201625139491633442745)
            ·
              refine ⟨6723901218854618725082059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965201625139491633442745 6723901218854618725082059)
              ·
                refine ⟨10085851828281928087623089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723901218854618725082059 10085851828281928087623089)
                ·
                  refine ⟨7564388871211446065717317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085851828281928087623089 7564388871211446065717317)
                  ·
                    refine ⟨1418322913352146137321997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564388871211446065717317 1418322913352146137321997)
                    ·
                      rfl

theorem cell22_4143261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4143261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143261 prefixEnd_4143261 := by exact prefixLift 4143261
  have htrace : WordTrace (prefixWord ++ tailWord_4143261) baseStart_4143261 baseEnd_4143261 := by
    simpa [prefixWord, tailWord_4143261, baseEnd_4143261] using wordTrace_append hprefix tailTrace_4143261
  have hstable : (prefixWord ++ tailWord_4143261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143261).length < 2 ^ (prefixWord ++ tailWord_4143261).sum := by decide
  have hdescent : baseEnd_4143261 < baseStart_4143261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143325 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4143325 : Nat := 118140960795 + 4143325 * 2 ^ 59
def prefixEnd_4143325 : Nat := 4983230072969 + 3 ^ 40 * 4143325 * 2
def baseEnd_4143325 : Nat := 1418344821860071303721801

theorem tailTrace_4143325 : CollatzResearch.WordTrace tailWord_4143325 prefixEnd_4143325 1418344821860071303721801 := by
  unfold tailWord_4143325
  simp only [CollatzResearch.WordTrace]
  refine ⟨151119477714448623418319429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100746318476299082278879619 151119477714448623418319429)
  ·
    refine ⟨28334902071459116890934893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151119477714448623418319429 28334902071459116890934893)
    ·
      refine ⟨10625588276797168834100585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28334902071459116890934893 10625588276797168834100585)
      ·
        refine ⟨7969191207597876625575439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10625588276797168834100585 7969191207597876625575439)
        ·
          refine ⟨11953786811396814938363159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969191207597876625575439 11953786811396814938363159)
          ·
            refine ⟨17930680217095222407544739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953786811396814938363159 17930680217095222407544739)
            ·
              refine ⟨26896020325642833611317109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17930680217095222407544739 26896020325642833611317109)
              ·
                refine ⟨2521501905529015651060979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26896020325642833611317109 2521501905529015651060979)
                ·
                  refine ⟨3782252858293523476591469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521501905529015651060979 3782252858293523476591469)
                  ·
                    refine ⟨1418344821860071303721801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782252858293523476591469 1418344821860071303721801)
                    ·
                      rfl

theorem cell22_4143325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4143325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143325 prefixEnd_4143325 := by exact prefixLift 4143325
  have htrace : WordTrace (prefixWord ++ tailWord_4143325) baseStart_4143325 baseEnd_4143325 := by
    simpa [prefixWord, tailWord_4143325, baseEnd_4143325] using wordTrace_append hprefix tailTrace_4143325
  have hstable : (prefixWord ++ tailWord_4143325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143325).length < 2 ^ (prefixWord ++ tailWord_4143325).sum := by decide
  have hdescent : baseEnd_4143325 < baseStart_4143325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143368 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_4143368 : Nat := 118140960795 + 4143368 * 2 ^ 59
def prefixEnd_4143368 : Nat := 4983230072969 + 3 ^ 40 * 4143368 * 2
def baseEnd_4143368 : Nat := 1418359541638833524896669

theorem tailTrace_4143368 : CollatzResearch.WordTrace tailWord_4143368 prefixEnd_4143368 1418359541638833524896669 := by
  unfold tailWord_4143368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75560523026646420881067379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100747364035528561174756505 75560523026646420881067379)
  ·
    refine ⟨113340784539969631321601069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75560523026646420881067379 113340784539969631321601069)
    ·
      refine ⟨42502794202488611745600401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113340784539969631321601069 42502794202488611745600401)
      ·
        refine ⟨31877095651866458809200301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42502794202488611745600401 31877095651866458809200301)
        ·
          refine ⟨11953910869449922053450113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31877095651866458809200301 11953910869449922053450113)
          ·
            refine ⟨8965433152087441540087585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953910869449922053450113 8965433152087441540087585)
            ·
              refine ⟨6724074864065581155065689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965433152087441540087585 6724074864065581155065689)
              ·
                refine ⟨5043056148049185866299267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724074864065581155065689 5043056148049185866299267)
                ·
                  refine ⟨7564584222073778799448901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043056148049185866299267 7564584222073778799448901)
                  ·
                    refine ⟨1418359541638833524896669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564584222073778799448901 1418359541638833524896669)
                    ·
                      rfl

theorem cell22_4143368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_4143368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143368 prefixEnd_4143368 := by exact prefixLift 4143368
  have htrace : WordTrace (prefixWord ++ tailWord_4143368) baseStart_4143368 baseEnd_4143368 := by
    simpa [prefixWord, tailWord_4143368, baseEnd_4143368] using wordTrace_append hprefix tailTrace_4143368
  have hstable : (prefixWord ++ tailWord_4143368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143368).length < 2 ^ (prefixWord ++ tailWord_4143368).sum := by decide
  have hdescent : baseEnd_4143368 < baseStart_4143368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_4143379 : Nat := 118140960795 + 4143379 * 2 ^ 59
def prefixEnd_4143379 : Nat := 4983230072969 + 3 ^ 40 * 4143379 * 2
def baseEnd_4143379 : Nat := 1418363307163633162871635

theorem tailTrace_4143379 : CollatzResearch.WordTrace tailWord_4143379 prefixEnd_4143379 1418363307163633162871635 := by
  unfold tailWord_4143379
  simp only [CollatzResearch.WordTrace]
  refine ⟨151121447256252990640785191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100747631504168660427190127 151121447256252990640785191)
  ·
    refine ⟨226682170884379485961177787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151121447256252990640785191 226682170884379485961177787)
    ·
      refine ⟨340023256326569228941766681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226682170884379485961177787 340023256326569228941766681)
      ·
        refine ⟨255017442244926921706325011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340023256326569228941766681 255017442244926921706325011)
        ·
          refine ⟨382526163367390382559487517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255017442244926921706325011 382526163367390382559487517)
          ·
            refine ⟨143447311262771393459807819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382526163367390382559487517 143447311262771393459807819)
            ·
              refine ⟨215170966894157090189711729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143447311262771393459807819 215170966894157090189711729)
              ·
                refine ⟨161378225170617817642283797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215170966894157090189711729 161378225170617817642283797)
                ·
                  refine ⟨7564604304872710201982053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161378225170617817642283797 7564604304872710201982053)
                  ·
                    refine ⟨1418363307163633162871635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564604304872710201982053 1418363307163633162871635)
                    ·
                      rfl

theorem cell22_4143379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_4143379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143379 prefixEnd_4143379 := by exact prefixLift 4143379
  have htrace : WordTrace (prefixWord ++ tailWord_4143379) baseStart_4143379 baseEnd_4143379 := by
    simpa [prefixWord, tailWord_4143379, baseEnd_4143379] using wordTrace_append hprefix tailTrace_4143379
  have hstable : (prefixWord ++ tailWord_4143379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143379).length < 2 ^ (prefixWord ++ tailWord_4143379).sum := by decide
  have hdescent : baseEnd_4143379 < baseStart_4143379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143381 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_4143381 : Nat := 118140960795 + 4143381 * 2 ^ 59
def prefixEnd_4143381 : Nat := 4983230072969 + 3 ^ 40 * 4143381 * 2
def baseEnd_4143381 : Nat := 1418363991804505824321629

theorem tailTrace_4143381 : CollatzResearch.WordTrace tailWord_4143381 prefixEnd_4143381 1418363991804505824321629 := by
  unfold tailWord_4143381
  simp only [CollatzResearch.WordTrace]
  refine ⟨151121520202245744982357997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100747680134830496654905331 151121520202245744982357997)
  ·
    refine ⟨56670570075842154368384249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151121520202245744982357997 56670570075842154368384249)
    ·
      refine ⟨42502927556881615776288187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56670570075842154368384249 42502927556881615776288187)
      ·
        refine ⟨63754391335322423664432281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42502927556881615776288187 63754391335322423664432281)
        ·
          refine ⟨47815793501491817748324211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63754391335322423664432281 47815793501491817748324211)
          ·
            refine ⟨71723690252237726622486317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47815793501491817748324211 71723690252237726622486317)
            ·
              refine ⟨26896383844589147483432369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71723690252237726622486317 26896383844589147483432369)
              ·
                refine ⟨20172287883441860612574277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26896383844589147483432369 20172287883441860612574277)
                ·
                  refine ⟨3782303978145348864857677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20172287883441860612574277 3782303978145348864857677)
                  ·
                    refine ⟨1418363991804505824321629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782303978145348864857677 1418363991804505824321629)
                    ·
                      rfl

theorem cell22_4143381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_4143381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143381 prefixEnd_4143381 := by exact prefixLift 4143381
  have htrace : WordTrace (prefixWord ++ tailWord_4143381) baseStart_4143381 baseEnd_4143381 := by
    simpa [prefixWord, tailWord_4143381, baseEnd_4143381] using wordTrace_append hprefix tailTrace_4143381
  have hstable : (prefixWord ++ tailWord_4143381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143381).length < 2 ^ (prefixWord ++ tailWord_4143381).sum := by decide
  have hdescent : baseEnd_4143381 < baseStart_4143381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143383 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 4]
def baseStart_4143383 : Nat := 118140960795 + 4143383 * 2 ^ 59
def prefixEnd_4143383 : Nat := 4983230072969 + 3 ^ 40 * 4143383 * 2
def baseEnd_4143383 : Nat := 472788225481792828590541

theorem tailTrace_4143383 : CollatzResearch.WordTrace tailWord_4143383 prefixEnd_4143383 472788225481792828590541 := by
  unfold tailWord_4143383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151121593148238499323930803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100747728765492332882620535 151121593148238499323930803)
  ·
    refine ⟨226682389722357748985896205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151121593148238499323930803 226682389722357748985896205)
    ·
      refine ⟨85005896145884155869711077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226682389722357748985896205 85005896145884155869711077)
      ·
        refine ⟨15938605527353279225570827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85005896145884155869711077 15938605527353279225570827)
        ·
          refine ⟨23907908291029918838356241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938605527353279225570827 23907908291029918838356241)
          ·
            refine ⟨17930931218272439128767181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23907908291029918838356241 17930931218272439128767181)
            ·
              refine ⟨6724099206852164673287693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17930931218272439128767181 6724099206852164673287693)
              ·
                refine ⟨2521537202569561752482885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6724099206852164673287693 2521537202569561752482885)
                ·
                  refine ⟨472788225481792828590541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521537202569561752482885 472788225481792828590541)
                  ·
                    rfl

theorem cell22_4143383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 4].length) (baseStart_4143383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143383 prefixEnd_4143383 := by exact prefixLift 4143383
  have htrace : WordTrace (prefixWord ++ tailWord_4143383) baseStart_4143383 baseEnd_4143383 := by
    simpa [prefixWord, tailWord_4143383, baseEnd_4143383] using wordTrace_append hprefix tailTrace_4143383
  have hstable : (prefixWord ++ tailWord_4143383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143383).length < 2 ^ (prefixWord ++ tailWord_4143383).sum := by decide
  have hdescent : baseEnd_4143383 < baseStart_4143383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143396 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_4143396 : Nat := 118140960795 + 4143396 * 2 ^ 59
def prefixEnd_4143396 : Nat := 4983230072969 + 3 ^ 40 * 4143396 * 2
def baseEnd_4143396 : Nat := 1418369126611050785196583

theorem tailTrace_4143396 : CollatzResearch.WordTrace tailWord_4143396 prefixEnd_4143396 1418369126611050785196583 := by
  unfold tailWord_4143396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75561033648595701272077021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100748044864794268362769361 75561033648595701272077021)
  ·
    refine ⟨28335387618223387977028883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75561033648595701272077021 28335387618223387977028883)
    ·
      refine ⟨42503081427335081965543325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28335387618223387977028883 42503081427335081965543325)
      ·
        refine ⟨15938655535250655737078747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42503081427335081965543325 15938655535250655737078747)
        ·
          refine ⟨23907983302875983605618121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938655535250655737078747 23907983302875983605618121)
          ·
            refine ⟨17930987477156987704213591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23907983302875983605618121 17930987477156987704213591)
            ·
              refine ⟨26896481215735481556320387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17930987477156987704213591 26896481215735481556320387)
              ·
                refine ⟨40344721823603222334480581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26896481215735481556320387 40344721823603222334480581)
                ·
                  refine ⟨7564635341925604187715109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40344721823603222334480581 7564635341925604187715109)
                  ·
                    refine ⟨1418369126611050785196583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564635341925604187715109 1418369126611050785196583)
                    ·
                      rfl

theorem cell22_4143396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_4143396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143396 prefixEnd_4143396 := by exact prefixLift 4143396
  have htrace : WordTrace (prefixWord ++ tailWord_4143396) baseStart_4143396 baseEnd_4143396 := by
    simpa [prefixWord, tailWord_4143396, baseEnd_4143396] using wordTrace_append hprefix tailTrace_4143396
  have hstable : (prefixWord ++ tailWord_4143396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143396).length < 2 ^ (prefixWord ++ tailWord_4143396).sum := by decide
  have hdescent : baseEnd_4143396 < baseStart_4143396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143400 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_4143400 : Nat := 118140960795 + 4143400 * 2 ^ 59
def prefixEnd_4143400 : Nat := 4983230072969 + 3 ^ 40 * 4143400 * 2
def baseEnd_4143400 : Nat := 472790165297598702698857

theorem tailTrace_4143400 : CollatzResearch.WordTrace tailWord_4143400 prefixEnd_4143400 472790165297598702698857 := by
  unfold tailWord_4143400
  simp only [CollatzResearch.WordTrace]
  refine ⟨75561106594588455613649827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100748142126117940818199769 75561106594588455613649827)
  ·
    refine ⟨113341659891882683420474741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75561106594588455613649827 113341659891882683420474741)
    ·
      refine ⟨10625780614864001570669507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113341659891882683420474741 10625780614864001570669507)
      ·
        refine ⟨15938670922296002356004261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10625780614864001570669507 15938670922296002356004261)
        ·
          refine ⟨2988500797930500441750799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15938670922296002356004261 2988500797930500441750799)
          ·
            refine ⟨4482751196895750662626199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988500797930500441750799 4482751196895750662626199)
            ·
              refine ⟨6724126795343625993939299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482751196895750662626199 6724126795343625993939299)
              ·
                refine ⟨10086190193015438990908949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724126795343625993939299 10086190193015438990908949)
                ·
                  refine ⟨472790165297598702698857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10086190193015438990908949 472790165297598702698857)
                  ·
                    rfl

theorem cell22_4143400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_4143400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143400 prefixEnd_4143400 := by exact prefixLift 4143400
  have htrace : WordTrace (prefixWord ++ tailWord_4143400) baseStart_4143400 baseEnd_4143400 := by
    simpa [prefixWord, tailWord_4143400, baseEnd_4143400] using wordTrace_append hprefix tailTrace_4143400
  have hstable : (prefixWord ++ tailWord_4143400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143400).length < 2 ^ (prefixWord ++ tailWord_4143400).sum := by decide
  have hdescent : baseEnd_4143400 < baseStart_4143400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143424 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_4143424 : Nat := 118140960795 + 4143424 * 2 ^ 59
def prefixEnd_4143424 : Nat := 4983230072969 + 3 ^ 40 * 4143424 * 2
def baseEnd_4143424 : Nat := 1418378711583268045496497

theorem tailTrace_4143424 : CollatzResearch.WordTrace tailWord_4143424 prefixEnd_4143424 1418378711583268045496497 := by
  unfold tailWord_4143424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75561544270544981663086663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100748725694059975550782217 75561544270544981663086663)
  ·
    refine ⟨113342316405817472494629995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75561544270544981663086663 113342316405817472494629995)
    ·
      refine ⟨170013474608726208741944993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113342316405817472494629995 170013474608726208741944993)
      ·
        refine ⟨127510105956544656556458745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170013474608726208741944993 127510105956544656556458745)
        ·
          refine ⟨95632579467408492417344059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127510105956544656556458745 95632579467408492417344059)
          ·
            refine ⟨143448869201112738626016089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95632579467408492417344059 143448869201112738626016089)
            ·
              refine ⟨107586651900834553969512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143448869201112738626016089 107586651900834553969512067)
              ·
                refine ⟨161379977851251830954268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107586651900834553969512067 161379977851251830954268101)
                ·
                  refine ⟨30258745847109718303925269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161379977851251830954268101 30258745847109718303925269)
                  ·
                    refine ⟨1418378711583268045496497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30258745847109718303925269 1418378711583268045496497)
                    ·
                      rfl

theorem cell22_4143424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_4143424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143424 prefixEnd_4143424 := by exact prefixLift 4143424
  have htrace : WordTrace (prefixWord ++ tailWord_4143424) baseStart_4143424 baseEnd_4143424 := by
    simpa [prefixWord, tailWord_4143424, baseEnd_4143424] using wordTrace_append hprefix tailTrace_4143424
  have hstable : (prefixWord ++ tailWord_4143424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143424).length < 2 ^ (prefixWord ++ tailWord_4143424).sum := by decide
  have hdescent : baseEnd_4143424 < baseStart_4143424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143439 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 7]
def baseStart_4143439 : Nat := 118140960795 + 4143439 * 2 ^ 59
def prefixEnd_4143439 : Nat := 4983230072969 + 3 ^ 40 * 4143439 * 2
def baseEnd_4143439 : Nat := 472794615463271002123817

theorem tailTrace_4143439 : CollatzResearch.WordTrace tailWord_4143439 prefixEnd_4143439 472794615463271002123817 := by
  unfold tailWord_4143439
  simp only [CollatzResearch.WordTrace]
  refine ⟨151123635636035620887969371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100749090424023747258646247 151123635636035620887969371)
  ·
    refine ⟨226685453454053431331954057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151123635636035620887969371 226685453454053431331954057)
    ·
      refine ⟨170014090090540073498965543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226685453454053431331954057 170014090090540073498965543)
      ·
        refine ⟨255021135135810110248448315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170014090090540073498965543 255021135135810110248448315)
        ·
          refine ⟨382531702703715165372672473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255021135135810110248448315 382531702703715165372672473)
          ·
            refine ⟨286898777027786374029504355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382531702703715165372672473 286898777027786374029504355)
            ·
              refine ⟨430348165541679561044256533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286898777027786374029504355 430348165541679561044256533)
              ·
                refine ⟨20172570259766229423949525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430348165541679561044256533 20172570259766229423949525)
                ·
                  refine ⟨472794615463271002123817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20172570259766229423949525 472794615463271002123817)
                  ·
                    rfl

theorem cell22_4143439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_4143439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143439 prefixEnd_4143439 := by exact prefixLift 4143439
  have htrace : WordTrace (prefixWord ++ tailWord_4143439) baseStart_4143439 baseEnd_4143439 := by
    simpa [prefixWord, tailWord_4143439, baseEnd_4143439] using wordTrace_append hprefix tailTrace_4143439
  have hstable : (prefixWord ++ tailWord_4143439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143439).length < 2 ^ (prefixWord ++ tailWord_4143439).sum := by decide
  have hdescent : baseEnd_4143439 < baseStart_4143439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143460 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4143460 : Nat := 118140960795 + 4143460 * 2 ^ 59
def prefixEnd_4143460 : Nat := 4983230072969 + 3 ^ 40 * 4143460 * 2
def baseEnd_4143460 : Nat := 1418391035118975951596387

theorem tailTrace_4143460 : CollatzResearch.WordTrace tailWord_4143460 prefixEnd_4143460 1418391035118975951596387 := by
  unfold tailWord_4143460
  simp only [CollatzResearch.WordTrace]
  refine ⟨75562200784479770737241917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100749601045973027649655889 75562200784479770737241917)
  ·
    refine ⟨28335825294179914026465719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75562200784479770737241917 28335825294179914026465719)
    ·
      refine ⟨42503737941269871039698579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28335825294179914026465719 42503737941269871039698579)
      ·
        refine ⟨63755606911904806559547869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42503737941269871039698579 63755606911904806559547869)
        ·
          refine ⟨23908352591964302459830451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63755606911904806559547869 23908352591964302459830451)
          ·
            refine ⟨35862528887946453689745677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23908352591964302459830451 35862528887946453689745677)
            ·
              refine ⟨13448448332979920133654629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35862528887946453689745677 13448448332979920133654629)
              ·
                refine ⟨2521584062433735025060243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13448448332979920133654629 2521584062433735025060243)
                ·
                  refine ⟨3782376093650602537590365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521584062433735025060243 3782376093650602537590365)
                  ·
                    refine ⟨1418391035118975951596387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782376093650602537590365 1418391035118975951596387)
                    ·
                      rfl

theorem cell22_4143460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4143460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143460 prefixEnd_4143460 := by exact prefixLift 4143460
  have htrace : WordTrace (prefixWord ++ tailWord_4143460) baseStart_4143460 baseEnd_4143460 := by
    simpa [prefixWord, tailWord_4143460, baseEnd_4143460] using wordTrace_append hprefix tailTrace_4143460
  have hstable : (prefixWord ++ tailWord_4143460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143460).length < 2 ^ (prefixWord ++ tailWord_4143460).sum := by decide
  have hdescent : baseEnd_4143460 < baseStart_4143460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143548 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4143548 : Nat := 118140960795 + 4143548 * 2 ^ 59
def prefixEnd_4143548 : Nat := 4983230072969 + 3 ^ 40 * 4143548 * 2
def baseEnd_4143548 : Nat := 1418421159317373055396117

theorem tailTrace_4143548 : CollatzResearch.WordTrace tailWord_4143548 prefixEnd_4143548 1418421159317373055396117 := by
  unfold tailWord_4143548
  simp only [CollatzResearch.WordTrace]
  refine ⟨75563805596320366251843649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100751740795093821669124865 75563805596320366251843649)
  ·
    refine ⟨56672854197240274688882737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75563805596320366251843649 56672854197240274688882737)
    ·
      refine ⟨42504640647930206016662053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56672854197240274688882737 42504640647930206016662053)
      ·
        refine ⟨7969620121486913628124135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42504640647930206016662053 7969620121486913628124135)
        ·
          refine ⟨11954430182230370442186203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969620121486913628124135 11954430182230370442186203)
          ·
            refine ⟨17931645273345555663279305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954430182230370442186203 17931645273345555663279305)
            ·
              refine ⟨13448733955009166747459479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17931645273345555663279305 13448733955009166747459479)
              ·
                refine ⟨20173100932513750121189219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448733955009166747459479 20173100932513750121189219)
                ·
                  refine ⟨30259651398770625181783829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20173100932513750121189219 30259651398770625181783829)
                  ·
                    refine ⟨1418421159317373055396117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30259651398770625181783829 1418421159317373055396117)
                    ·
                      rfl

theorem cell22_4143548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4143548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143548 prefixEnd_4143548 := by exact prefixLift 4143548
  have htrace : WordTrace (prefixWord ++ tailWord_4143548) baseStart_4143548 baseEnd_4143548 := by
    simpa [prefixWord, tailWord_4143548, baseEnd_4143548] using wordTrace_append hprefix tailTrace_4143548
  have hstable : (prefixWord ++ tailWord_4143548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143548).length < 2 ^ (prefixWord ++ tailWord_4143548).sum := by decide
  have hdescent : baseEnd_4143548 < baseStart_4143548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143576 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_4143576 : Nat := 118140960795 + 4143576 * 2 ^ 59
def prefixEnd_4143576 : Nat := 4983230072969 + 3 ^ 40 * 4143576 * 2
def baseEnd_4143576 : Nat := 1418430744289590315696031

theorem tailTrace_4143576 : CollatzResearch.WordTrace tailWord_4143576 prefixEnd_4143576 1418430744289590315696031 := by
  unfold tailWord_4143576
  simp only [CollatzResearch.WordTrace]
  refine ⟨75564316218269646642853291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100752421624359528857137721 75564316218269646642853291)
  ·
    refine ⟨113346474327404469964279937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75564316218269646642853291 113346474327404469964279937)
    ·
      refine ⟨85009855745553352473209953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113346474327404469964279937 85009855745553352473209953)
      ·
        refine ⟨63757391809165014354907465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85009855745553352473209953 63757391809165014354907465)
        ·
          refine ⟨47818043856873760766180599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63757391809165014354907465 47818043856873760766180599)
          ·
            refine ⟨71727065785310641149270899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47818043856873760766180599 71727065785310641149270899)
            ·
              refine ⟨107590598677965961723906349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71727065785310641149270899 107590598677965961723906349)
              ·
                refine ⟨40346474504237235646464881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107590598677965961723906349 40346474504237235646464881)
                ·
                  refine ⟨30259855878177926734848661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40346474504237235646464881 30259855878177926734848661)
                  ·
                    refine ⟨1418430744289590315696031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30259855878177926734848661 1418430744289590315696031)
                    ·
                      rfl

theorem cell22_4143576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_4143576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143576 prefixEnd_4143576 := by exact prefixLift 4143576
  have htrace : WordTrace (prefixWord ++ tailWord_4143576) baseStart_4143576 baseEnd_4143576 := by
    simpa [prefixWord, tailWord_4143576, baseEnd_4143576] using wordTrace_append hprefix tailTrace_4143576
  have hstable : (prefixWord ++ tailWord_4143576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143576).length < 2 ^ (prefixWord ++ tailWord_4143576).sum := by decide
  have hdescent : baseEnd_4143576 < baseStart_4143576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143683 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_4143683 : Nat := 118140960795 + 4143683 * 2 ^ 59
def prefixEnd_4143683 : Nat := 4983230072969 + 3 ^ 40 * 4143683 * 2
def baseEnd_4143683 : Nat := 1418467372576277703270703

theorem tailTrace_4143683 : CollatzResearch.WordTrace tailWord_4143683 prefixEnd_4143683 1418467372576277703270703 := by
  unfold tailWord_4143683
  simp only [CollatzResearch.WordTrace]
  refine ⟨151132535047151650559851703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100755023364767767039901135 151132535047151650559851703)
  ·
    refine ⟨226698802570727475839777555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151132535047151650559851703 226698802570727475839777555)
    ·
      refine ⟨340048203856091213759666333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226698802570727475839777555 340048203856091213759666333)
      ·
        refine ⟨127518076446034205159874875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340048203856091213759666333 127518076446034205159874875)
        ·
          refine ⟨191277114669051307739812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127518076446034205159874875 191277114669051307739812313)
          ·
            refine ⟨143457836001788480804859235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191277114669051307739812313 143457836001788480804859235)
            ·
              refine ⟨215186754002682721207288853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143457836001788480804859235 215186754002682721207288853)
              ·
                refine ⟨10086879093875752556591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215186754002682721207288853 10086879093875752556591665)
                ·
                  refine ⟨7565159320406814417443749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10086879093875752556591665 7565159320406814417443749)
                  ·
                    refine ⟨1418467372576277703270703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565159320406814417443749 1418467372576277703270703)
                    ·
                      rfl

theorem cell22_4143683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_4143683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143683 prefixEnd_4143683 := by exact prefixLift 4143683
  have htrace : WordTrace (prefixWord ++ tailWord_4143683) baseStart_4143683 baseEnd_4143683 := by
    simpa [prefixWord, tailWord_4143683, baseEnd_4143683] using wordTrace_append hprefix tailTrace_4143683
  have hstable : (prefixWord ++ tailWord_4143683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143683).length < 2 ^ (prefixWord ++ tailWord_4143683).sum := by decide
  have hdescent : baseEnd_4143683 < baseStart_4143683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143685 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_4143685 : Nat := 118140960795 + 4143685 * 2 ^ 59
def prefixEnd_4143685 : Nat := 4983230072969 + 3 ^ 40 * 4143685 * 2
def baseEnd_4143685 : Nat := 1418468057217150364720697

theorem tailTrace_4143685 : CollatzResearch.WordTrace tailWord_4143685 prefixEnd_4143685 1418468057217150364720697 := by
  unfold tailWord_4143685
  simp only [CollatzResearch.WordTrace]
  refine ⟨151132607993144404901424509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100755071995429603267616339 151132607993144404901424509)
  ·
    refine ⟨56674727997429151838034191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151132607993144404901424509 56674727997429151838034191)
    ·
      refine ⟨85012091996143727757051287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56674727997429151838034191 85012091996143727757051287)
      ·
        refine ⟨127518137994215591635576931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85012091996143727757051287 127518137994215591635576931)
        ·
          refine ⟨191277206991323387453365397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127518137994215591635576931 191277206991323387453365397)
          ·
            refine ⟨8966119077718283786876503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 191277206991323387453365397 8966119077718283786876503)
            ·
              refine ⟨13449178616577425680314755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966119077718283786876503 13449178616577425680314755)
              ·
                refine ⟨20173767924866138520472133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449178616577425680314755 20173767924866138520472133)
                ·
                  refine ⟨3782581485912400972588525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20173767924866138520472133 3782581485912400972588525)
                  ·
                    refine ⟨1418468057217150364720697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782581485912400972588525 1418468057217150364720697)
                    ·
                      rfl

theorem cell22_4143685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_4143685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143685 prefixEnd_4143685 := by exact prefixLift 4143685
  have htrace : WordTrace (prefixWord ++ tailWord_4143685) baseStart_4143685 baseEnd_4143685 := by
    simpa [prefixWord, tailWord_4143685, baseEnd_4143685] using wordTrace_append hprefix tailTrace_4143685
  have hstable : (prefixWord ++ tailWord_4143685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143685).length < 2 ^ (prefixWord ++ tailWord_4143685).sum := by decide
  have hdescent : baseEnd_4143685 < baseStart_4143685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143698 : List Nat := [3, 2, 2, 1, 2, 1, 2, 9]
def baseStart_4143698 : Nat := 118140960795 + 4143698 * 2 ^ 59
def prefixEnd_4143698 : Nat := 4983230072969 + 3 ^ 40 * 4143698 * 2
def baseEnd_4143698 : Nat := 157608056375869184905073

theorem tailTrace_4143698 : CollatzResearch.WordTrace tailWord_4143698 prefixEnd_4143698 157608056375869184905073 := by
  unfold tailWord_4143698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37783270535524327030411937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100755388094731538747765165 37783270535524327030411937)
  ·
    refine ⟨28337452901643245272808953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37783270535524327030411937 28337452901643245272808953)
    ·
      refine ⟨21253089676232433954606715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28337452901643245272808953 21253089676232433954606715)
      ·
        refine ⟨31879634514348650931910073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253089676232433954606715 31879634514348650931910073)
        ·
          refine ⟨23909725885761488198932555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31879634514348650931910073 23909725885761488198932555)
          ·
            refine ⟨35864588828642232298398833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23909725885761488198932555 35864588828642232298398833)
            ·
              refine ⟨26898441621481674223799125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35864588828642232298398833 26898441621481674223799125)
              ·
                refine ⟨157608056375869184905073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26898441621481674223799125 157608056375869184905073)
                ·
                  rfl

theorem cell22_4143698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_4143698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143698 prefixEnd_4143698 := by exact prefixLift 4143698
  have htrace : WordTrace (prefixWord ++ tailWord_4143698) baseStart_4143698 baseEnd_4143698 := by
    simpa [prefixWord, tailWord_4143698, baseEnd_4143698] using wordTrace_append hprefix tailTrace_4143698
  have hstable : (prefixWord ++ tailWord_4143698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143698).length < 2 ^ (prefixWord ++ tailWord_4143698).sum := by decide
  have hdescent : baseEnd_4143698 < baseStart_4143698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143747 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 1, 3]
def baseStart_4143747 : Nat := 118140960795 + 4143747 * 2 ^ 59
def prefixEnd_4143747 : Nat := 4983230072969 + 3 ^ 40 * 4143747 * 2
def baseEnd_4143747 : Nat := 1418489281084202869670507

theorem tailTrace_4143747 : CollatzResearch.WordTrace tailWord_4143747 prefixEnd_4143747 1418489281084202869670507 := by
  unfold tailWord_4143747
  simp only [CollatzResearch.WordTrace]
  refine ⟨151134869318919789490181495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100756579545946526326787663 151134869318919789490181495)
  ·
    refine ⟨226702303978379684235272243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151134869318919789490181495 226702303978379684235272243)
    ·
      refine ⟨340053455967569526352908365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226702303978379684235272243 340053455967569526352908365)
      ·
        refine ⟨127520045987838572382340637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340053455967569526352908365 127520045987838572382340637)
        ·
          refine ⟨47820017245439464643377739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127520045987838572382340637 47820017245439464643377739)
          ·
            refine ⟨71730025868159196965066609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47820017245439464643377739 71730025868159196965066609)
            ·
              refine ⟨53797519401119397723799957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71730025868159196965066609 53797519401119397723799957)
              ·
                refine ⟨2521758721927471768303123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53797519401119397723799957 2521758721927471768303123)
                ·
                  refine ⟨3782638082891207652454685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521758721927471768303123 3782638082891207652454685)
                  ·
                    refine ⟨1418489281084202869670507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782638082891207652454685 1418489281084202869670507)
                    ·
                      rfl

theorem cell22_4143747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 3].length) (baseStart_4143747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143747 prefixEnd_4143747 := by exact prefixLift 4143747
  have htrace : WordTrace (prefixWord ++ tailWord_4143747) baseStart_4143747 baseEnd_4143747 := by
    simpa [prefixWord, tailWord_4143747, baseEnd_4143747] using wordTrace_append hprefix tailTrace_4143747
  have hstable : (prefixWord ++ tailWord_4143747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143747).length < 2 ^ (prefixWord ++ tailWord_4143747).sum := by decide
  have hdescent : baseEnd_4143747 < baseStart_4143747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143798 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4143798 : Nat := 118140960795 + 4143798 * 2 ^ 59
def prefixEnd_4143798 : Nat := 4983230072969 + 3 ^ 40 * 4143798 * 2
def baseEnd_4143798 : Nat := 1418506739426455736645351

theorem tailTrace_4143798 : CollatzResearch.WordTrace tailWord_4143798 prefixEnd_4143798 1418506739426455736645351 := by
  unfold tailWord_4143798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446045590108439075018003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100757819627823350133525365 9446045590108439075018003)
  ·
    refine ⟨14169068385162658612527005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446045590108439075018003 14169068385162658612527005)
    ·
      refine ⟨5313400644435996979697627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14169068385162658612527005 5313400644435996979697627)
      ·
        refine ⟨7970100966653995469546441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313400644435996979697627 7970100966653995469546441)
        ·
          refine ⟨5977575724990496602159831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7970100966653995469546441 5977575724990496602159831)
          ·
            refine ⟨8966363587485744903239747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977575724990496602159831 8966363587485744903239747)
            ·
              refine ⟨13449545381228617354859621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966363587485744903239747 13449545381228617354859621)
              ·
                refine ⟨2521789758980365754036179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13449545381228617354859621 2521789758980365754036179)
                ·
                  refine ⟨3782684638470548631054269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521789758980365754036179 3782684638470548631054269)
                  ·
                    refine ⟨1418506739426455736645351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782684638470548631054269 1418506739426455736645351)
                    ·
                      rfl

theorem cell22_4143798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4143798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143798 prefixEnd_4143798 := by exact prefixLift 4143798
  have htrace : WordTrace (prefixWord ++ tailWord_4143798) baseStart_4143798 baseEnd_4143798 := by
    simpa [prefixWord, tailWord_4143798, baseEnd_4143798] using wordTrace_append hprefix tailTrace_4143798
  have hstable : (prefixWord ++ tailWord_4143798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143798).length < 2 ^ (prefixWord ++ tailWord_4143798).sum := by decide
  have hdescent : baseEnd_4143798 < baseStart_4143798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143809 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4143809 : Nat := 118140960795 + 4143809 * 2 ^ 59
def prefixEnd_4143809 : Nat := 4983230072969 + 3 ^ 40 * 4143809 * 2
def baseEnd_4143809 : Nat := 1418510504951255374620317

theorem tailTrace_4143809 : CollatzResearch.WordTrace tailWord_4143809 prefixEnd_4143809 1418510504951255374620317 := by
  unfold tailWord_4143809
  simp only [CollatzResearch.WordTrace]
  refine ⟨151137130644695174078938481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100758087096463449385958987 151137130644695174078938481)
  ·
    refine ⟨113352847983521380559203861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151137130644695174078938481 113352847983521380559203861)
    ·
      refine ⟨5313414749227564713712681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113352847983521380559203861 5313414749227564713712681)
      ·
        refine ⟨3985061061920673535284511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313414749227564713712681 3985061061920673535284511)
        ·
          refine ⟨5977591592881010302926767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985061061920673535284511 5977591592881010302926767)
          ·
            refine ⟨8966387389321515454390151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977591592881010302926767 8966387389321515454390151)
            ·
              refine ⟨13449581083982273181585227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966387389321515454390151 13449581083982273181585227)
              ·
                refine ⟨20174371625973409772377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449581083982273181585227 20174371625973409772377841)
                ·
                  refine ⟨15130778719480057329283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20174371625973409772377841 15130778719480057329283381)
                  ·
                    refine ⟨1418510504951255374620317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15130778719480057329283381 1418510504951255374620317)
                    ·
                      rfl

theorem cell22_4143809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4143809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143809 prefixEnd_4143809 := by exact prefixLift 4143809
  have htrace : WordTrace (prefixWord ++ tailWord_4143809) baseStart_4143809 baseEnd_4143809 := by
    simpa [prefixWord, tailWord_4143809, baseEnd_4143809] using wordTrace_append hprefix tailTrace_4143809
  have hstable : (prefixWord ++ tailWord_4143809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143809).length < 2 ^ (prefixWord ++ tailWord_4143809).sum := by decide
  have hdescent : baseEnd_4143809 < baseStart_4143809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143854 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_4143854 : Nat := 118140960795 + 4143854 * 2 ^ 59
def prefixEnd_4143854 : Nat := 4983230072969 + 3 ^ 40 * 4143854 * 2
def baseEnd_4143854 : Nat := 1418525909370890257245179

theorem tailTrace_4143854 : CollatzResearch.WordTrace tailWord_4143854 prefixEnd_4143854 1418525909370890257245179 := by
  unfold tailWord_4143854
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892346491191518345540827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100759181286354764509551077 18892346491191518345540827)
  ·
    refine ⟨28338519736787277518311241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18892346491191518345540827 28338519736787277518311241)
    ·
      refine ⟨21253889802590458138733431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28338519736787277518311241 21253889802590458138733431)
      ·
        refine ⟨31880834703885687208100147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253889802590458138733431 31880834703885687208100147)
        ·
          refine ⟨47821252055828530812150221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31880834703885687208100147 47821252055828530812150221)
          ·
            refine ⟨17932969520935699054556333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47821252055828530812150221 17932969520935699054556333)
            ·
              refine ⟨6724863570350887145458625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17932969520935699054556333 6724863570350887145458625)
              ·
                refine ⟨5043647677763165359093969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724863570350887145458625 5043647677763165359093969)
                ·
                  refine ⟨3782735758322374019320477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043647677763165359093969 3782735758322374019320477)
                  ·
                    refine ⟨1418525909370890257245179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782735758322374019320477 1418525909370890257245179)
                    ·
                      rfl

theorem cell22_4143854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_4143854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143854 prefixEnd_4143854 := by exact prefixLift 4143854
  have htrace : WordTrace (prefixWord ++ tailWord_4143854) baseStart_4143854 baseEnd_4143854 := by
    simpa [prefixWord, tailWord_4143854, baseEnd_4143854] using wordTrace_append hprefix tailTrace_4143854
  have hstable : (prefixWord ++ tailWord_4143854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143854).length < 2 ^ (prefixWord ++ tailWord_4143854).sum := by decide
  have hdescent : baseEnd_4143854 < baseStart_4143854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143882 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_4143882 : Nat := 118140960795 + 4143882 * 2 ^ 59
def prefixEnd_4143882 : Nat := 4983230072969 + 3 ^ 40 * 4143882 * 2
def baseEnd_4143882 : Nat := 1418535494343107517545093

theorem tailTrace_4143882 : CollatzResearch.WordTrace tailWord_4143882 prefixEnd_4143882 1418535494343107517545093 := by
  unfold tailWord_4143882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784948293357676886586475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100759862115620471697563933 37784948293357676886586475)
  ·
    refine ⟨56677422440036515329879713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784948293357676886586475 56677422440036515329879713)
    ·
      refine ⟨42508066830027386497409785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56677422440036515329879713 42508066830027386497409785)
      ·
        refine ⟨31881050122520539873057339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42508066830027386497409785 31881050122520539873057339)
        ·
          refine ⟨47821575183780809809586009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31881050122520539873057339 47821575183780809809586009)
          ·
            refine ⟨35866181387835607357189507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47821575183780809809586009 35866181387835607357189507)
            ·
              refine ⟨53799272081753411035784261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35866181387835607357189507 53799272081753411035784261)
              ·
                refine ⟨10087363515328764569209549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53799272081753411035784261 10087363515328764569209549)
                ·
                  refine ⟨3782761318248286713453581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10087363515328764569209549 3782761318248286713453581)
                  ·
                    refine ⟨1418535494343107517545093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782761318248286713453581 1418535494343107517545093)
                    ·
                      rfl

theorem cell22_4143882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_4143882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143882 prefixEnd_4143882 := by exact prefixLift 4143882
  have htrace : WordTrace (prefixWord ++ tailWord_4143882) baseStart_4143882 baseEnd_4143882 := by
    simpa [prefixWord, tailWord_4143882, baseEnd_4143882] using wordTrace_append hprefix tailTrace_4143882
  have hstable : (prefixWord ++ tailWord_4143882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143882).length < 2 ^ (prefixWord ++ tailWord_4143882).sum := by decide
  have hdescent : baseEnd_4143882 < baseStart_4143882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143912 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_4143912 : Nat := 118140960795 + 4143912 * 2 ^ 59
def prefixEnd_4143912 : Nat := 4983230072969 + 3 ^ 40 * 4143912 * 2
def baseEnd_4143912 : Nat := 472848587985399146431667

theorem tailTrace_4143912 : CollatzResearch.WordTrace tailWord_4143912 prefixEnd_4143912 472848587985399146431667 := by
  unfold tailWord_4143912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570443681661011334968995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100760591575548015113291993 75570443681661011334968995)
  ·
    refine ⟨113355665522491517002453493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75570443681661011334968995 113355665522491517002453493)
    ·
      refine ⟨10627093642733579718980015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113355665522491517002453493 10627093642733579718980015)
      ·
        refine ⟨15940640464100369578470023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627093642733579718980015 15940640464100369578470023)
        ·
          refine ⟨23910960696150554367705035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15940640464100369578470023 23910960696150554367705035)
          ·
            refine ⟨35866441044225831551557553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23910960696150554367705035 35866441044225831551557553)
            ·
              refine ⟨26899830783169373663668165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35866441044225831551557553 26899830783169373663668165)
              ·
                refine ⟨5043718271844257561937781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26899830783169373663668165 5043718271844257561937781)
                ·
                  refine ⟨472848587985399146431667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5043718271844257561937781 472848587985399146431667)
                  ·
                    rfl

theorem cell22_4143912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_4143912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143912 prefixEnd_4143912 := by exact prefixLift 4143912
  have htrace : WordTrace (prefixWord ++ tailWord_4143912) baseStart_4143912 baseEnd_4143912 := by
    simpa [prefixWord, tailWord_4143912, baseEnd_4143912] using wordTrace_append hprefix tailTrace_4143912
  have hstable : (prefixWord ++ tailWord_4143912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143912).length < 2 ^ (prefixWord ++ tailWord_4143912).sum := by decide
  have hdescent : baseEnd_4143912 < baseStart_4143912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143916 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_4143916 : Nat := 118140960795 + 4143916 * 2 ^ 59
def prefixEnd_4143916 : Nat := 4983230072969 + 3 ^ 40 * 4143916 * 2
def baseEnd_4143916 : Nat := 1418547133237942762194989

theorem tailTrace_4143916 : CollatzResearch.WordTrace tailWord_4143916 prefixEnd_4143916 1418547133237942762194989 := by
  unfold tailWord_4143916
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570516627653765676541801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100760688836871687568722401 75570516627653765676541801)
  ·
    refine ⟨56677887470740324257406351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75570516627653765676541801 56677887470740324257406351)
    ·
      refine ⟨85016831206110486386109527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56677887470740324257406351 85016831206110486386109527)
      ·
        refine ⟨127525246809165729579164291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85016831206110486386109527 127525246809165729579164291)
        ·
          refine ⟨191287870213748594368746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127525246809165729579164291 191287870213748594368746437)
          ·
            refine ⟨35866475665077861444139957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191287870213748594368746437 35866475665077861444139957)
            ·
              refine ⟨3362482093601049510388121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35866475665077861444139957 3362482093601049510388121)
              ·
                refine ⟨2521861570200787132791091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362482093601049510388121 2521861570200787132791091)
                ·
                  refine ⟨3782792355301180699186637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521861570200787132791091 3782792355301180699186637)
                  ·
                    refine ⟨1418547133237942762194989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782792355301180699186637 1418547133237942762194989)
                    ·
                      rfl

theorem cell22_4143916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_4143916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143916 prefixEnd_4143916 := by exact prefixLift 4143916
  have htrace : WordTrace (prefixWord ++ tailWord_4143916) baseStart_4143916 baseEnd_4143916 := by
    simpa [prefixWord, tailWord_4143916, baseEnd_4143916] using wordTrace_append hprefix tailTrace_4143916
  have hstable : (prefixWord ++ tailWord_4143916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143916).length < 2 ^ (prefixWord ++ tailWord_4143916).sum := by decide
  have hdescent : baseEnd_4143916 < baseStart_4143916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4143989 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4143989 : Nat := 118140960795 + 4143989 * 2 ^ 59
def prefixEnd_4143989 : Nat := 4983230072969 + 3 ^ 40 * 4143989 * 2
def baseEnd_4143989 : Nat := 1418572122629794905119765

theorem tailTrace_4143989 : CollatzResearch.WordTrace tailWord_4143989 prefixEnd_4143989 1418572122629794905119765 := by
  unfold tailWord_4143989
  simp only [CollatzResearch.WordTrace]
  refine ⟨151143695784043064820491021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100762463856028709880327347 151143695784043064820491021)
  ·
    refine ⟨56678885919016149307684133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151143695784043064820491021 56678885919016149307684133)
    ·
      refine ⟨10627291109815527995190775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56678885919016149307684133 10627291109815527995190775)
      ·
        refine ⟨15940936664723291992786163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627291109815527995190775 15940936664723291992786163)
        ·
          refine ⟨23911404997084937989179245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15940936664723291992786163 23911404997084937989179245)
          ·
            refine ⟨8966776873906851745942217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23911404997084937989179245 8966776873906851745942217)
            ·
              refine ⟨6725082655430138809456663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966776873906851745942217 6725082655430138809456663)
              ·
                refine ⟨10087623983145208214184995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725082655430138809456663 10087623983145208214184995)
                ·
                  refine ⟨15131435974717812321277493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087623983145208214184995 15131435974717812321277493)
                  ·
                    refine ⟨1418572122629794905119765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15131435974717812321277493 1418572122629794905119765)
                    ·
                      rfl

theorem cell22_4143989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4143989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4143989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4143989 prefixEnd_4143989 := by exact prefixLift 4143989
  have htrace : WordTrace (prefixWord ++ tailWord_4143989) baseStart_4143989 baseEnd_4143989 := by
    simpa [prefixWord, tailWord_4143989, baseEnd_4143989] using wordTrace_append hprefix tailTrace_4143989
  have hstable : (prefixWord ++ tailWord_4143989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4143989).length < 2 ^ (prefixWord ++ tailWord_4143989).sum := by decide
  have hdescent : baseEnd_4143989 < baseStart_4143989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4143989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144000 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_4144000 : Nat := 118140960795 + 4144000 * 2 ^ 59
def prefixEnd_4144000 : Nat := 4983230072969 + 3 ^ 40 * 4144000 * 2
def baseEnd_4144000 : Nat := 1418575888154594543094731

theorem tailTrace_4144000 : CollatzResearch.WordTrace tailWord_4144000 prefixEnd_4144000 1418575888154594543094731 := by
  unfold tailWord_4144000
  simp only [CollatzResearch.WordTrace]
  refine ⟨75572048493501606849570727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100762731324668809132760969 75572048493501606849570727)
  ·
    refine ⟨113358072740252410274356091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75572048493501606849570727 113358072740252410274356091)
    ·
      refine ⟨170037109110378615411534137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113358072740252410274356091 170037109110378615411534137)
      ·
        refine ⟨127527831832783961558650603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170037109110378615411534137 127527831832783961558650603)
        ·
          refine ⟨191291747749175942337975905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127527831832783961558650603 191291747749175942337975905)
          ·
            refine ⟨143468810811881956753481929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191291747749175942337975905 143468810811881956753481929)
            ·
              refine ⟨107601608108911467565111447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143468810811881956753481929 107601608108911467565111447)
              ·
                refine ⟨161402412163367201347667171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107601608108911467565111447 161402412163367201347667171)
                ·
                  refine ⟨242103618245050802021500757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161402412163367201347667171 242103618245050802021500757)
                  ·
                    refine ⟨1418575888154594543094731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 242103618245050802021500757 1418575888154594543094731)
                    ·
                      rfl

theorem cell22_4144000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_4144000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144000 prefixEnd_4144000 := by exact prefixLift 4144000
  have htrace : WordTrace (prefixWord ++ tailWord_4144000) baseStart_4144000 baseEnd_4144000 := by
    simpa [prefixWord, tailWord_4144000, baseEnd_4144000] using wordTrace_append hprefix tailTrace_4144000
  have hstable : (prefixWord ++ tailWord_4144000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144000).length < 2 ^ (prefixWord ++ tailWord_4144000).sum := by decide
  have hdescent : baseEnd_4144000 < baseStart_4144000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144017 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_4144017 : Nat := 118140960795 + 4144017 * 2 ^ 59
def prefixEnd_4144017 : Nat := 4983230072969 + 3 ^ 40 * 4144017 * 2
def baseEnd_4144017 : Nat := 1418581707602012165419679

theorem tailTrace_4144017 : CollatzResearch.WordTrace tailWord_4144017 prefixEnd_4144017 1418581707602012165419679 := by
  unfold tailWord_4144017
  simp only [CollatzResearch.WordTrace]
  refine ⟨151144717027941625602510305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100763144685294417068340203 151144717027941625602510305)
  ·
    refine ⟨113358537770956219201882729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151144717027941625602510305 113358537770956219201882729)
    ·
      refine ⟨85018903328217164401412047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113358537770956219201882729 85018903328217164401412047)
      ·
        refine ⟨127528354992325746602118071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85018903328217164401412047 127528354992325746602118071)
        ·
          refine ⟨191292532488488619903177107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127528354992325746602118071 191292532488488619903177107)
          ·
            refine ⟨286938798732732929854765661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191292532488488619903177107 286938798732732929854765661)
            ·
              refine ⟨107602049524774848695537123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286938798732732929854765661 107602049524774848695537123)
              ·
                refine ⟨161403074287162273043305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107602049524774848695537123 161403074287162273043305685)
                ·
                  refine ⟨3782884553605365774452477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161403074287162273043305685 3782884553605365774452477)
                  ·
                    refine ⟨1418581707602012165419679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782884553605365774452477 1418581707602012165419679)
                    ·
                      rfl

theorem cell22_4144017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_4144017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144017 prefixEnd_4144017 := by exact prefixLift 4144017
  have htrace : WordTrace (prefixWord ++ tailWord_4144017) baseStart_4144017 baseEnd_4144017 := by
    simpa [prefixWord, tailWord_4144017, baseEnd_4144017] using wordTrace_append hprefix tailTrace_4144017
  have hstable : (prefixWord ++ tailWord_4144017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144017).length < 2 ^ (prefixWord ++ tailWord_4144017).sum := by decide
  have hdescent : baseEnd_4144017 < baseStart_4144017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144070 : List Nat := [6, 1, 3, 1, 1, 2, 8]
def baseStart_4144070 : Nat := 118140960795 + 4144070 * 2 ^ 59
def prefixEnd_4144070 : Nat := 4983230072969 + 3 ^ 40 * 4144070 * 2
def baseEnd_4144070 : Nat := 52540735206856951623871

theorem tailTrace_4144070 : CollatzResearch.WordTrace tailWord_4144070 prefixEnd_4144070 52540735206856951623871 := by
  unfold tailWord_4144070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723332815523425489193427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100764433397833077102793109 4723332815523425489193427)
  ·
    refine ⟨7084999223285138233790141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723332815523425489193427 7084999223285138233790141)
    ·
      refine ⟨2656874708731926837671303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7084999223285138233790141 2656874708731926837671303)
      ·
        refine ⟨3985312063097890256506955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656874708731926837671303 3985312063097890256506955)
        ·
          refine ⟨5977968094646835384760433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985312063097890256506955 5977968094646835384760433)
          ·
            refine ⟨4483476070985126538570325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5977968094646835384760433 4483476070985126538570325)
            ·
              refine ⟨52540735206856951623871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4483476070985126538570325 52540735206856951623871)
              ·
                rfl

theorem cell22_4144070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 8].length) (baseStart_4144070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144070 prefixEnd_4144070 := by exact prefixLift 4144070
  have htrace : WordTrace (prefixWord ++ tailWord_4144070) baseStart_4144070 baseEnd_4144070 := by
    simpa [prefixWord, tailWord_4144070, baseEnd_4144070] using wordTrace_append hprefix tailTrace_4144070
  have hstable : (prefixWord ++ tailWord_4144070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144070).length < 2 ^ (prefixWord ++ tailWord_4144070).sum := by decide
  have hdescent : baseEnd_4144070 < baseStart_4144070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144085 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_4144085 : Nat := 118140960795 + 4144085 * 2 ^ 59
def prefixEnd_4144085 : Nat := 4983230072969 + 3 ^ 40 * 4144085 * 2
def baseEnd_4144085 : Nat := 1418604985391682654719471

theorem tailTrace_4144085 : CollatzResearch.WordTrace tailWord_4144085 prefixEnd_4144085 1418604985391682654719471 := by
  unfold tailWord_4144085
  simp only [CollatzResearch.WordTrace]
  refine ⟨151147197191695273215985709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100764798127796848810657139 151147197191695273215985709)
  ·
    refine ⟨56680198946885727455994641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151147197191695273215985709 56680198946885727455994641)
    ·
      refine ⟨42510149210164295591995981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56680198946885727455994641 42510149210164295591995981)
      ·
        refine ⟨15941305953811610846998493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42510149210164295591995981 15941305953811610846998493)
        ·
          refine ⟨5977989732679354067624435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15941305953811610846998493 5977989732679354067624435)
          ·
            refine ⟨8966984599019031101436653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977989732679354067624435 8966984599019031101436653)
            ·
              refine ⟨3362619224632136663038745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966984599019031101436653 3362619224632136663038745)
              ·
                refine ⟨2521964418474102497279059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362619224632136663038745 2521964418474102497279059)
                ·
                  refine ⟨3782946627711153745918589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521964418474102497279059 3782946627711153745918589)
                  ·
                    refine ⟨1418604985391682654719471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3782946627711153745918589 1418604985391682654719471)
                    ·
                      rfl

theorem cell22_4144085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_4144085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144085 prefixEnd_4144085 := by exact prefixLift 4144085
  have htrace : WordTrace (prefixWord ++ tailWord_4144085) baseStart_4144085 baseEnd_4144085 := by
    simpa [prefixWord, tailWord_4144085, baseEnd_4144085] using wordTrace_append hprefix tailTrace_4144085
  have hstable : (prefixWord ++ tailWord_4144085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144085).length < 2 ^ (prefixWord ++ tailWord_4144085).sum := by decide
  have hdescent : baseEnd_4144085 < baseStart_4144085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144098 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4144098 : Nat := 118140960795 + 4144098 * 2 ^ 59
def prefixEnd_4144098 : Nat := 4983230072969 + 3 ^ 40 * 4144098 * 2
def baseEnd_4144098 : Nat := 472869811852451651381477

theorem tailTrace_4144098 : CollatzResearch.WordTrace tailWord_4144098 prefixEnd_4144098 472869811852451651381477 := by
  unfold tailWord_4144098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786917835162044109052237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100765114227098784290805965 37786917835162044109052237)
  ·
    refine ⟨14170094188185766540894589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37786917835162044109052237 14170094188185766540894589)
    ·
      refine ⟨5313785320569662452835471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14170094188185766540894589 5313785320569662452835471)
      ·
        refine ⟨7970677980854493679253207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313785320569662452835471 7970677980854493679253207)
        ·
          refine ⟨11956016971281740518879811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970677980854493679253207 11956016971281740518879811)
          ·
            refine ⟨17934025456922610778319717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956016971281740518879811 17934025456922610778319717)
            ·
              refine ⟨3362629773172989520934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17934025456922610778319717 3362629773172989520934947)
              ·
                refine ⟨5043944659759484281402421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362629773172989520934947 5043944659759484281402421)
                ·
                  refine ⟨472869811852451651381477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5043944659759484281402421 472869811852451651381477)
                  ·
                    rfl

theorem cell22_4144098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4144098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144098 prefixEnd_4144098 := by exact prefixLift 4144098
  have htrace : WordTrace (prefixWord ++ tailWord_4144098) baseStart_4144098 baseEnd_4144098 := by
    simpa [prefixWord, tailWord_4144098, baseEnd_4144098] using wordTrace_append hprefix tailTrace_4144098
  have hstable : (prefixWord ++ tailWord_4144098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144098).length < 2 ^ (prefixWord ++ tailWord_4144098).sum := by decide
  have hdescent : baseEnd_4144098 < baseStart_4144098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144111 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 1, 4]
def baseStart_4144111 : Nat := 118140960795 + 4144111 * 2 ^ 59
def prefixEnd_4144111 : Nat := 4983230072969 + 3 ^ 40 * 4144111 * 2
def baseEnd_4144111 : Nat := 1418613885723027253569391

theorem tailTrace_4144111 : CollatzResearch.WordTrace tailWord_4144111 prefixEnd_4144111 1418613885723027253569391 := by
  unfold tailWord_4144111
  simp only [CollatzResearch.WordTrace]
  refine ⟨151148145489601079656432187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100765430326400719770954791 151148145489601079656432187)
  ·
    refine ⟨226722218234401619484648281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151148145489601079656432187 226722218234401619484648281)
    ·
      refine ⟨170041663675801214613486211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226722218234401619484648281 170041663675801214613486211)
      ·
        refine ⟨255062495513701821920229317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170041663675801214613486211 255062495513701821920229317)
        ·
          refine ⟨47824217908819091610042997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255062495513701821920229317 47824217908819091610042997)
          ·
            refine ⟨4483520428951789838441531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47824217908819091610042997 4483520428951789838441531)
            ·
              refine ⟨6725280643427684757662297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483520428951789838441531 6725280643427684757662297)
              ·
                refine ⟨5043960482570763568246723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725280643427684757662297 5043960482570763568246723)
                ·
                  refine ⟨7565940723856145352370085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043960482570763568246723 7565940723856145352370085)
                  ·
                    refine ⟨1418613885723027253569391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565940723856145352370085 1418613885723027253569391)
                    ·
                      rfl

theorem cell22_4144111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_4144111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144111 prefixEnd_4144111 := by exact prefixLift 4144111
  have htrace : WordTrace (prefixWord ++ tailWord_4144111) baseStart_4144111 baseEnd_4144111 := by
    simpa [prefixWord, tailWord_4144111, baseEnd_4144111] using wordTrace_append hprefix tailTrace_4144111
  have hstable : (prefixWord ++ tailWord_4144111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144111).length < 2 ^ (prefixWord ++ tailWord_4144111).sum := by decide
  have hdescent : baseEnd_4144111 < baseStart_4144111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144122 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_4144122 : Nat := 118140960795 + 4144122 * 2 ^ 59
def prefixEnd_4144122 : Nat := 4983230072969 + 3 ^ 40 * 4144122 * 2
def baseEnd_4144122 : Nat := 1418617651247826891544357

theorem tailTrace_4144122 : CollatzResearch.WordTrace tailWord_4144122 prefixEnd_4144122 1418617651247826891544357 := by
  unfold tailWord_4144122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37787136673140307133770655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100765697795040819023388413 37787136673140307133770655)
  ·
    refine ⟨56680705009710460700655983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37787136673140307133770655 56680705009710460700655983)
    ·
      refine ⟨85021057514565691050983975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56680705009710460700655983 85021057514565691050983975)
      ·
        refine ⟨127531586271848536576475963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85021057514565691050983975 127531586271848536576475963)
        ·
          refine ⟨191297379407772804864713945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127531586271848536576475963 191297379407772804864713945)
          ·
            refine ⟨143473034555829603648535459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191297379407772804864713945 143473034555829603648535459)
            ·
              refine ⟨215209551833744405472803189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143473034555829603648535459 215209551833744405472803189)
              ·
                refine ⟨20175895484413538013075299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215209551833744405472803189 20175895484413538013075299)
                ·
                  refine ⟨30263843226620307019612949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20175895484413538013075299 30263843226620307019612949)
                  ·
                    refine ⟨1418617651247826891544357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30263843226620307019612949 1418617651247826891544357)
                    ·
                      rfl

theorem cell22_4144122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_4144122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144122 prefixEnd_4144122 := by exact prefixLift 4144122
  have htrace : WordTrace (prefixWord ++ tailWord_4144122) baseStart_4144122 baseEnd_4144122 := by
    simpa [prefixWord, tailWord_4144122, baseEnd_4144122] using wordTrace_append hprefix tailTrace_4144122
  have hstable : (prefixWord ++ tailWord_4144122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144122).length < 2 ^ (prefixWord ++ tailWord_4144122).sum := by decide
  have hdescent : baseEnd_4144122 < baseStart_4144122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144124 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4144124 : Nat := 118140960795 + 4144124 * 2 ^ 59
def prefixEnd_4144124 : Nat := 4983230072969 + 3 ^ 40 * 4144124 * 2
def baseEnd_4144124 : Nat := 1418618335888699552994351

theorem tailTrace_4144124 : CollatzResearch.WordTrace tailWord_4144124 prefixEnd_4144124 1418618335888699552994351 := by
  unfold tailWord_4144124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75574309819276991438327713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100765746425702655251103617 75574309819276991438327713)
  ·
    refine ⟨56680732364457743578745785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75574309819276991438327713 56680732364457743578745785)
    ·
      refine ⟨42510549273343307684059339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56680732364457743578745785 42510549273343307684059339)
      ·
        refine ⟨63765823910014961526089009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42510549273343307684059339 63765823910014961526089009)
        ·
          refine ⟨47824367932511221144566757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63765823910014961526089009 47824367932511221144566757)
          ·
            refine ⟨8967068987345853964606267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47824367932511221144566757 8967068987345853964606267)
            ·
              refine ⟨13450603481018780946909401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967068987345853964606267 13450603481018780946909401)
              ·
                refine ⟨10087952610764085710182051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13450603481018780946909401 10087952610764085710182051)
                ·
                  refine ⟨15131928916146128565273077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087952610764085710182051 15131928916146128565273077)
                  ·
                    refine ⟨1418618335888699552994351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15131928916146128565273077 1418618335888699552994351)
                    ·
                      rfl

theorem cell22_4144124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4144124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144124 prefixEnd_4144124 := by exact prefixLift 4144124
  have htrace : WordTrace (prefixWord ++ tailWord_4144124) baseStart_4144124 baseEnd_4144124 := by
    simpa [prefixWord, tailWord_4144124, baseEnd_4144124] using wordTrace_append hprefix tailTrace_4144124
  have hstable : (prefixWord ++ tailWord_4144124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144124).length < 2 ^ (prefixWord ++ tailWord_4144124).sum := by decide
  have hdescent : baseEnd_4144124 < baseStart_4144124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144139 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_4144139 : Nat := 118140960795 + 4144139 * 2 ^ 59
def prefixEnd_4144139 : Nat := 4983230072969 + 3 ^ 40 * 4144139 * 2
def baseEnd_4144139 : Nat := 1418623470695244513869305

theorem tailTrace_4144139 : CollatzResearch.WordTrace tailWord_4144139 prefixEnd_4144139 1418623470695244513869305 := by
  unfold tailWord_4144139
  simp only [CollatzResearch.WordTrace]
  refine ⟨151149166733499640438451471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100766111155666426958967647 151149166733499640438451471)
  ·
    refine ⟨226723750100249460657677207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151149166733499640438451471 226723750100249460657677207)
    ·
      refine ⟨340085625150374190986515811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226723750100249460657677207 340085625150374190986515811)
      ·
        refine ⟨510128437725561286479773717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340085625150374190986515811 510128437725561286479773717)
        ·
          refine ⟨23912270518385685303739393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510128437725561286479773717 23912270518385685303739393)
          ·
            refine ⟨17934202888789263977804545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23912270518385685303739393 17934202888789263977804545)
            ·
              refine ⟨13450652166591947983353409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17934202888789263977804545 13450652166591947983353409)
              ·
                refine ⟨10087989124943960987515057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13450652166591947983353409 10087989124943960987515057)
                ·
                  refine ⟨7565991843707970740636293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10087989124943960987515057 7565991843707970740636293)
                  ·
                    refine ⟨1418623470695244513869305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565991843707970740636293 1418623470695244513869305)
                    ·
                      rfl

theorem cell22_4144139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_4144139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144139 prefixEnd_4144139 := by exact prefixLift 4144139
  have htrace : WordTrace (prefixWord ++ tailWord_4144139) baseStart_4144139 baseEnd_4144139 := by
    simpa [prefixWord, tailWord_4144139, baseEnd_4144139] using wordTrace_append hprefix tailTrace_4144139
  have hstable : (prefixWord ++ tailWord_4144139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144139).length < 2 ^ (prefixWord ++ tailWord_4144139).sum := by decide
  have hdescent : baseEnd_4144139 < baseStart_4144139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144199 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 7]
def baseStart_4144199 : Nat := 118140960795 + 4144199 * 2 ^ 59
def prefixEnd_4144199 : Nat := 4983230072969 + 3 ^ 40 * 4144199 * 2
def baseEnd_4144199 : Nat := 472881336640474785789707

theorem tailTrace_4144199 : CollatzResearch.WordTrace tailWord_4144199 prefixEnd_4144199 472881336640474785789707 := by
  unfold tailWord_4144199
  simp only [CollatzResearch.WordTrace]
  refine ⟨151151355113282270685635651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100767570075521513790423767 151151355113282270685635651)
  ·
    refine ⟨226727032669923406028453477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151151355113282270685635651 226727032669923406028453477)
    ·
      refine ⟨42511318625610638630335027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226727032669923406028453477 42511318625610638630335027)
      ·
        refine ⟨63766977938415957945502541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42511318625610638630335027 63766977938415957945502541)
        ·
          refine ⟨23912616726905984229563453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63766977938415957945502541 23912616726905984229563453)
          ·
            refine ⟨8967231272589744086086295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23912616726905984229563453 8967231272589744086086295)
            ·
              refine ⟨13450846908884616129129443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967231272589744086086295 13450846908884616129129443)
              ·
                refine ⟨20176270363326924193694165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450846908884616129129443 20176270363326924193694165)
                ·
                  refine ⟨472881336640474785789707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20176270363326924193694165 472881336640474785789707)
                  ·
                    rfl

theorem cell22_4144199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_4144199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144199 prefixEnd_4144199 := by exact prefixLift 4144199
  have htrace : WordTrace (prefixWord ++ tailWord_4144199) baseStart_4144199 baseEnd_4144199 := by
    simpa [prefixWord, tailWord_4144199, baseEnd_4144199] using wordTrace_append hprefix tailTrace_4144199
  have hstable : (prefixWord ++ tailWord_4144199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144199).length < 2 ^ (prefixWord ++ tailWord_4144199).sum := by decide
  have hdescent : baseEnd_4144199 < baseStart_4144199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144216 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_4144216 : Nat := 118140960795 + 4144216 * 2 ^ 59
def prefixEnd_4144216 : Nat := 4983230072969 + 3 ^ 40 * 4144216 * 2
def baseEnd_4144216 : Nat := 472883276456280659898023

theorem tailTrace_4144216 : CollatzResearch.WordTrace tailWord_4144216 prefixEnd_4144216 472883276456280659898023 := by
  unfold tailWord_4144216
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575987577110341294502251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100767983436147121726003001 75575987577110341294502251)
  ·
    refine ⟨113363981365665511941753377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75575987577110341294502251 113363981365665511941753377)
    ·
      refine ⟨85022986024249133956315033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113363981365665511941753377 85022986024249133956315033)
      ·
        refine ⟨63767239518186850467236275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85022986024249133956315033 63767239518186850467236275)
        ·
          refine ⟨95650859277280275700854413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63767239518186850467236275 95650859277280275700854413)
          ·
            refine ⟨35869072228980103387820405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95650859277280275700854413 35869072228980103387820405)
            ·
              refine ⟨3362725521466884692608163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35869072228980103387820405 3362725521466884692608163)
              ·
                refine ⟨5044088282200327038912245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362725521466884692608163 5044088282200327038912245)
                ·
                  refine ⟨472883276456280659898023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044088282200327038912245 472883276456280659898023)
                  ·
                    rfl

theorem cell22_4144216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_4144216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144216 prefixEnd_4144216 := by exact prefixLift 4144216
  have htrace : WordTrace (prefixWord ++ tailWord_4144216) baseStart_4144216 baseEnd_4144216 := by
    simpa [prefixWord, tailWord_4144216, baseEnd_4144216] using wordTrace_append hprefix tailTrace_4144216
  have hstable : (prefixWord ++ tailWord_4144216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144216).length < 2 ^ (prefixWord ++ tailWord_4144216).sum := by decide
  have hdescent : baseEnd_4144216 < baseStart_4144216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144254 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4144254 : Nat := 118140960795 + 4144254 * 2 ^ 59
def prefixEnd_4144254 : Nat := 4983230072969 + 3 ^ 40 * 4144254 * 2
def baseEnd_4144254 : Nat := 1418662837545422547243953

theorem tailTrace_4144254 : CollatzResearch.WordTrace tailWord_4144254 prefixEnd_4144254 1418662837545422547243953 := by
  unfold tailWord_4144254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894170141010376884860977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100768907418722010052591877 18894170141010376884860977)
  ·
    refine ⟨14170627605757782663645733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18894170141010376884860977 14170627605757782663645733)
    ·
      refine ⟨2656992676079584249433575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14170627605757782663645733 2656992676079584249433575)
      ·
        refine ⟨3985489014119376374150363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656992676079584249433575 3985489014119376374150363)
        ·
          refine ⟨5978233521179064561225545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985489014119376374150363 5978233521179064561225545)
          ·
            refine ⟨4483675140884298420919159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978233521179064561225545 4483675140884298420919159)
            ·
              refine ⟨6725512711326447631378739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483675140884298420919159 6725512711326447631378739)
              ·
                refine ⟨10088269066989671447068109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725512711326447631378739 10088269066989671447068109)
                ·
                  refine ⟨3783100900121126792650541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10088269066989671447068109 3783100900121126792650541)
                  ·
                    refine ⟨1418662837545422547243953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783100900121126792650541 1418662837545422547243953)
                    ·
                      rfl

theorem cell22_4144254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4144254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144254 prefixEnd_4144254 := by exact prefixLift 4144254
  have htrace : WordTrace (prefixWord ++ tailWord_4144254) baseStart_4144254 baseEnd_4144254 := by
    simpa [prefixWord, tailWord_4144254, baseEnd_4144254] using wordTrace_append hprefix tailTrace_4144254
  have hstable : (prefixWord ++ tailWord_4144254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144254).length < 2 ^ (prefixWord ++ tailWord_4144254).sum := by decide
  have hdescent : baseEnd_4144254 < baseStart_4144254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144289 : List Nat := [1, 2, 3, 3, 1, 1, 1, 10]
def baseStart_4144289 : Nat := 118140960795 + 4144289 * 2 ^ 59
def prefixEnd_4144289 : Nat := 4983230072969 + 3 ^ 40 * 4144289 * 2
def baseEnd_4144289 : Nat := 157630535417854902513205

theorem tailTrace_4144289 : CollatzResearch.WordTrace tailWord_4144289 prefixEnd_4144289 157630535417854902513205 := by
  unfold tailWord_4144289
  simp only [CollatzResearch.WordTrace]
  refine ⟨151154637682956216056411921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100769758455304144037607947 151154637682956216056411921)
  ·
    refine ⟨113365978262217162042308941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151154637682956216056411921 113365978262217162042308941)
    ·
      refine ⟨42512241848331435765865853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113365978262217162042308941 42512241848331435765865853)
      ·
        refine ⟨15942090693124288412199695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42512241848331435765865853 15942090693124288412199695)
        ·
          refine ⟨23913136039686432618299543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942090693124288412199695 23913136039686432618299543)
          ·
            refine ⟨35869704059529648927449315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913136039686432618299543 35869704059529648927449315)
            ·
              refine ⟨53804556089294473391173973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35869704059529648927449315 53804556089294473391173973)
              ·
                refine ⟨157630535417854902513205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53804556089294473391173973 157630535417854902513205)
                ·
                  rfl

theorem cell22_4144289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 10].length) (baseStart_4144289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144289 prefixEnd_4144289 := by exact prefixLift 4144289
  have htrace : WordTrace (prefixWord ++ tailWord_4144289) baseStart_4144289 baseEnd_4144289 := by
    simpa [prefixWord, tailWord_4144289, baseEnd_4144289] using wordTrace_append hprefix tailTrace_4144289
  have hstable : (prefixWord ++ tailWord_4144289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144289).length < 2 ^ (prefixWord ++ tailWord_4144289).sum := by decide
  have hdescent : baseEnd_4144289 < baseStart_4144289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144319 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_4144319 : Nat := 118140960795 + 4144319 * 2 ^ 59
def prefixEnd_4144319 : Nat := 4983230072969 + 3 ^ 40 * 4144319 * 2
def baseEnd_4144319 : Nat := 1418685088373784044368753

theorem tailTrace_4144319 : CollatzResearch.WordTrace tailWord_4144319 prefixEnd_4144319 1418685088373784044368753 := by
  unfold tailWord_4144319
  simp only [CollatzResearch.WordTrace]
  refine ⟨151155731872847531180004011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100770487915231687453336007 151155731872847531180004011)
  ·
    refine ⟨226733597809271296770006017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151155731872847531180004011 226733597809271296770006017)
    ·
      refine ⟨170050198356953472577504513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226733597809271296770006017 170050198356953472577504513)
      ·
        refine ⟨127537648767715104433128385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170050198356953472577504513 127537648767715104433128385)
        ·
          refine ⟨95653236575786328324846289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127537648767715104433128385 95653236575786328324846289)
          ·
            refine ⟨71739927431839746243634717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95653236575786328324846289 71739927431839746243634717)
            ·
              refine ⟨26902472786939904841363019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71739927431839746243634717 26902472786939904841363019)
              ·
                refine ⟨40353709180409857262044529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26902472786939904841363019 40353709180409857262044529)
                ·
                  refine ⟨30265281885307392946533397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40353709180409857262044529 30265281885307392946533397)
                  ·
                    refine ⟨1418685088373784044368753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30265281885307392946533397 1418685088373784044368753)
                    ·
                      rfl

theorem cell22_4144319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_4144319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144319 prefixEnd_4144319 := by exact prefixLift 4144319
  have htrace : WordTrace (prefixWord ++ tailWord_4144319) baseStart_4144319 baseEnd_4144319 := by
    simpa [prefixWord, tailWord_4144319, baseEnd_4144319] using wordTrace_append hprefix tailTrace_4144319
  have hstable : (prefixWord ++ tailWord_4144319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144319).length < 2 ^ (prefixWord ++ tailWord_4144319).sum := by decide
  have hdescent : baseEnd_4144319 < baseStart_4144319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144338 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_4144338 : Nat := 118140960795 + 4144338 * 2 ^ 59
def prefixEnd_4144338 : Nat := 4983230072969 + 3 ^ 40 * 4144338 * 2
def baseEnd_4144338 : Nat := 1418691592462074328143695

theorem tailTrace_4144338 : CollatzResearch.WordTrace tailWord_4144338 prefixEnd_4144338 1418691592462074328143695 := by
  unfold tailWord_4144338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37789106214944674356236417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100770949906519131616630445 37789106214944674356236417)
  ·
    refine ⟨28341829661208505767177313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37789106214944674356236417 28341829661208505767177313)
    ·
      refine ⟨21256372245906379325382985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28341829661208505767177313 21256372245906379325382985)
      ·
        refine ⟨15942279184429784494037239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21256372245906379325382985 15942279184429784494037239)
        ·
          refine ⟨23913418776644676741055859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942279184429784494037239 23913418776644676741055859)
          ·
            refine ⟨35870128164967015111583789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913418776644676741055859 35870128164967015111583789)
            ·
              refine ⟨13451298061862630666843921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35870128164967015111583789 13451298061862630666843921)
              ·
                refine ⟨10088473546396973000132941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451298061862630666843921 10088473546396973000132941)
                ·
                  refine ⟨3783177579898864875049853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10088473546396973000132941 3783177579898864875049853)
                  ·
                    refine ⟨1418691592462074328143695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783177579898864875049853 1418691592462074328143695)
                    ·
                      rfl

theorem cell22_4144338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_4144338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144338 prefixEnd_4144338 := by exact prefixLift 4144338
  have htrace : WordTrace (prefixWord ++ tailWord_4144338) baseStart_4144338 baseEnd_4144338 := by
    simpa [prefixWord, tailWord_4144338, baseEnd_4144338] using wordTrace_append hprefix tailTrace_4144338
  have hstable : (prefixWord ++ tailWord_4144338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144338).length < 2 ^ (prefixWord ++ tailWord_4144338).sum := by decide
  have hdescent : baseEnd_4144338 < baseStart_4144338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144340 : List Nat := [2, 4, 1, 4, 1, 1, 3, 6]
def baseStart_4144340 : Nat := 118140960795 + 4144340 * 2 ^ 59
def prefixEnd_4144340 : Nat := 4983230072969 + 3 ^ 40 * 4144340 * 2
def baseEnd_4144340 : Nat := 157632475233660776621521

theorem tailTrace_4144340 : CollatzResearch.WordTrace tailWord_4144340 prefixEnd_4144340 157632475233660776621521 := by
  unfold tailWord_4144340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75578248902885725883259237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100770998537180967844345649 75578248902885725883259237)
  ·
    refine ⟨14170921669291073603111107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75578248902885725883259237 14170921669291073603111107)
    ·
      refine ⟨21256382503936610404666661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170921669291073603111107 21256382503936610404666661)
      ·
        refine ⟨3985571719488114450874999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21256382503936610404666661 3985571719488114450874999)
        ·
          refine ⟨5978357579232171676312499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985571719488114450874999 5978357579232171676312499)
          ·
            refine ⟨8967536368848257514468749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978357579232171676312499 8967536368848257514468749)
            ·
              refine ⟨3362826138318096567925781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8967536368848257514468749 3362826138318096567925781)
              ·
                refine ⟨157632475233660776621521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3362826138318096567925781 157632475233660776621521)
                ·
                  rfl

theorem cell22_4144340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_4144340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144340 prefixEnd_4144340 := by exact prefixLift 4144340
  have htrace : WordTrace (prefixWord ++ tailWord_4144340) baseStart_4144340 baseEnd_4144340 := by
    simpa [prefixWord, tailWord_4144340, baseEnd_4144340] using wordTrace_append hprefix tailTrace_4144340
  have hstable : (prefixWord ++ tailWord_4144340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144340).length < 2 ^ (prefixWord ++ tailWord_4144340).sum := by decide
  have hdescent : baseEnd_4144340 < baseStart_4144340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144342 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4144342 : Nat := 118140960795 + 4144342 * 2 ^ 59
def prefixEnd_4144342 : Nat := 4983230072969 + 3 ^ 40 * 4144342 * 2
def baseEnd_4144342 : Nat := 1418692961743819651043683

theorem tailTrace_4144342 : CollatzResearch.WordTrace tailWord_4144342 prefixEnd_4144342 1418692961743819651043683 := by
  unfold tailWord_4144342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447285671985262881755705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100771047167842804072060853 9447285671985262881755705)
  ·
    refine ⟨7085464253988947161316779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9447285671985262881755705 7085464253988947161316779)
    ·
      refine ⟨10628196380983420741975169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085464253988947161316779 10628196380983420741975169)
      ·
        refine ⟨7971147285737565556481377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10628196380983420741975169 7971147285737565556481377)
        ·
          refine ⟨5978360464303174167361033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7971147285737565556481377 5978360464303174167361033)
          ·
            refine ⟨4483770348227380625520775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978360464303174167361033 4483770348227380625520775)
            ·
              refine ⟨6725655522341070938281163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483770348227380625520775 6725655522341070938281163)
              ·
                refine ⟨10088483283511606407421745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725655522341070938281163 10088483283511606407421745)
                ·
                  refine ⟨7566362462633704805566309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10088483283511606407421745 7566362462633704805566309)
                  ·
                    refine ⟨1418692961743819651043683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566362462633704805566309 1418692961743819651043683)
                    ·
                      rfl

theorem cell22_4144342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4144342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144342 prefixEnd_4144342 := by exact prefixLift 4144342
  have htrace : WordTrace (prefixWord ++ tailWord_4144342) baseStart_4144342 baseEnd_4144342 := by
    simpa [prefixWord, tailWord_4144342, baseEnd_4144342] using wordTrace_append hprefix tailTrace_4144342
  have hstable : (prefixWord ++ tailWord_4144342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144342).length < 2 ^ (prefixWord ++ tailWord_4144342).sum := by decide
  have hdescent : baseEnd_4144342 < baseStart_4144342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144366 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4144366 : Nat := 118140960795 + 4144366 * 2 ^ 59
def prefixEnd_4144366 : Nat := 4983230072969 + 3 ^ 40 * 4144366 * 2
def baseEnd_4144366 : Nat := 1418701177434291588443609

theorem tailTrace_4144366 : CollatzResearch.WordTrace tailWord_4144366 prefixEnd_4144366 1418701177434291588443609 := by
  unfold tailWord_4144366
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894680762959657275870619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100771630735784838804643301 18894680762959657275870619)
  ·
    refine ⟨28342021144439485913805929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18894680762959657275870619 28342021144439485913805929)
    ·
      refine ⟨21256515858329614435354447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28342021144439485913805929 21256515858329614435354447)
      ·
        refine ⟨31884773787494421653031671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21256515858329614435354447 31884773787494421653031671)
        ·
          refine ⟨47827160681241632479547507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31884773787494421653031671 47827160681241632479547507)
          ·
            refine ⟨71740741021862448719321261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47827160681241632479547507 71740741021862448719321261)
            ·
              refine ⟨26902777883198418269745473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71740741021862448719321261 26902777883198418269745473)
              ·
                refine ⟨20177083412398813702309105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26902777883198418269745473 20177083412398813702309105)
                ·
                  refine ⟨15132812559299110276731829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20177083412398813702309105 15132812559299110276731829)
                  ·
                    refine ⟨1418701177434291588443609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15132812559299110276731829 1418701177434291588443609)
                    ·
                      rfl

theorem cell22_4144366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4144366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144366 prefixEnd_4144366 := by exact prefixLift 4144366
  have htrace : WordTrace (prefixWord ++ tailWord_4144366) baseStart_4144366 baseEnd_4144366 := by
    simpa [prefixWord, tailWord_4144366, baseEnd_4144366] using wordTrace_append hprefix tailTrace_4144366
  have hstable : (prefixWord ++ tailWord_4144366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144366).length < 2 ^ (prefixWord ++ tailWord_4144366).sum := by decide
  have hdescent : baseEnd_4144366 < baseStart_4144366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144396 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_4144396 : Nat := 118140960795 + 4144396 * 2 ^ 59
def prefixEnd_4144396 : Nat := 4983230072969 + 3 ^ 40 * 4144396 * 2
def baseEnd_4144396 : Nat := 472903815682460503397839

theorem tailTrace_4144396 : CollatzResearch.WordTrace tailWord_4144396 prefixEnd_4144396 472903815682460503397839 := by
  unfold tailWord_4144396
  simp only [CollatzResearch.WordTrace]
  refine ⟨75579270146784286665278521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100772360195712382220371361 75579270146784286665278521)
  ·
    refine ⟨56684452610088214998958891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75579270146784286665278521 56684452610088214998958891)
    ·
      refine ⟨85026678915132322498438337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56684452610088214998958891 85026678915132322498438337)
      ·
        refine ⟨63770009186349241873828753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85026678915132322498438337 63770009186349241873828753)
        ·
          refine ⟨47827506889761931405371565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63770009186349241873828753 47827506889761931405371565)
          ·
            refine ⟨17935315083660724277014337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47827506889761931405371565 17935315083660724277014337)
            ·
              refine ⟨13451486312745543207760753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17935315083660724277014337 13451486312745543207760753)
              ·
                refine ⟨10088614734559157405820565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451486312745543207760753 10088614734559157405820565)
                ·
                  refine ⟨472903815682460503397839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10088614734559157405820565 472903815682460503397839)
                  ·
                    rfl

theorem cell22_4144396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_4144396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144396 prefixEnd_4144396 := by exact prefixLift 4144396
  have htrace : WordTrace (prefixWord ++ tailWord_4144396) baseStart_4144396 baseEnd_4144396 := by
    simpa [prefixWord, tailWord_4144396, baseEnd_4144396] using wordTrace_append hprefix tailTrace_4144396
  have hstable : (prefixWord ++ tailWord_4144396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144396).length < 2 ^ (prefixWord ++ tailWord_4144396).sum := by decide
  have hdescent : baseEnd_4144396 < baseStart_4144396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144398 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_4144398 : Nat := 118140960795 + 4144398 * 2 ^ 59
def prefixEnd_4144398 : Nat := 4983230072969 + 3 ^ 40 * 4144398 * 2
def baseEnd_4144398 : Nat := 1418712131688254171643511

theorem tailTrace_4144398 : CollatzResearch.WordTrace tailWord_4144398 prefixEnd_4144398 1418712131688254171643511 := by
  unfold tailWord_4144398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894826654945165959016231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100772408826374218448086565 18894826654945165959016231)
  ·
    refine ⟨28342239982417748938524347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18894826654945165959016231 28342239982417748938524347)
    ·
      refine ⟨42513359973626623407786521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28342239982417748938524347 42513359973626623407786521)
      ·
        refine ⟨31885019980219967555839891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42513359973626623407786521 31885019980219967555839891)
        ·
          refine ⟨47827529970329951333759837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31885019980219967555839891 47827529970329951333759837)
          ·
            refine ⟨17935323738873731750159939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47827529970329951333759837 17935323738873731750159939)
            ·
              refine ⟨26902985608310597625239909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17935323738873731750159939 26902985608310597625239909)
              ·
                refine ⟨5044309801558237054732483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26902985608310597625239909 5044309801558237054732483)
                ·
                  refine ⟨7566464702337355582098725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044309801558237054732483 7566464702337355582098725)
                  ·
                    refine ⟨1418712131688254171643511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566464702337355582098725 1418712131688254171643511)
                    ·
                      rfl

theorem cell22_4144398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_4144398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144398 prefixEnd_4144398 := by exact prefixLift 4144398
  have htrace : WordTrace (prefixWord ++ tailWord_4144398) baseStart_4144398 baseEnd_4144398 := by
    simpa [prefixWord, tailWord_4144398, baseEnd_4144398] using wordTrace_append hprefix tailTrace_4144398
  have hstable : (prefixWord ++ tailWord_4144398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144398).length < 2 ^ (prefixWord ++ tailWord_4144398).sum := by decide
  have hdescent : baseEnd_4144398 < baseStart_4144398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144428 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_4144428 : Nat := 118140960795 + 4144428 * 2 ^ 59
def prefixEnd_4144428 : Nat := 4983230072969 + 3 ^ 40 * 4144428 * 2
def baseEnd_4144428 : Nat := 1418722401301344093393419

theorem tailTrace_4144428 : CollatzResearch.WordTrace tailWord_4144428 prefixEnd_4144428 1418722401301344093393419 := by
  unfold tailWord_4144428
  simp only [CollatzResearch.WordTrace]
  refine ⟨75579853714726321397860969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100773138286301761863814625 75579853714726321397860969)
  ·
    refine ⟨56684890286044741048395727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75579853714726321397860969 56684890286044741048395727)
    ·
      refine ⟨85027335429067111572593591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56684890286044741048395727 85027335429067111572593591)
      ·
        refine ⟨127541003143600667358890387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85027335429067111572593591 127541003143600667358890387)
        ·
          refine ⟨191311504715401001038335581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127541003143600667358890387 191311504715401001038335581)
          ·
            refine ⟨71741814268275375389375843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191311504715401001038335581 71741814268275375389375843)
            ·
              refine ⟨107612721402413063084063765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71741814268275375389375843 107612721402413063084063765)
              ·
                refine ⟨5044346315738112332065489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107612721402413063084063765 5044346315738112332065489)
                ·
                  refine ⟨3783259736803584249049117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5044346315738112332065489 3783259736803584249049117)
                  ·
                    refine ⟨1418722401301344093393419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783259736803584249049117 1418722401301344093393419)
                    ·
                      rfl

theorem cell22_4144428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_4144428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144428 prefixEnd_4144428 := by exact prefixLift 4144428
  have htrace : WordTrace (prefixWord ++ tailWord_4144428) baseStart_4144428 baseEnd_4144428 := by
    simpa [prefixWord, tailWord_4144428, baseEnd_4144428] using wordTrace_append hprefix tailTrace_4144428
  have hstable : (prefixWord ++ tailWord_4144428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144428).length < 2 ^ (prefixWord ++ tailWord_4144428).sum := by decide
  have hdescent : baseEnd_4144428 < baseStart_4144428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144659 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 1, 3]
def baseStart_4144659 : Nat := 118140960795 + 4144659 * 2 ^ 59
def prefixEnd_4144659 : Nat := 4983230072969 + 3 ^ 40 * 4144659 * 2
def baseEnd_4144659 : Nat := 1418801477322136490867711

theorem tailTrace_4144659 : CollatzResearch.WordTrace tailWord_4144659 prefixEnd_4144659 1418801477322136490867711 := by
  unfold tailWord_4144659
  simp only [CollatzResearch.WordTrace]
  refine ⟨151168132691615769247381031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100778755127743846164920687 151168132691615769247381031)
  ·
    refine ⟨226752199037423653871071547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151168132691615769247381031 226752199037423653871071547)
    ·
      refine ⟨340128298556135480806607321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226752199037423653871071547 340128298556135480806607321)
      ·
        refine ⟨255096223917101610604955491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340128298556135480806607321 255096223917101610604955491)
        ·
          refine ⟨382644335875652415907433237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255096223917101610604955491 382644335875652415907433237)
          ·
            refine ⟨17936453244171206995660933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382644335875652415907433237 17936453244171206995660933)
            ·
              refine ⟨3363084983282101311686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17936453244171206995660933 3363084983282101311686425)
              ·
                refine ⟨2522313737461575983764819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363084983282101311686425 2522313737461575983764819)
                ·
                  refine ⟨3783470606192363975647229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522313737461575983764819 3783470606192363975647229)
                  ·
                    refine ⟨1418801477322136490867711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783470606192363975647229 1418801477322136490867711)
                    ·
                      rfl

theorem cell22_4144659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 1, 3].length) (baseStart_4144659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144659 prefixEnd_4144659 := by exact prefixLift 4144659
  have htrace : WordTrace (prefixWord ++ tailWord_4144659) baseStart_4144659 baseEnd_4144659 := by
    simpa [prefixWord, tailWord_4144659, baseEnd_4144659] using wordTrace_append hprefix tailTrace_4144659
  have hstable : (prefixWord ++ tailWord_4144659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144659).length < 2 ^ (prefixWord ++ tailWord_4144659).sum := by decide
  have hdescent : baseEnd_4144659 < baseStart_4144659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144728 : List Nat := [2, 1, 2, 2, 1, 2, 1, 11]
def baseStart_4144728 : Nat := 118140960795 + 4144728 * 2 ^ 59
def prefixEnd_4144728 : Nat := 4983230072969 + 3 ^ 40 * 4144728 * 2
def baseEnd_4144728 : Nat := 157647233048027034543611

theorem tailTrace_4144728 : CollatzResearch.WordTrace tailWord_4144728 prefixEnd_4144728 157647233048027034543611 := by
  unfold tailWord_4144728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75585324664182897015821419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100780432885577196021095225 75585324664182897015821419)
  ·
    refine ⟨113377986996274345523732129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75585324664182897015821419 113377986996274345523732129)
    ·
      refine ⟨85033490247205759142799097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113377986996274345523732129 85033490247205759142799097)
      ·
        refine ⟨63775117685404319357099323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85033490247205759142799097 63775117685404319357099323)
        ·
          refine ⟨95662676528106479035648985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63775117685404319357099323 95662676528106479035648985)
          ·
            refine ⟨71747007396079859276736739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95662676528106479035648985 71747007396079859276736739)
            ·
              refine ⟨107620511094119788915105109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71747007396079859276736739 107620511094119788915105109)
              ·
                refine ⟨157647233048027034543611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107620511094119788915105109 157647233048027034543611)
                ·
                  rfl

theorem cell22_4144728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_4144728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144728 prefixEnd_4144728 := by exact prefixLift 4144728
  have htrace : WordTrace (prefixWord ++ tailWord_4144728) baseStart_4144728 baseEnd_4144728 := by
    simpa [prefixWord, tailWord_4144728, baseEnd_4144728] using wordTrace_append hprefix tailTrace_4144728
  have hstable : (prefixWord ++ tailWord_4144728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144728).length < 2 ^ (prefixWord ++ tailWord_4144728).sum := by decide
  have hdescent : baseEnd_4144728 < baseStart_4144728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144732 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4144732 : Nat := 118140960795 + 4144732 * 2 ^ 59
def prefixEnd_4144732 : Nat := 4983230072969 + 3 ^ 40 * 4144732 * 2
def baseEnd_4144732 : Nat := 1418826466713988633792487

theorem tailTrace_4144732 : CollatzResearch.WordTrace tailWord_4144732 prefixEnd_4144732 1418826466713988633792487 := by
  unfold tailWord_4144732
  simp only [CollatzResearch.WordTrace]
  refine ⟨75585397610175651357394225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100780530146900868476525633 75585397610175651357394225)
  ·
    refine ⟨56689048207631738518045669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75585397610175651357394225 56689048207631738518045669)
    ·
      refine ⟨10629196538930950972133563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56689048207631738518045669 10629196538930950972133563)
      ·
        refine ⟨15943794808396426458200345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10629196538930950972133563 15943794808396426458200345)
        ·
          refine ⟨11957846106297319843650259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15943794808396426458200345 11957846106297319843650259)
          ·
            refine ⟨17936769159445979765475389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957846106297319843650259 17936769159445979765475389)
            ·
              refine ⟨6726288434792242412053271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17936769159445979765475389 6726288434792242412053271)
              ·
                refine ⟨10089432652188363618079907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726288434792242412053271 10089432652188363618079907)
                ·
                  refine ⟨15134148978282545427119861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089432652188363618079907 15134148978282545427119861)
                  ·
                    refine ⟨1418826466713988633792487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15134148978282545427119861 1418826466713988633792487)
                    ·
                      rfl

theorem cell22_4144732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4144732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144732 prefixEnd_4144732 := by exact prefixLift 4144732
  have htrace : WordTrace (prefixWord ++ tailWord_4144732) baseStart_4144732 baseEnd_4144732 := by
    simpa [prefixWord, tailWord_4144732, baseEnd_4144732] using wordTrace_append hprefix tailTrace_4144732
  have hstable : (prefixWord ++ tailWord_4144732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144732).length < 2 ^ (prefixWord ++ tailWord_4144732).sum := by decide
  have hdescent : baseEnd_4144732 < baseStart_4144732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144745 : List Nat := [1, 2, 1, 1, 1, 4, 6, 6]
def baseStart_4144745 : Nat := 118140960795 + 4144745 * 2 ^ 59
def prefixEnd_4144745 : Nat := 4983230072969 + 3 ^ 40 * 4144745 * 2
def baseEnd_4144745 : Nat := 157647879653295659246383

theorem tailTrace_4144745 : CollatzResearch.WordTrace tailWord_4144745 prefixEnd_4144745 157647879653295659246383 := by
  unfold tailWord_4144745
  simp only [CollatzResearch.WordTrace]
  refine ⟨151171269369304205935011689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100780846246202803956674459 151171269369304205935011689)
  ·
    refine ⟨113378452026978154451258767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151171269369304205935011689 113378452026978154451258767)
    ·
      refine ⟨170067678040467231676888151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113378452026978154451258767 170067678040467231676888151)
      ·
        refine ⟨255101517060700847515332227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170067678040467231676888151 255101517060700847515332227)
        ·
          refine ⟨382652275591051271272998341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255101517060700847515332227 382652275591051271272998341)
          ·
            refine ⟨71747301673322113363687189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382652275591051271272998341 71747301673322113363687189)
            ·
              refine ⟨3363154765936974063922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71747301673322113363687189 3363154765936974063922837)
              ·
                refine ⟨157647879653295659246383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3363154765936974063922837 157647879653295659246383)
                ·
                  rfl

theorem cell22_4144745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 6].length) (baseStart_4144745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144745 prefixEnd_4144745 := by exact prefixLift 4144745
  have htrace : WordTrace (prefixWord ++ tailWord_4144745) baseStart_4144745 baseEnd_4144745 := by
    simpa [prefixWord, tailWord_4144745, baseEnd_4144745] using wordTrace_append hprefix tailTrace_4144745
  have hstable : (prefixWord ++ tailWord_4144745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144745).length < 2 ^ (prefixWord ++ tailWord_4144745).sum := by decide
  have hdescent : baseEnd_4144745 < baseStart_4144745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144777 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_4144777 : Nat := 118140960795 + 4144777 * 2 ^ 59
def prefixEnd_4144777 : Nat := 4983230072969 + 3 ^ 40 * 4144777 * 2
def baseEnd_4144777 : Nat := 1418841871133623516417349

theorem tailTrace_4144777 : CollatzResearch.WordTrace tailWord_4144777 prefixEnd_4144777 1418841871133623516417349 := by
  unfold tailWord_4144777
  simp only [CollatzResearch.WordTrace]
  refine ⟨151172436505188275400176585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100781624336792183600117723 151172436505188275400176585)
  ·
    refine ⟨113379327378891206550132439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151172436505188275400176585 113379327378891206550132439)
    ·
      refine ⟨170068991068336809825198659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113379327378891206550132439 170068991068336809825198659)
      ·
        refine ⟨255103486602505214737797989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170068991068336809825198659 255103486602505214737797989)
        ·
          refine ⟨47831903737969727763337123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255103486602505214737797989 47831903737969727763337123)
          ·
            refine ⟨71747855606954591645005685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47831903737969727763337123 71747855606954591645005685)
            ·
              refine ⟨6726361463151992966719283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71747855606954591645005685 6726361463151992966719283)
              ·
                refine ⟨10089542194727989450078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726361463151992966719283 10089542194727989450078925)
                ·
                  refine ⟨3783578323022996043779597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10089542194727989450078925 3783578323022996043779597)
                  ·
                    refine ⟨1418841871133623516417349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783578323022996043779597 1418841871133623516417349)
                    ·
                      rfl

theorem cell22_4144777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_4144777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144777 prefixEnd_4144777 := by exact prefixLift 4144777
  have htrace : WordTrace (prefixWord ++ tailWord_4144777) baseStart_4144777 baseEnd_4144777 := by
    simpa [prefixWord, tailWord_4144777, baseEnd_4144777] using wordTrace_append hprefix tailTrace_4144777
  have hstable : (prefixWord ++ tailWord_4144777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144777).length < 2 ^ (prefixWord ++ tailWord_4144777).sum := by decide
  have hdescent : baseEnd_4144777 < baseStart_4144777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144828 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_4144828 : Nat := 118140960795 + 4144828 * 2 ^ 59
def prefixEnd_4144828 : Nat := 4983230072969 + 3 ^ 40 * 4144828 * 2
def baseEnd_4144828 : Nat := 1418859329475876383392193

theorem tailTrace_4144828 : CollatzResearch.WordTrace tailWord_4144828 prefixEnd_4144828 1418859329475876383392193 := by
  unfold tailWord_4144828
  simp only [CollatzResearch.WordTrace]
  refine ⟨75587148314001755555141569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100782864418669007406855425 75587148314001755555141569)
  ·
    refine ⟨56690361235501316666356177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75587148314001755555141569 56690361235501316666356177)
    ·
      refine ⟨42517770926625987499767133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56690361235501316666356177 42517770926625987499767133)
      ·
        refine ⟨15944164097484745312412675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42517770926625987499767133 15944164097484745312412675)
        ·
          refine ⟨23916246146227117968619013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944164097484745312412675 23916246146227117968619013)
          ·
            refine ⟨4484296152417584619116065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23916246146227117968619013 4484296152417584619116065)
            ·
              refine ⟨3363222114313188464337049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484296152417584619116065 3363222114313188464337049)
              ·
                refine ⟨2522416585734891348252787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363222114313188464337049 2522416585734891348252787)
                ·
                  refine ⟨3783624878602337022379181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522416585734891348252787 3783624878602337022379181)
                  ·
                    refine ⟨1418859329475876383392193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783624878602337022379181 1418859329475876383392193)
                    ·
                      rfl

theorem cell22_4144828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_4144828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144828 prefixEnd_4144828 := by exact prefixLift 4144828
  have htrace : WordTrace (prefixWord ++ tailWord_4144828) baseStart_4144828 baseEnd_4144828 := by
    simpa [prefixWord, tailWord_4144828, baseEnd_4144828] using wordTrace_append hprefix tailTrace_4144828
  have hstable : (prefixWord ++ tailWord_4144828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144828).length < 2 ^ (prefixWord ++ tailWord_4144828).sum := by decide
  have hdescent : baseEnd_4144828 < baseStart_4144828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144852 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4144852 : Nat := 118140960795 + 4144852 * 2 ^ 59
def prefixEnd_4144852 : Nat := 4983230072969 + 3 ^ 40 * 4144852 * 2
def baseEnd_4144852 : Nat := 472955848388782773597373

theorem tailTrace_4144852 : CollatzResearch.WordTrace tailWord_4144852 prefixEnd_4144852 472955848388782773597373 := by
  unfold tailWord_4144852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75587585989958281604578405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100783447986611042139437873 75587585989958281604578405)
  ·
    refine ⟨14172672373117177800858451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75587585989958281604578405 14172672373117177800858451)
    ·
      refine ⟨21259008559675766701287677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14172672373117177800858451 21259008559675766701287677)
      ·
        refine ⟨7972128209878412512982879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21259008559675766701287677 7972128209878412512982879)
        ·
          refine ⟨11958192314817618769474319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972128209878412512982879 11958192314817618769474319)
          ·
            refine ⟨17937288472226428154211479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958192314817618769474319 17937288472226428154211479)
            ·
              refine ⟨26905932708339642231317219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17937288472226428154211479 26905932708339642231317219)
              ·
                refine ⟨40358899062509463346975829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26905932708339642231317219 40358899062509463346975829)
                ·
                  refine ⟨472955848388782773597373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40358899062509463346975829 472955848388782773597373)
                  ·
                    rfl

theorem cell22_4144852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4144852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144852 prefixEnd_4144852 := by exact prefixLift 4144852
  have htrace : WordTrace (prefixWord ++ tailWord_4144852) baseStart_4144852 baseEnd_4144852 := by
    simpa [prefixWord, tailWord_4144852, baseEnd_4144852] using wordTrace_append hprefix tailTrace_4144852
  have hstable : (prefixWord ++ tailWord_4144852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144852).length < 2 ^ (prefixWord ++ tailWord_4144852).sum := by decide
  have hdescent : baseEnd_4144852 < baseStart_4144852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144869 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 4]
def baseStart_4144869 : Nat := 118140960795 + 4144869 * 2 ^ 59
def prefixEnd_4144869 : Nat := 4983230072969 + 3 ^ 40 * 4144869 * 2
def baseEnd_4144869 : Nat := 472957788204588647705689

theorem tailTrace_4144869 : CollatzResearch.WordTrace tailWord_4144869 prefixEnd_4144869 472957788204588647705689 := by
  unfold tailWord_4144869
  simp only [CollatzResearch.WordTrace]
  refine ⟨151175792020854975112525661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100783861347236650075017107 151175792020854975112525661)
  ·
    refine ⟨56690922007820615667197123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151175792020854975112525661 56690922007820615667197123)
    ·
      refine ⟨85036383011730923500795685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56690922007820615667197123 85036383011730923500795685)
      ·
        refine ⟨15944321814699548156399191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85036383011730923500795685 15944321814699548156399191)
        ·
          refine ⟨23916482722049322234598787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944321814699548156399191 23916482722049322234598787)
          ·
            refine ⟨35874724083073983351898181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916482722049322234598787 35874724083073983351898181)
            ·
              refine ⟨6726510765576371878480909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35874724083073983351898181 6726510765576371878480909)
              ·
                refine ⟨2522441537091139454430341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726510765576371878480909 2522441537091139454430341)
                ·
                  refine ⟨472957788204588647705689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522441537091139454430341 472957788204588647705689)
                  ·
                    rfl

theorem cell22_4144869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_4144869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144869 prefixEnd_4144869 := by exact prefixLift 4144869
  have htrace : WordTrace (prefixWord ++ tailWord_4144869) baseStart_4144869 baseEnd_4144869 := by
    simpa [prefixWord, tailWord_4144869, baseEnd_4144869] using wordTrace_append hprefix tailTrace_4144869
  have hstable : (prefixWord ++ tailWord_4144869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144869).length < 2 ^ (prefixWord ++ tailWord_4144869).sum := by decide
  have hdescent : baseEnd_4144869 < baseStart_4144869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144871 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 1, 4]
def baseStart_4144871 : Nat := 118140960795 + 4144871 * 2 ^ 59
def prefixEnd_4144871 : Nat := 4983230072969 + 3 ^ 40 * 4144871 * 2
def baseEnd_4144871 : Nat := 1418874049254638604567061

theorem tailTrace_4144871 : CollatzResearch.WordTrace tailWord_4144871 prefixEnd_4144871 1418874049254638604567061 := by
  unfold tailWord_4144871
  simp only [CollatzResearch.WordTrace]
  refine ⟨151175864966847729454098467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100783909977898486302732311 151175864966847729454098467)
  ·
    refine ⟨226763797450271594181147701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151175864966847729454098467 226763797450271594181147701)
    ·
      refine ⟨21259106010962961954482597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226763797450271594181147701 21259106010962961954482597)
      ·
        refine ⟨3986082377055555366465487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21259106010962961954482597 3986082377055555366465487)
        ·
          refine ⟨5979123565583333049698231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986082377055555366465487 5979123565583333049698231)
          ·
            refine ⟨8968685348374999574547347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979123565583333049698231 8968685348374999574547347)
            ·
              refine ⟨13453028022562499361821021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8968685348374999574547347 13453028022562499361821021)
              ·
                refine ⟨5044885508460937260682883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13453028022562499361821021 5044885508460937260682883)
                ·
                  refine ⟨7567328262691405891024325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044885508460937260682883 7567328262691405891024325)
                  ·
                    refine ⟨1418874049254638604567061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567328262691405891024325 1418874049254638604567061)
                    ·
                      rfl

theorem cell22_4144871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_4144871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144871 prefixEnd_4144871 := by exact prefixLift 4144871
  have htrace : WordTrace (prefixWord ++ tailWord_4144871) baseStart_4144871 baseEnd_4144871 := by
    simpa [prefixWord, tailWord_4144871, baseEnd_4144871] using wordTrace_append hprefix tailTrace_4144871
  have hstable : (prefixWord ++ tailWord_4144871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144871).length < 2 ^ (prefixWord ++ tailWord_4144871).sum := by decide
  have hdescent : baseEnd_4144871 < baseStart_4144871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144882 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4144882 : Nat := 118140960795 + 4144882 * 2 ^ 59
def prefixEnd_4144882 : Nat := 4983230072969 + 3 ^ 40 * 4144882 * 2
def baseEnd_4144882 : Nat := 1418877814779438242542027

theorem tailTrace_4144882 : CollatzResearch.WordTrace tailWord_4144882 prefixEnd_4144882 1418877814779438242542027 := by
  unfold tailWord_4144882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794066542451969583187225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100784177446538585555165933 37794066542451969583187225)
  ·
    refine ⟨28345549906838977187390419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37794066542451969583187225 28345549906838977187390419)
    ·
      refine ⟨42518324860258465781085629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28345549906838977187390419 42518324860258465781085629)
      ·
        refine ⟨15944371822596924667907111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42518324860258465781085629 15944371822596924667907111)
        ·
          refine ⟨23916557733895387001860667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944371822596924667907111 23916557733895387001860667)
          ·
            refine ⟨35874836600843080502791001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916557733895387001860667 35874836600843080502791001)
            ·
              refine ⟨26906127450632310377093251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35874836600843080502791001 26906127450632310377093251)
              ·
                refine ⟨40359191175948465565639877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26906127450632310377093251 40359191175948465565639877)
                ·
                  refine ⟨7567348345490337293557477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40359191175948465565639877 7567348345490337293557477)
                  ·
                    refine ⟨1418877814779438242542027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567348345490337293557477 1418877814779438242542027)
                    ·
                      rfl

theorem cell22_4144882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4144882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144882 prefixEnd_4144882 := by exact prefixLift 4144882
  have htrace : WordTrace (prefixWord ++ tailWord_4144882) baseStart_4144882 baseEnd_4144882 := by
    simpa [prefixWord, tailWord_4144882, baseEnd_4144882] using wordTrace_append hprefix tailTrace_4144882
  have hstable : (prefixWord ++ tailWord_4144882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144882).length < 2 ^ (prefixWord ++ tailWord_4144882).sum := by decide
  have hdescent : baseEnd_4144882 < baseStart_4144882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144914 : List Nat := [3, 2, 4, 1, 1, 2, 1, 8]
def baseStart_4144914 : Nat := 118140960795 + 4144914 * 2 ^ 59
def prefixEnd_4144914 : Nat := 4983230072969 + 3 ^ 40 * 4144914 * 2
def baseEnd_4144914 : Nat := 157654307670377869526881

theorem tailTrace_4144914 : CollatzResearch.WordTrace tailWord_4144914 prefixEnd_4144914 157654307670377869526881 := by
  unfold tailWord_4144914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794358326422986949478449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100784955537127965198609197 37794358326422986949478449)
  ·
    refine ⟨28345768744817240212108837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37794358326422986949478449 28345768744817240212108837)
    ·
      refine ⟨5314831639653232539770407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28345768744817240212108837 5314831639653232539770407)
      ·
        refine ⟨7972247459479848809655611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314831639653232539770407 7972247459479848809655611)
        ·
          refine ⟨11958371189219773214483417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972247459479848809655611 11958371189219773214483417)
          ·
            refine ⟨8968778391914829910862563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11958371189219773214483417 8968778391914829910862563)
            ·
              refine ⟨13453167587872244866293845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8968778391914829910862563 13453167587872244866293845)
              ·
                refine ⟨157654307670377869526881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13453167587872244866293845 157654307670377869526881)
                ·
                  rfl

theorem cell22_4144914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_4144914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144914 prefixEnd_4144914 := by exact prefixLift 4144914
  have htrace : WordTrace (prefixWord ++ tailWord_4144914) baseStart_4144914 baseEnd_4144914 := by
    simpa [prefixWord, tailWord_4144914, baseEnd_4144914] using wordTrace_append hprefix tailTrace_4144914
  have hstable : (prefixWord ++ tailWord_4144914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144914).length < 2 ^ (prefixWord ++ tailWord_4144914).sum := by decide
  have hdescent : baseEnd_4144914 < baseStart_4144914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144946 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_4144946 : Nat := 118140960795 + 4144946 * 2 ^ 59
def prefixEnd_4144946 : Nat := 4983230072969 + 3 ^ 40 * 4144946 * 2
def baseEnd_4144946 : Nat := 1418899723287363408941831

theorem tailTrace_4144946 : CollatzResearch.WordTrace tailWord_4144946 prefixEnd_4144946 1418899723287363408941831 := by
  unfold tailWord_4144946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794650110394004315769673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100785733627717344842052461 37794650110394004315769673)
  ·
    refine ⟨28345987582795503236827255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37794650110394004315769673 28345987582795503236827255)
    ·
      refine ⟨42518981374193254855240883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28345987582795503236827255 42518981374193254855240883)
      ·
        refine ⟨63778472061289882282861325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42518981374193254855240883 63778472061289882282861325)
        ·
          refine ⟨23916927022983705856072997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63778472061289882282861325 23916927022983705856072997)
          ·
            refine ⟨4484423816809444848013687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23916927022983705856072997 4484423816809444848013687)
            ·
              refine ⟨6726635725214167272020531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484423816809444848013687 6726635725214167272020531)
              ·
                refine ⟨10089953587821250908030797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726635725214167272020531 10089953587821250908030797)
                ·
                  refine ⟨3783732595432969090511549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10089953587821250908030797 3783732595432969090511549)
                  ·
                    refine ⟨1418899723287363408941831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783732595432969090511549 1418899723287363408941831)
                    ·
                      rfl

theorem cell22_4144946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_4144946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144946 prefixEnd_4144946 := by exact prefixLift 4144946
  have htrace : WordTrace (prefixWord ++ tailWord_4144946) baseStart_4144946 baseEnd_4144946 := by
    simpa [prefixWord, tailWord_4144946, baseEnd_4144946] using wordTrace_append hprefix tailTrace_4144946
  have hstable : (prefixWord ++ tailWord_4144946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144946).length < 2 ^ (prefixWord ++ tailWord_4144946).sum := by decide
  have hdescent : baseEnd_4144946 < baseStart_4144946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144959 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 5]
def baseStart_4144959 : Nat := 118140960795 + 4144959 * 2 ^ 59
def prefixEnd_4144959 : Nat := 4983230072969 + 3 ^ 40 * 4144959 * 2
def baseEnd_4144959 : Nat := 472968057817678569455597

theorem tailTrace_4144959 : CollatzResearch.WordTrace tailWord_4144959 prefixEnd_4144959 472968057817678569455597 := by
  unfold tailWord_4144959
  simp only [CollatzResearch.WordTrace]
  refine ⟨151179074590528920483301931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100786049727019280322201287 151179074590528920483301931)
  ·
    refine ⟨226768611885793380724952897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151179074590528920483301931 226768611885793380724952897)
    ·
      refine ⟨170076458914345035543714673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226768611885793380724952897 170076458914345035543714673)
      ·
        refine ⟨127557344185758776657786005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170076458914345035543714673 127557344185758776657786005)
        ·
          refine ⟨5979250508707442655833719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127557344185758776657786005 5979250508707442655833719)
          ·
            refine ⟨8968875763061163983750579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979250508707442655833719 8968875763061163983750579)
            ·
              refine ⟨13453313644591745975625869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8968875763061163983750579 13453313644591745975625869)
              ·
                refine ⟨5044992616721904740859701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13453313644591745975625869 5044992616721904740859701)
                ·
                  refine ⟨472968057817678569455597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044992616721904740859701 472968057817678569455597)
                  ·
                    rfl

theorem cell22_4144959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 5].length) (baseStart_4144959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4144959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4144959 prefixEnd_4144959 := by exact prefixLift 4144959
  have htrace : WordTrace (prefixWord ++ tailWord_4144959) baseStart_4144959 baseEnd_4144959 := by
    simpa [prefixWord, tailWord_4144959, baseEnd_4144959] using wordTrace_append hprefix tailTrace_4144959
  have hstable : (prefixWord ++ tailWord_4144959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144959).length < 2 ^ (prefixWord ++ tailWord_4144959).sum := by decide
  have hdescent : baseEnd_4144959 < baseStart_4144959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145017 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_4145017 : Nat := 118140960795 + 4145017 * 2 ^ 59
def prefixEnd_4145017 : Nat := 4983230072969 + 3 ^ 40 * 4145017 * 2
def baseEnd_4145017 : Nat := 1418924028038342890416613

theorem tailTrace_4145017 : CollatzResearch.WordTrace tailWord_4145017 prefixEnd_4145017 1418924028038342890416613 := by
  unfold tailWord_4145017
  simp only [CollatzResearch.WordTrace]
  refine ⟨151181190024318796388913305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100787460016212530925942203 151181190024318796388913305)
  ·
    refine ⟨113385892518239097291684979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151181190024318796388913305 113385892518239097291684979)
    ·
      refine ⟨170078838777358645937527469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113385892518239097291684979 170078838777358645937527469)
      ·
        refine ⟨63779564541509492226572801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170078838777358645937527469 63779564541509492226572801)
        ·
          refine ⟨47834673406132119169929601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63779564541509492226572801 47834673406132119169929601)
          ·
            refine ⟨35876005054599089377447201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47834673406132119169929601 35876005054599089377447201)
            ·
              refine ⟨26907003790949317033085401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35876005054599089377447201 26907003790949317033085401)
              ·
                refine ⟨20180252843211987774814051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26907003790949317033085401 20180252843211987774814051)
                ·
                  refine ⟨30270379264817981662221077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20180252843211987774814051 30270379264817981662221077)
                  ·
                    refine ⟨1418924028038342890416613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30270379264817981662221077 1418924028038342890416613)
                    ·
                      rfl

theorem cell22_4145017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_4145017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145017 prefixEnd_4145017 := by exact prefixLift 4145017
  have htrace : WordTrace (prefixWord ++ tailWord_4145017) baseStart_4145017 baseEnd_4145017 := by
    simpa [prefixWord, tailWord_4145017, baseEnd_4145017] using wordTrace_append hprefix tailTrace_4145017
  have hstable : (prefixWord ++ tailWord_4145017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145017).length < 2 ^ (prefixWord ++ tailWord_4145017).sum := by decide
  have hdescent : baseEnd_4145017 < baseStart_4145017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145053 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_4145053 : Nat := 118140960795 + 4145053 * 2 ^ 59
def prefixEnd_4145053 : Nat := 4983230072969 + 3 ^ 40 * 4145053 * 2
def baseEnd_4145053 : Nat := 1418936351574050796516503

theorem tailTrace_4145053 : CollatzResearch.WordTrace tailWord_4145053 prefixEnd_4145053 1418936351574050796516503 := by
  unfold tailWord_4145053
  simp only [CollatzResearch.WordTrace]
  refine ⟨151182503052188374537223813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100788335368125583024815875 151182503052188374537223813)
  ·
    refine ⟨28346719322285320225729465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151182503052188374537223813 28346719322285320225729465)
    ·
      refine ⟨21260039491713990169297099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28346719322285320225729465 21260039491713990169297099)
      ·
        refine ⟨31890059237570985253945649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21260039491713990169297099 31890059237570985253945649)
        ·
          refine ⟨23917544428178238940459237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31890059237570985253945649 23917544428178238940459237)
          ·
            refine ⟨4484539580283419801336107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23917544428178238940459237 4484539580283419801336107)
            ·
              refine ⟨6726809370425129702004161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484539580283419801336107 6726809370425129702004161)
              ·
                refine ⟨5045107027818847276503121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726809370425129702004161 5045107027818847276503121)
                ·
                  refine ⟨3783830270864135457377341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045107027818847276503121 3783830270864135457377341)
                  ·
                    refine ⟨1418936351574050796516503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783830270864135457377341 1418936351574050796516503)
                    ·
                      rfl

theorem cell22_4145053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_4145053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145053 prefixEnd_4145053 := by exact prefixLift 4145053
  have htrace : WordTrace (prefixWord ++ tailWord_4145053) baseStart_4145053 baseEnd_4145053 := by
    simpa [prefixWord, tailWord_4145053, baseEnd_4145053] using wordTrace_append hprefix tailTrace_4145053
  have hstable : (prefixWord ++ tailWord_4145053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145053).length < 2 ^ (prefixWord ++ tailWord_4145053).sum := by decide
  have hdescent : baseEnd_4145053 < baseStart_4145053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145098 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_4145098 : Nat := 118140960795 + 4145098 * 2 ^ 59
def prefixEnd_4145098 : Nat := 4983230072969 + 3 ^ 40 * 4145098 * 2
def baseEnd_4145098 : Nat := 1418951755993685679141365

theorem tailTrace_4145098 : CollatzResearch.WordTrace tailWord_4145098 prefixEnd_4145098 1418951755993685679141365 := by
  unfold tailWord_4145098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37796036084256336805652987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100789429558016898148407965 37796036084256336805652987)
  ·
    refine ⟨56694054126384505208479481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37796036084256336805652987 56694054126384505208479481)
    ·
      refine ⟨42520540594788378906359611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56694054126384505208479481 42520540594788378906359611)
      ·
        refine ⟨63780810892182568359539417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42520540594788378906359611 63780810892182568359539417)
        ·
          refine ⟨47835608169136926269654563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63780810892182568359539417 47835608169136926269654563)
          ·
            refine ⟨71753412253705389404481845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47835608169136926269654563 71753412253705389404481845)
            ·
              refine ⟨6726882398784880256670173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71753412253705389404481845 6726882398784880256670173)
              ·
                refine ⟨2522580899544330096251315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726882398784880256670173 2522580899544330096251315)
                ·
                  refine ⟨3783871349316495144376973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522580899544330096251315 3783871349316495144376973)
                  ·
                    refine ⟨1418951755993685679141365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783871349316495144376973 1418951755993685679141365)
                    ·
                      rfl

theorem cell22_4145098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_4145098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145098 prefixEnd_4145098 := by exact prefixLift 4145098
  have htrace : WordTrace (prefixWord ++ tailWord_4145098) baseStart_4145098 baseEnd_4145098 := by
    simpa [prefixWord, tailWord_4145098, baseEnd_4145098] using wordTrace_append hprefix tailTrace_4145098
  have hstable : (prefixWord ++ tailWord_4145098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145098).length < 2 ^ (prefixWord ++ tailWord_4145098).sum := by decide
  have hdescent : baseEnd_4145098 < baseStart_4145098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145124 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_4145124 : Nat := 118140960795 + 4145124 * 2 ^ 59
def prefixEnd_4145124 : Nat := 4983230072969 + 3 ^ 40 * 4145124 * 2
def baseEnd_4145124 : Nat := 1418960656325030277991285

theorem tailTrace_4145124 : CollatzResearch.WordTrace tailWord_4145124 prefixEnd_4145124 1418960656325030277991285 := by
  unfold tailWord_4145124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75592546317465576831529213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100790061756620769108705617 75592546317465576831529213)
  ·
    refine ⟨28347204869049591311823455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75592546317465576831529213 28347204869049591311823455)
    ·
      refine ⟨42520807303574386967735183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28347204869049591311823455 42520807303574386967735183)
      ·
        refine ⟨63781210955361580451602775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42520807303574386967735183 63781210955361580451602775)
        ·
          refine ⟨95671816433042370677404163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63781210955361580451602775 95671816433042370677404163)
          ·
            refine ⟨143507724649563556016106245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95671816433042370677404163 143507724649563556016106245)
            ·
              refine ⟨26907698371793166753019921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143507724649563556016106245 26907698371793166753019921)
              ·
                refine ⟨20180773778844875064764941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26907698371793166753019921 20180773778844875064764941)
                ·
                  refine ⟨7567790167066828149286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20180773778844875064764941 7567790167066828149286853)
                  ·
                    refine ⟨1418960656325030277991285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567790167066828149286853 1418960656325030277991285)
                    ·
                      rfl

theorem cell22_4145124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_4145124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145124 prefixEnd_4145124 := by exact prefixLift 4145124
  have htrace : WordTrace (prefixWord ++ tailWord_4145124) baseStart_4145124 baseEnd_4145124 := by
    simpa [prefixWord, tailWord_4145124, baseEnd_4145124] using wordTrace_append hprefix tailTrace_4145124
  have hstable : (prefixWord ++ tailWord_4145124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145124).length < 2 ^ (prefixWord ++ tailWord_4145124).sum := by decide
  have hdescent : baseEnd_4145124 < baseStart_4145124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145171 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 2, 3]
def baseStart_4145171 : Nat := 118140960795 + 4145171 * 2 ^ 59
def prefixEnd_4145171 : Nat := 4983230072969 + 3 ^ 40 * 4145171 * 2
def baseEnd_4145171 : Nat := 1418976745385537822066141

theorem tailTrace_4145171 : CollatzResearch.WordTrace tailWord_4145171 prefixEnd_4145171 1418976745385537822066141 := by
  unfold tailWord_4145171
  simp only [CollatzResearch.WordTrace]
  refine ⟨151186806865760880690019367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100791204577173920460012911 151186806865760880690019367)
  ·
    refine ⟨226780210298641321035029051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151186806865760880690019367 226780210298641321035029051)
    ·
      refine ⟨340170315447961981552543577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226780210298641321035029051 340170315447961981552543577)
      ·
        refine ⟨255127736585971486164407683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340170315447961981552543577 255127736585971486164407683)
        ·
          refine ⟨382691604878957229246611525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255127736585971486164407683 382691604878957229246611525)
          ·
            refine ⟨71754675914804480483739661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382691604878957229246611525 71754675914804480483739661)
            ·
              refine ⟨26908003468051680181402373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71754675914804480483739661 26908003468051680181402373)
              ·
                refine ⟨5045250650259690034012945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26908003468051680181402373 5045250650259690034012945)
                ·
                  refine ⟨3783937987694767525509709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045250650259690034012945 3783937987694767525509709)
                  ·
                    refine ⟨1418976745385537822066141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783937987694767525509709 1418976745385537822066141)
                    ·
                      rfl

theorem cell22_4145171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 3].length) (baseStart_4145171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145171 prefixEnd_4145171 := by exact prefixLift 4145171
  have htrace : WordTrace (prefixWord ++ tailWord_4145171) baseStart_4145171 baseEnd_4145171 := by
    simpa [prefixWord, tailWord_4145171, baseEnd_4145171] using wordTrace_append hprefix tailTrace_4145171
  have hstable : (prefixWord ++ tailWord_4145171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145171).length < 2 ^ (prefixWord ++ tailWord_4145171).sum := by decide
  have hdescent : baseEnd_4145171 < baseStart_4145171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145173 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 4]
def baseStart_4145173 : Nat := 118140960795 + 4145173 * 2 ^ 59
def prefixEnd_4145173 : Nat := 4983230072969 + 3 ^ 40 * 4145173 * 2
def baseEnd_4145173 : Nat := 472992476675470161172045

theorem tailTrace_4145173 : CollatzResearch.WordTrace tailWord_4145173 prefixEnd_4145173 472992476675470161172045 := by
  unfold tailWord_4145173
  simp only [CollatzResearch.WordTrace]
  refine ⟨151186879811753635031592173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100791253207835756687728115 151186879811753635031592173)
  ·
    refine ⟨56695079929407613136847065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151186879811753635031592173 56695079929407613136847065)
    ·
      refine ⟨42521309947055709852635299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56695079929407613136847065 42521309947055709852635299)
      ·
        refine ⟨63781964920583564778952949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42521309947055709852635299 63781964920583564778952949)
        ·
          refine ⟨5979559211304709198026839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63781964920583564778952949 5979559211304709198026839)
          ·
            refine ⟨8969338816957063797040259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979559211304709198026839 8969338816957063797040259)
            ·
              refine ⟨13454008225435595695560389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8969338816957063797040259 13454008225435595695560389)
              ·
                refine ⟨2522626542269174192917573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13454008225435595695560389 2522626542269174192917573)
                ·
                  refine ⟨472992476675470161172045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522626542269174192917573 472992476675470161172045)
                  ·
                    rfl

theorem cell22_4145173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_4145173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4145173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4145173 prefixEnd_4145173 := by exact prefixLift 4145173
  have htrace : WordTrace (prefixWord ++ tailWord_4145173) baseStart_4145173 baseEnd_4145173 := by
    simpa [prefixWord, tailWord_4145173, baseEnd_4145173] using wordTrace_append hprefix tailTrace_4145173
  have hstable : (prefixWord ++ tailWord_4145173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145173).length < 2 ^ (prefixWord ++ tailWord_4145173).sum := by decide
  have hdescent : baseEnd_4145173 < baseStart_4145173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
