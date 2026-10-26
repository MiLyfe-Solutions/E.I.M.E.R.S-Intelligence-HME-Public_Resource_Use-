import V185TrunkScan22Chunk411

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3673060 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3673060 : Nat := 118140960795 + 3673060 * 2 ^ 59
def prefixEnd_3673060 : Nat := 4983230072969 + 3 ^ 40 * 3673060 * 2
def baseEnd_3673060 : Nat := 1257363501869002913038607

theorem tailTrace_3673060 : CollatzResearch.WordTrace tailWord_3673060 prefixEnd_3673060 1257363501869002913038607 := by
  unfold tailWord_3673060
  simp only [CollatzResearch.WordTrace]
  refine ⟨66983752036569201775256317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89311669382092269033675089 66983752036569201775256317)
  ·
    refine ⟨25118907013713450665721119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66983752036569201775256317 25118907013713450665721119)
    ·
      refine ⟨37678360520570175998581679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25118907013713450665721119 37678360520570175998581679)
      ·
        refine ⟨56517540780855263997872519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37678360520570175998581679 56517540780855263997872519)
        ·
          refine ⟨84776311171282895996808779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56517540780855263997872519 84776311171282895996808779)
          ·
            refine ⟨127164466756924343995213169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84776311171282895996808779 127164466756924343995213169)
            ·
              refine ⟨95373350067693257996409877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127164466756924343995213169 95373350067693257996409877)
              ·
                refine ⟨4470625784423121468581713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95373350067693257996409877 4470625784423121468581713)
                ·
                  refine ⟨3352969338317341101436285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470625784423121468581713 3352969338317341101436285)
                  ·
                    refine ⟨1257363501869002913038607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3352969338317341101436285 1257363501869002913038607)
                    ·
                      rfl

theorem cell22_3673060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3673060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673060 prefixEnd_3673060 := by exact prefixLift 3673060
  have htrace : WordTrace (prefixWord ++ tailWord_3673060) baseStart_3673060 baseEnd_3673060 := by
    simpa [prefixWord, tailWord_3673060, baseEnd_3673060] using wordTrace_append hprefix tailTrace_3673060
  have hstable : (prefixWord ++ tailWord_3673060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673060).length < 2 ^ (prefixWord ++ tailWord_3673060).sum := by decide
  have hdescent : baseEnd_3673060 < baseStart_3673060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673122 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3673122 : Nat := 118140960795 + 3673122 * 2 ^ 59
def prefixEnd_3673122 : Nat := 4983230072969 + 3 ^ 40 * 3673122 * 2
def baseEnd_3673122 : Nat := 1257384725736055417988417

theorem tailTrace_3673122 : CollatzResearch.WordTrace tailWord_3673122 prefixEnd_3673122 1257384725736055417988417 := by
  unfold tailWord_3673122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492441349728447034817405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89313176932609192092846413 33492441349728447034817405)
  ·
    refine ⟨12559665506148167638056527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33492441349728447034817405 12559665506148167638056527)
    ·
      refine ⟨18839498259222251457084791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12559665506148167638056527 18839498259222251457084791)
      ·
        refine ⟨28259247388833377185627187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18839498259222251457084791 28259247388833377185627187)
        ·
          refine ⟨42388871083250065778440781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28259247388833377185627187 42388871083250065778440781)
          ·
            refine ⟨15895826656218774666915293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42388871083250065778440781 15895826656218774666915293)
            ·
              refine ⟨5960934996082040500093235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15895826656218774666915293 5960934996082040500093235)
              ·
                refine ⟨8941402494123060750139853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960934996082040500093235 8941402494123060750139853)
                ·
                  refine ⟨3353025935296147781302445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8941402494123060750139853 3353025935296147781302445)
                  ·
                    refine ⟨1257384725736055417988417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353025935296147781302445 1257384725736055417988417)
                    ·
                      rfl

theorem cell22_3673122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3673122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673122 prefixEnd_3673122 := by exact prefixLift 3673122
  have htrace : WordTrace (prefixWord ++ tailWord_3673122) baseStart_3673122 baseEnd_3673122 := by
    simpa [prefixWord, tailWord_3673122, baseEnd_3673122] using wordTrace_append hprefix tailTrace_3673122
  have hstable : (prefixWord ++ tailWord_3673122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673122).length < 2 ^ (prefixWord ++ tailWord_3673122).sum := by decide
  have hdescent : baseEnd_3673122 < baseStart_3673122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673180 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_3673180 : Nat := 118140960795 + 3673180 * 2 ^ 59
def prefixEnd_3673180 : Nat := 4983230072969 + 3 ^ 40 * 3673180 * 2
def baseEnd_3673180 : Nat := 419134860107120866679413

theorem tailTrace_3673180 : CollatzResearch.WordTrace tailWord_3673180 prefixEnd_3673180 419134860107120866679413 := by
  unfold tailWord_3673180
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985940416351832022440497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89314587221802442696587329 66985940416351832022440497)
  ·
    refine ⟨50239455312263874016830373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66985940416351832022440497 50239455312263874016830373)
    ·
      refine ⟨9419897871049476378155695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50239455312263874016830373 9419897871049476378155695)
      ·
        refine ⟨14129846806574214567233543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9419897871049476378155695 14129846806574214567233543)
        ·
          refine ⟨21194770209861321850850315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129846806574214567233543 21194770209861321850850315)
          ·
            refine ⟨31792155314791982776275473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194770209861321850850315 31792155314791982776275473)
            ·
              refine ⟨23844116486093987082206605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31792155314791982776275473 23844116486093987082206605)
              ·
                refine ⟨8941543682285245155827477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23844116486093987082206605 8941543682285245155827477)
                ·
                  refine ⟨419134860107120866679413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8941543682285245155827477 419134860107120866679413)
                  ·
                    rfl

theorem cell22_3673180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_3673180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673180 prefixEnd_3673180 := by exact prefixLift 3673180
  have htrace : WordTrace (prefixWord ++ tailWord_3673180) baseStart_3673180 baseEnd_3673180 := by
    simpa [prefixWord, tailWord_3673180, baseEnd_3673180] using wordTrace_append hprefix tailTrace_3673180
  have hstable : (prefixWord ++ tailWord_3673180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673180).length < 2 ^ (prefixWord ++ tailWord_3673180).sum := by decide
  have hdescent : baseEnd_3673180 < baseStart_3673180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673208 : List Nat := [2, 1, 2, 1, 1, 1, 4, 10]
def baseStart_3673208 : Nat := 118140960795 + 3673208 * 2 ^ 59
def prefixEnd_3673208 : Nat := 4983230072969 + 3 ^ 40 * 3673208 * 2
def baseEnd_3673208 : Nat := 139712685032619984482017

theorem tailTrace_3673208 : CollatzResearch.WordTrace tailWord_3673208 prefixEnd_3673208 139712685032619984482017 := by
  unfold tailWord_3673208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66986451038301112413450139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89315268051068149884600185 66986451038301112413450139)
  ·
    refine ⟨100479676557451668620175209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66986451038301112413450139 100479676557451668620175209)
    ·
      refine ⟨75359757418088751465131407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100479676557451668620175209 75359757418088751465131407)
      ·
        refine ⟨113039636127133127197697111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75359757418088751465131407 113039636127133127197697111)
        ·
          refine ⟨169559454190699690796545667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113039636127133127197697111 169559454190699690796545667)
          ·
            refine ⟨254339181286049536194818501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169559454190699690796545667 254339181286049536194818501)
            ·
              refine ⟨47688596491134288036528469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254339181286049536194818501 47688596491134288036528469)
              ·
                refine ⟨139712685032619984482017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47688596491134288036528469 139712685032619984482017)
                ·
                  rfl

theorem cell22_3673208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_3673208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673208 prefixEnd_3673208 := by exact prefixLift 3673208
  have htrace : WordTrace (prefixWord ++ tailWord_3673208) baseStart_3673208 baseEnd_3673208 := by
    simpa [prefixWord, tailWord_3673208, baseEnd_3673208] using wordTrace_append hprefix tailTrace_3673208
  have hstable : (prefixWord ++ tailWord_3673208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673208).length < 2 ^ (prefixWord ++ tailWord_3673208).sum := by decide
  have hdescent : baseEnd_3673208 < baseStart_3673208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673379 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 2, 4]
def baseStart_3673379 : Nat := 118140960795 + 3673379 * 2 ^ 59
def prefixEnd_3673379 : Nat := 4983230072969 + 3 ^ 40 * 3673379 * 2
def baseEnd_3673379 : Nat := 1257472702088192414312629

theorem tailTrace_3673379 : CollatzResearch.WordTrace tailWord_3673379 prefixEnd_3673379 1257472702088192414312629 := by
  unfold tailWord_3673379
  simp only [CollatzResearch.WordTrace]
  refine ⟨133979138958982721031375191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89319425972655147354250127 133979138958982721031375191)
  ·
    refine ⟨200968708438474081547062787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133979138958982721031375191 200968708438474081547062787)
    ·
      refine ⟨301453062657711122320594181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200968708438474081547062787 301453062657711122320594181)
      ·
        refine ⟨56522449248320835435111409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301453062657711122320594181 56522449248320835435111409)
        ·
          refine ⟨42391836936240626576333557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56522449248320835435111409 42391836936240626576333557)
          ·
            refine ⟨3974234712772558741531271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42391836936240626576333557 3974234712772558741531271)
            ·
              refine ⟨5961352069158838112296907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974234712772558741531271 5961352069158838112296907)
              ·
                refine ⟨8942028103738257168445361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961352069158838112296907 8942028103738257168445361)
                ·
                  refine ⟨6706521077803692876334021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8942028103738257168445361 6706521077803692876334021)
                  ·
                    refine ⟨1257472702088192414312629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706521077803692876334021 1257472702088192414312629)
                    ·
                      rfl

theorem cell22_3673379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].length) (baseStart_3673379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673379 prefixEnd_3673379 := by exact prefixLift 3673379
  have htrace : WordTrace (prefixWord ++ tailWord_3673379) baseStart_3673379 baseEnd_3673379 := by
    simpa [prefixWord, tailWord_3673379, baseEnd_3673379] using wordTrace_append hprefix tailTrace_3673379
  have hstable : (prefixWord ++ tailWord_3673379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673379).length < 2 ^ (prefixWord ++ tailWord_3673379).sum := by decide
  have hdescent : baseEnd_3673379 < baseStart_3673379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673392 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_3673392 : Nat := 118140960795 + 3673392 * 2 ^ 59
def prefixEnd_3673392 : Nat := 4983230072969 + 3 ^ 40 * 3673392 * 2
def baseEnd_3673392 : Nat := 1257477152253864713737589

theorem tailTrace_3673392 : CollatzResearch.WordTrace tailWord_3673392 prefixEnd_3673392 1257477152253864713737589 := by
  unfold tailWord_3673392
  simp only [CollatzResearch.WordTrace]
  refine ⟨66989806553967812125799215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89319742071957082834398953 66989806553967812125799215)
  ·
    refine ⟨100484709830951718188698823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66989806553967812125799215 100484709830951718188698823)
    ·
      refine ⟨150727064746427577283048235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100484709830951718188698823 150727064746427577283048235)
      ·
        refine ⟨226090597119641365924572353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150727064746427577283048235 226090597119641365924572353)
        ·
          refine ⟨169567947839731024443429265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226090597119641365924572353 169567947839731024443429265)
          ·
            refine ⟨127175960879798268332571949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169567947839731024443429265 127175960879798268332571949)
            ·
              refine ⟨47690985329924350624714481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127175960879798268332571949 47690985329924350624714481)
              ·
                refine ⟨35768238997443262968535861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47690985329924350624714481 35768238997443262968535861)
                ·
                  refine ⟨3353272406010305903300237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35768238997443262968535861 3353272406010305903300237)
                  ·
                    refine ⟨1257477152253864713737589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353272406010305903300237 1257477152253864713737589)
                    ·
                      rfl

theorem cell22_3673392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_3673392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673392 prefixEnd_3673392 := by exact prefixLift 3673392
  have htrace : WordTrace (prefixWord ++ tailWord_3673392) baseStart_3673392 baseEnd_3673392 := by
    simpa [prefixWord, tailWord_3673392, baseEnd_3673392] using wordTrace_append hprefix tailTrace_3673392
  have hstable : (prefixWord ++ tailWord_3673392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673392).length < 2 ^ (prefixWord ++ tailWord_3673392).sum := by decide
  have hdescent : baseEnd_3673392 < baseStart_3673392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673398 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3673398 : Nat := 118140960795 + 3673398 * 2 ^ 59
def prefixEnd_3673398 : Nat := 4983230072969 + 3 ^ 40 * 3673398 * 2
def baseEnd_3673398 : Nat := 1257479206176482698087571

theorem tailTrace_3673398 : CollatzResearch.WordTrace tailWord_3673398 prefixEnd_3673398 1257479206176482698087571 := by
  unfold tailWord_3673398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373739496619617954769803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89319887963942591517544565 8373739496619617954769803)
  ·
    refine ⟨12560609244929426932154705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8373739496619617954769803 12560609244929426932154705)
    ·
      refine ⟨9420456933697070199116029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12560609244929426932154705 9420456933697070199116029)
      ·
        refine ⟨3532671350136401324668511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9420456933697070199116029 3532671350136401324668511)
        ·
          refine ⟨5299007025204601987002767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532671350136401324668511 5299007025204601987002767)
          ·
            refine ⟨7948510537806902980504151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299007025204601987002767 7948510537806902980504151)
            ·
              refine ⟨11922765806710354470756227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948510537806902980504151 11922765806710354470756227)
              ·
                refine ⟨17884148710065531706134341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11922765806710354470756227 17884148710065531706134341)
                ·
                  refine ⟨3353277883137287194900189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17884148710065531706134341 3353277883137287194900189)
                  ·
                    refine ⟨1257479206176482698087571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353277883137287194900189 1257479206176482698087571)
                    ·
                      rfl

theorem cell22_3673398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3673398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673398 prefixEnd_3673398 := by exact prefixLift 3673398
  have htrace : WordTrace (prefixWord ++ tailWord_3673398) baseStart_3673398 baseEnd_3673398 := by
    simpa [prefixWord, tailWord_3673398, baseEnd_3673398] using wordTrace_append hprefix tailTrace_3673398
  have hstable : (prefixWord ++ tailWord_3673398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673398).length < 2 ^ (prefixWord ++ tailWord_3673398).sum := by decide
  have hdescent : baseEnd_3673398 < baseStart_3673398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673443 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 1, 3]
def baseStart_3673443 : Nat := 118140960795 + 3673443 * 2 ^ 59
def prefixEnd_3673443 : Nat := 4983230072969 + 3 ^ 40 * 3673443 * 2
def baseEnd_3673443 : Nat := 1257494610596117580712433

theorem tailTrace_3673443 : CollatzResearch.WordTrace tailWord_3673443 prefixEnd_3673443 1257494610596117580712433 := by
  unfold tailWord_3673443
  simp only [CollatzResearch.WordTrace]
  refine ⟨133981473230750859961704983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89320982153833906641136655 133981473230750859961704983)
  ·
    refine ⟨200972209846126289942557475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133981473230750859961704983 200972209846126289942557475)
    ·
      refine ⟨301458314769189434913836213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200972209846126289942557475 301458314769189434913836213)
      ·
        refine ⟨28261717009611509523172145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301458314769189434913836213 28261717009611509523172145)
        ·
          refine ⟨21196287757208632142379109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28261717009611509523172145 21196287757208632142379109)
          ·
            refine ⟨3974303954476618526696083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21196287757208632142379109 3974303954476618526696083)
            ·
              refine ⟨5961455931714927790044125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974303954476618526696083 5961455931714927790044125)
              ·
                refine ⟨2235545974393097921266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5961455931714927790044125 2235545974393097921266547)
                ·
                  refine ⟨3353318961589646881899821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235545974393097921266547 3353318961589646881899821)
                  ·
                    refine ⟨1257494610596117580712433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353318961589646881899821 1257494610596117580712433)
                    ·
                      rfl

theorem cell22_3673443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 3].length) (baseStart_3673443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673443 prefixEnd_3673443 := by exact prefixLift 3673443
  have htrace : WordTrace (prefixWord ++ tailWord_3673443) baseStart_3673443 baseEnd_3673443 := by
    simpa [prefixWord, tailWord_3673443, baseEnd_3673443] using wordTrace_append hprefix tailTrace_3673443
  have hstable : (prefixWord ++ tailWord_3673443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673443).length < 2 ^ (prefixWord ++ tailWord_3673443).sum := by decide
  have hdescent : baseEnd_3673443 < baseStart_3673443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673473 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 5]
def baseStart_3673473 : Nat := 118140960795 + 3673473 * 2 ^ 59
def prefixEnd_3673473 : Nat := 4983230072969 + 3 ^ 40 * 3673473 * 2
def baseEnd_3673473 : Nat := 419168293403069167487447

theorem tailTrace_3673473 : CollatzResearch.WordTrace tailWord_3673473 prefixEnd_3673473 419168293403069167487447 := by
  unfold tailWord_3673473
  simp only [CollatzResearch.WordTrace]
  refine ⟨133982567420642175085297073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89321711613761450056864715 133982567420642175085297073)
  ·
    refine ⟨100486925565481631313972805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133982567420642175085297073 100486925565481631313972805)
    ·
      refine ⟨18841298543527805871369901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100486925565481631313972805 18841298543527805871369901)
      ·
        refine ⟨7065486953822927201763713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18841298543527805871369901 7065486953822927201763713)
        ·
          refine ⟨5299115215367195401322785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065486953822927201763713 5299115215367195401322785)
          ·
            refine ⟨3974336411525396550992089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5299115215367195401322785 3974336411525396550992089)
            ·
              refine ⟨2980752308644047413244067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974336411525396550992089 2980752308644047413244067)
              ·
                refine ⟨4471128462966071119866101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980752308644047413244067 4471128462966071119866101)
                ·
                  refine ⟨419168293403069167487447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4471128462966071119866101 419168293403069167487447)
                  ·
                    rfl

theorem cell22_3673473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_3673473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673473 prefixEnd_3673473 := by exact prefixLift 3673473
  have htrace : WordTrace (prefixWord ++ tailWord_3673473) baseStart_3673473 baseEnd_3673473 := by
    simpa [prefixWord, tailWord_3673473, baseEnd_3673473] using wordTrace_append hprefix tailTrace_3673473
  have hstable : (prefixWord ++ tailWord_3673473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673473).length < 2 ^ (prefixWord ++ tailWord_3673473).sum := by decide
  have hdescent : baseEnd_3673473 < baseStart_3673473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673486 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3673486 : Nat := 118140960795 + 3673486 * 2 ^ 59
def prefixEnd_3673486 : Nat := 4983230072969 + 3 ^ 40 * 3673486 * 2
def baseEnd_3673486 : Nat := 1257509330374879801887301

theorem tailTrace_3673486 : CollatzResearch.WordTrace tailWord_3673486 prefixEnd_3673486 1257509330374879801887301 := by
  unfold tailWord_3673486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747880196199384788190039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89322027713063385537013541 16747880196199384788190039)
  ·
    refine ⟨25121820294299077182285059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16747880196199384788190039 25121820294299077182285059)
    ·
      refine ⟨37682730441448615773427589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25121820294299077182285059 37682730441448615773427589)
      ·
        refine ⟨7065511957771615457517673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37682730441448615773427589 7065511957771615457517673)
        ·
          refine ⟨5299133968328711593138255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065511957771615457517673 5299133968328711593138255)
          ·
            refine ⟨7948700952493067389707383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299133968328711593138255 7948700952493067389707383)
            ·
              refine ⟨11923051428739601084561075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948700952493067389707383 11923051428739601084561075)
              ·
                refine ⟨17884577143109401626841613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923051428739601084561075 17884577143109401626841613)
                ·
                  refine ⟨6706716428666025610065605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17884577143109401626841613 6706716428666025610065605)
                  ·
                    refine ⟨1257509330374879801887301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706716428666025610065605 1257509330374879801887301)
                    ·
                      rfl

theorem cell22_3673486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3673486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673486 prefixEnd_3673486 := by exact prefixLift 3673486
  have htrace : WordTrace (prefixWord ++ tailWord_3673486) baseStart_3673486 baseEnd_3673486 := by
    simpa [prefixWord, tailWord_3673486, baseEnd_3673486] using wordTrace_append hprefix tailTrace_3673486
  have hstable : (prefixWord ++ tailWord_3673486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673486).length < 2 ^ (prefixWord ++ tailWord_3673486).sum := by decide
  have hdescent : baseEnd_3673486 < baseStart_3673486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673578 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3673578 : Nat := 118140960795 + 3673578 * 2 ^ 59
def prefixEnd_3673578 : Nat := 4983230072969 + 3 ^ 40 * 3673578 * 2
def baseEnd_3673578 : Nat := 1257540823855022228587019

theorem tailTrace_3673578 : CollatzResearch.WordTrace tailWord_3673578 prefixEnd_3673578 1257540823855022228587019 := by
  unfold tailWord_3673578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33496599271315444504467347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89324264723507852011912925 33496599271315444504467347)
  ·
    refine ⟨50244898906973166756701021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33496599271315444504467347 50244898906973166756701021)
    ·
      refine ⟨18841837090114937533762883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50244898906973166756701021 18841837090114937533762883)
      ·
        refine ⟨28262755635172406300644325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18841837090114937533762883 28262755635172406300644325)
        ·
          refine ⟨5299266681594826181370811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28262755635172406300644325 5299266681594826181370811)
          ·
            refine ⟨7948900022392239272056217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299266681594826181370811 7948900022392239272056217)
            ·
              refine ⟨5961675016794179454042163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948900022392239272056217 5961675016794179454042163)
              ·
                refine ⟨8942512525191269181063245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961675016794179454042163 8942512525191269181063245)
                ·
                  refine ⟨3353442196946725942898717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8942512525191269181063245 3353442196946725942898717)
                  ·
                    refine ⟨1257540823855022228587019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353442196946725942898717 1257540823855022228587019)
                    ·
                      rfl

theorem cell22_3673578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3673578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673578 prefixEnd_3673578 := by exact prefixLift 3673578
  have htrace : WordTrace (prefixWord ++ tailWord_3673578) baseStart_3673578 baseEnd_3673578 := by
    simpa [prefixWord, tailWord_3673578, baseEnd_3673578] using wordTrace_append hprefix tailTrace_3673578
  have hstable : (prefixWord ++ tailWord_3673578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673578).length < 2 ^ (prefixWord ++ tailWord_3673578).sum := by decide
  have hdescent : baseEnd_3673578 < baseStart_3673578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673587 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_3673587 : Nat := 118140960795 + 3673587 * 2 ^ 59
def prefixEnd_3673587 : Nat := 4983230072969 + 3 ^ 40 * 3673587 * 2
def baseEnd_3673587 : Nat := 1257543904738949205111991

theorem tailTrace_3673587 : CollatzResearch.WordTrace tailWord_3673587 prefixEnd_3673587 1257543904738949205111991 := by
  unfold tailWord_3673587
  simp only [CollatzResearch.WordTrace]
  refine ⟨133986725342229172554947015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89324483561486115036631343 133986725342229172554947015)
  ·
    refine ⟨200980088013343758832420523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133986725342229172554947015 200980088013343758832420523)
    ·
      refine ⟨301470132020015638248630785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200980088013343758832420523 301470132020015638248630785)
      ·
        refine ⟨226102599015011728686473089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301470132020015638248630785 226102599015011728686473089)
        ·
          refine ⟨169576949261258796514854817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226102599015011728686473089 169576949261258796514854817)
          ·
            refine ⟨127182711945944097386141113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169576949261258796514854817 127182711945944097386141113)
            ·
              refine ⟨95387033959458073039605835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127182711945944097386141113 95387033959458073039605835)
              ·
                refine ⟨143080550939187109559408753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95387033959458073039605835 143080550939187109559408753)
                ·
                  refine ⟨107310413204390332169556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143080550939187109559408753 107310413204390332169556565)
                  ·
                    refine ⟨1257543904738949205111991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107310413204390332169556565 1257543904738949205111991)
                    ·
                      rfl

theorem cell22_3673587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_3673587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673587 prefixEnd_3673587 := by exact prefixLift 3673587
  have htrace : WordTrace (prefixWord ++ tailWord_3673587) baseStart_3673587 baseEnd_3673587 := by
    simpa [prefixWord, tailWord_3673587, baseEnd_3673587] using wordTrace_append hprefix tailTrace_3673587
  have hstable : (prefixWord ++ tailWord_3673587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673587).length < 2 ^ (prefixWord ++ tailWord_3673587).sum := by decide
  have hdescent : baseEnd_3673587 < baseStart_3673587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673612 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_3673612 : Nat := 118140960795 + 3673612 * 2 ^ 59
def prefixEnd_3673612 : Nat := 4983230072969 + 3 ^ 40 * 3673612 * 2
def baseEnd_3673612 : Nat := 1257552462749857473236915

theorem tailTrace_3673612 : CollatzResearch.WordTrace tailWord_3673612 prefixEnd_3673612 1257552462749857473236915 := by
  unfold tailWord_3673612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66993818583569300912303545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89325091444759067883071393 66993818583569300912303545)
  ·
    refine ⟨50245363937676975684227659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66993818583569300912303545 50245363937676975684227659)
    ·
      refine ⟨75368045906515463526341489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50245363937676975684227659 75368045906515463526341489)
      ·
        refine ⟨56526034429886597644756117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75368045906515463526341489 56526034429886597644756117)
        ·
          refine ⟨2649657863900934264597943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56526034429886597644756117 2649657863900934264597943)
          ·
            refine ⟨3974486795851401396896915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649657863900934264597943 3974486795851401396896915)
            ·
              refine ⟨5961730193777102095345373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974486795851401396896915 5961730193777102095345373)
              ·
                refine ⟨2235648822666413285754515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5961730193777102095345373 2235648822666413285754515)
                ·
                  refine ⟨3353473233999619928631773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235648822666413285754515 3353473233999619928631773)
                  ·
                    refine ⟨1257552462749857473236915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353473233999619928631773 1257552462749857473236915)
                    ·
                      rfl

theorem cell22_3673612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_3673612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673612 prefixEnd_3673612 := by exact prefixLift 3673612
  have htrace : WordTrace (prefixWord ++ tailWord_3673612) baseStart_3673612 baseEnd_3673612 := by
    simpa [prefixWord, tailWord_3673612, baseEnd_3673612] using wordTrace_append hprefix tailTrace_3673612
  have hstable : (prefixWord ++ tailWord_3673612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673612).length < 2 ^ (prefixWord ++ tailWord_3673612).sum := by decide
  have hdescent : baseEnd_3673612 < baseStart_3673612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673621 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3673621 : Nat := 118140960795 + 3673621 * 2 ^ 59
def prefixEnd_3673621 : Nat := 4983230072969 + 3 ^ 40 * 3673621 * 2
def baseEnd_3673621 : Nat := 1257555543633784449761887

theorem tailTrace_3673621 : CollatzResearch.WordTrace tailWord_3673621 prefixEnd_3673621 1257555543633784449761887 := by
  unfold tailWord_3673621
  simp only [CollatzResearch.WordTrace]
  refine ⟨133987965424105996361684717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89325310282737330907789811 133987965424105996361684717)
  ·
    refine ⟨50245487034039748635631769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133987965424105996361684717 50245487034039748635631769)
    ·
      refine ⟨37684115275529811476723827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50245487034039748635631769 37684115275529811476723827)
      ·
        refine ⟨56526172913294717215085741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37684115275529811476723827 56526172913294717215085741)
        ·
          refine ⟨21197314842485518955657153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56526172913294717215085741 21197314842485518955657153)
          ·
            refine ⟨15897986131864139216742865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21197314842485518955657153 15897986131864139216742865)
            ·
              refine ⟨11923489598898104412557149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15897986131864139216742865 11923489598898104412557149)
              ·
                refine ⟨4471308599586789154708931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11923489598898104412557149 4471308599586789154708931)
                ·
                  refine ⟨6706962899380183732063397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471308599586789154708931 6706962899380183732063397)
                  ·
                    refine ⟨1257555543633784449761887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706962899380183732063397 1257555543633784449761887)
                    ·
                      rfl

theorem cell22_3673621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3673621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673621 prefixEnd_3673621 := by exact prefixLift 3673621
  have htrace : WordTrace (prefixWord ++ tailWord_3673621) baseStart_3673621 baseEnd_3673621 := by
    simpa [prefixWord, tailWord_3673621, baseEnd_3673621] using wordTrace_append hprefix tailTrace_3673621
  have hstable : (prefixWord ++ tailWord_3673621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673621).length < 2 ^ (prefixWord ++ tailWord_3673621).sum := by decide
  have hdescent : baseEnd_3673621 < baseStart_3673621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673649 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3673649 : Nat := 118140960795 + 3673649 * 2 ^ 59
def prefixEnd_3673649 : Nat := 4983230072969 + 3 ^ 40 * 3673649 * 2
def baseEnd_3673649 : Nat := 1257565128606001710061801

theorem tailTrace_3673649 : CollatzResearch.WordTrace tailWord_3673649 prefixEnd_3673649 1257565128606001710061801 := by
  unfold tailWord_3673649
  simp only [CollatzResearch.WordTrace]
  refine ⟨133988986668004557143704001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89325991112003038095802667 133988986668004557143704001)
  ·
    refine ⟨100491740001003417857778001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133988986668004557143704001 100491740001003417857778001)
    ·
      refine ⟨75368805000752563393333501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100491740001003417857778001 75368805000752563393333501)
      ·
        refine ⟨28263301875282211272500063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75368805000752563393333501 28263301875282211272500063)
        ·
          refine ⟨42394952812923316908750095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28263301875282211272500063 42394952812923316908750095)
          ·
            refine ⟨63592429219384975363125143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42394952812923316908750095 63592429219384975363125143)
            ·
              refine ⟨95388643829077463044687715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63592429219384975363125143 95388643829077463044687715)
              ·
                refine ⟨143082965743616194567031573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95388643829077463044687715 143082965743616194567031573)
                ·
                  refine ⟨6707014019232009120329605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143082965743616194567031573 6707014019232009120329605)
                  ·
                    refine ⟨1257565128606001710061801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707014019232009120329605 1257565128606001710061801)
                    ·
                      rfl

theorem cell22_3673649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3673649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673649 prefixEnd_3673649 := by exact prefixLift 3673649
  have htrace : WordTrace (prefixWord ++ tailWord_3673649) baseStart_3673649 baseEnd_3673649 := by
    simpa [prefixWord, tailWord_3673649, baseEnd_3673649] using wordTrace_append hprefix tailTrace_3673649
  have hstable : (prefixWord ++ tailWord_3673649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673649).length < 2 ^ (prefixWord ++ tailWord_3673649).sum := by decide
  have hdescent : baseEnd_3673649 < baseStart_3673649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673696 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_3673696 : Nat := 118140960795 + 3673696 * 2 ^ 59
def prefixEnd_3673696 : Nat := 4983230072969 + 3 ^ 40 * 3673696 * 2
def baseEnd_3673696 : Nat := 1257581217666509254136657

theorem tailTrace_3673696 : CollatzResearch.WordTrace tailWord_3673696 prefixEnd_3673696 1257581217666509254136657 := by
  unfold tailWord_3673696
  simp only [CollatzResearch.WordTrace]
  refine ⟨66995350449417142085332471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89327133932556189447109961 66995350449417142085332471)
  ·
    refine ⟨100493025674125713127998707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66995350449417142085332471 100493025674125713127998707)
    ·
      refine ⟨150739538511188569691998061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100493025674125713127998707 150739538511188569691998061)
      ·
        refine ⟨56527326941695713634499273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150739538511188569691998061 56527326941695713634499273)
        ·
          refine ⟨42395495206271785225874455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56527326941695713634499273 42395495206271785225874455)
          ·
            refine ⟨63593242809407677838811683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42395495206271785225874455 63593242809407677838811683)
            ·
              refine ⟨95389864214111516758217525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63593242809407677838811683 95389864214111516758217525)
              ·
                refine ⟨8942799770072954696082893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95389864214111516758217525 8942799770072954696082893)
                ·
                  refine ⟨3353549913777358011031085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8942799770072954696082893 3353549913777358011031085)
                  ·
                    refine ⟨1257581217666509254136657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353549913777358011031085 1257581217666509254136657)
                    ·
                      rfl

theorem cell22_3673696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_3673696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673696 prefixEnd_3673696 := by exact prefixLift 3673696
  have htrace : WordTrace (prefixWord ++ tailWord_3673696) baseStart_3673696 baseEnd_3673696 := by
    simpa [prefixWord, tailWord_3673696, baseEnd_3673696] using wordTrace_append hprefix tailTrace_3673696
  have hstable : (prefixWord ++ tailWord_3673696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673696).length < 2 ^ (prefixWord ++ tailWord_3673696).sum := by decide
  have hdescent : baseEnd_3673696 < baseStart_3673696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673724 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3673724 : Nat := 118140960795 + 3673724 * 2 ^ 59
def prefixEnd_3673724 : Nat := 4983230072969 + 3 ^ 40 * 3673724 * 2
def baseEnd_3673724 : Nat := 1257590802638726514436571

theorem tailTrace_3673724 : CollatzResearch.WordTrace tailWord_3673724 prefixEnd_3673724 1257590802638726514436571 := by
  unfold tailWord_3673724
  simp only [CollatzResearch.WordTrace]
  refine ⟨66995861071366422476342113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89327814761821896635122817 66995861071366422476342113)
  ·
    refine ⟨50246895803524816857256585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66995861071366422476342113 50246895803524816857256585)
    ·
      refine ⟨37685171852643612642942439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50246895803524816857256585 37685171852643612642942439)
      ·
        refine ⟨56527757778965418964413659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37685171852643612642942439 56527757778965418964413659)
        ·
          refine ⟨84791636668448128446620489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56527757778965418964413659 84791636668448128446620489)
          ·
            refine ⟨63593727501336096334965367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84791636668448128446620489 63593727501336096334965367)
            ·
              refine ⟨95390591252004144502448051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63593727501336096334965367 95390591252004144502448051)
              ·
                refine ⟨143085886878006216753672077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95390591252004144502448051 143085886878006216753672077)
                ·
                  refine ⟨53657207579252331282627029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143085886878006216753672077 53657207579252331282627029)
                  ·
                    refine ⟨1257590802638726514436571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53657207579252331282627029 1257590802638726514436571)
                    ·
                      rfl

theorem cell22_3673724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3673724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673724 prefixEnd_3673724 := by exact prefixLift 3673724
  have htrace : WordTrace (prefixWord ++ tailWord_3673724) baseStart_3673724 baseEnd_3673724 := by
    simpa [prefixWord, tailWord_3673724, baseEnd_3673724] using wordTrace_append hprefix tailTrace_3673724
  have hstable : (prefixWord ++ tailWord_3673724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673724).length < 2 ^ (prefixWord ++ tailWord_3673724).sum := by decide
  have hdescent : baseEnd_3673724 < baseStart_3673724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673758 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3673758 : Nat := 118140960795 + 3673758 * 2 ^ 59
def prefixEnd_3673758 : Nat := 4983230072969 + 3 ^ 40 * 3673758 * 2
def baseEnd_3673758 : Nat := 1257602441533561759086467

theorem tailTrace_3673758 : CollatzResearch.WordTrace tailWord_3673758 prefixEnd_3673758 1257602441533561759086467 := by
  unfold tailWord_3673758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749120278076208594927741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89328641483073112506281285 16749120278076208594927741)
  ·
    refine ⟨6280920104278578223097903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16749120278076208594927741 6280920104278578223097903)
    ·
      refine ⟨9421380156417867334646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280920104278578223097903 9421380156417867334646855)
      ·
        refine ⟨14132070234626801001970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421380156417867334646855 14132070234626801001970283)
        ·
          refine ⟨21198105351940201502955425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14132070234626801001970283 21198105351940201502955425)
          ·
            refine ⟨15898579013955151127216569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21198105351940201502955425 15898579013955151127216569)
            ·
              refine ⟨11923934260466363345412427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15898579013955151127216569 11923934260466363345412427)
              ·
                refine ⟨17885901390699545018118641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923934260466363345412427 17885901390699545018118641)
                ·
                  refine ⟨13414426043024658763588981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17885901390699545018118641 13414426043024658763588981)
                  ·
                    refine ⟨1257602441533561759086467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13414426043024658763588981 1257602441533561759086467)
                    ·
                      rfl

theorem cell22_3673758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3673758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673758 prefixEnd_3673758 := by exact prefixLift 3673758
  have htrace : WordTrace (prefixWord ++ tailWord_3673758) baseStart_3673758 baseEnd_3673758 := by
    simpa [prefixWord, tailWord_3673758, baseEnd_3673758] using wordTrace_append hprefix tailTrace_3673758
  have hstable : (prefixWord ++ tailWord_3673758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673758).length < 2 ^ (prefixWord ++ tailWord_3673758).sum := by decide
  have hdescent : baseEnd_3673758 < baseStart_3673758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673805 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3673805 : Nat := 118140960795 + 3673805 * 2 ^ 59
def prefixEnd_3673805 : Nat := 4983230072969 + 3 ^ 40 * 3673805 * 2
def baseEnd_3673805 : Nat := 419206176864689767720441

theorem tailTrace_3673805 : CollatzResearch.WordTrace tailWord_3673805 prefixEnd_3673805 419206176864689767720441 := by
  unfold tailWord_3673805
  simp only [CollatzResearch.WordTrace]
  refine ⟨133994676455439395786382869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89329784303626263857588579 133994676455439395786382869)
  ·
    refine ⟨6281000458848721677486697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133994676455439395786382869 6281000458848721677486697)
    ·
      refine ⟨4710750344136541258115023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6281000458848721677486697 4710750344136541258115023)
      ·
        refine ⟨7066125516204811887172535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710750344136541258115023 7066125516204811887172535)
        ·
          refine ⟨10599188274307217830758803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066125516204811887172535 10599188274307217830758803)
          ·
            refine ⟨15898782411460826746138205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599188274307217830758803 15898782411460826746138205)
            ·
              refine ⟨5962043404297810029801827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15898782411460826746138205 5962043404297810029801827)
              ·
                refine ⟨8943065106446715044702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962043404297810029801827 8943065106446715044702741)
                ·
                  refine ⟨419206176864689767720441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8943065106446715044702741 419206176864689767720441)
                  ·
                    rfl

theorem cell22_3673805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3673805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673805 prefixEnd_3673805 := by exact prefixLift 3673805
  have htrace : WordTrace (prefixWord ++ tailWord_3673805) baseStart_3673805 baseEnd_3673805 := by
    simpa [prefixWord, tailWord_3673805, baseEnd_3673805] using wordTrace_append hprefix tailTrace_3673805
  have hstable : (prefixWord ++ tailWord_3673805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673805).length < 2 ^ (prefixWord ++ tailWord_3673805).sum := by decide
  have hdescent : baseEnd_3673805 < baseStart_3673805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673816 : List Nat := [2, 1, 2, 2, 3, 1, 4, 7]
def baseStart_3673816 : Nat := 118140960795 + 3673816 * 2 ^ 59
def prefixEnd_3673816 : Nat := 4983230072969 + 3 ^ 40 * 3673816 * 2
def baseEnd_3673816 : Nat := 139735810679874326792921

theorem tailTrace_3673816 : CollatzResearch.WordTrace tailWord_3673816 prefixEnd_3673816 139735810679874326792921 := by
  unfold tailWord_3673816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66997538829199772332516651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89330051772266363110022201 66997538829199772332516651)
  ·
    refine ⟨100496308243799658498774977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66997538829199772332516651 100496308243799658498774977)
    ·
      refine ⟨75372231182849743874081233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100496308243799658498774977 75372231182849743874081233)
      ·
        refine ⟨56529173387137307905560925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75372231182849743874081233 56529173387137307905560925)
        ·
          refine ⟨21198440020176490464585347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56529173387137307905560925 21198440020176490464585347)
          ·
            refine ⟨31797660030264735696878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21198440020176490464585347 31797660030264735696878021)
            ·
              refine ⟨5962061255674637943164629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31797660030264735696878021 5962061255674637943164629)
              ·
                refine ⟨139735810679874326792921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5962061255674637943164629 139735810679874326792921)
                ·
                  rfl

theorem cell22_3673816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_3673816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673816 prefixEnd_3673816 := by exact prefixLift 3673816
  have htrace : WordTrace (prefixWord ++ tailWord_3673816) baseStart_3673816 baseEnd_3673816 := by
    simpa [prefixWord, tailWord_3673816, baseEnd_3673816] using wordTrace_append hprefix tailTrace_3673816
  have hstable : (prefixWord ++ tailWord_3673816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673816).length < 2 ^ (prefixWord ++ tailWord_3673816).sum := by decide
  have hdescent : baseEnd_3673816 < baseStart_3673816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673886 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3673886 : Nat := 118140960795 + 3673886 * 2 ^ 59
def prefixEnd_3673886 : Nat := 4983230072969 + 3 ^ 40 * 3673886 * 2
def baseEnd_3673886 : Nat := 1257646258549412091886075

theorem tailTrace_3673886 : CollatzResearch.WordTrace tailWord_3673886 prefixEnd_3673886 1257646258549412091886075 := by
  unfold tailWord_3673886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749703846018243327510189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89331753845430631080054341 16749703846018243327510189)
  ·
    refine ⟨6281138942256841247816321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16749703846018243327510189 6281138942256841247816321)
    ·
      refine ⟨4710854206692630935862241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6281138942256841247816321 4710854206692630935862241)
      ·
        refine ⟨3533140655019473201896681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4710854206692630935862241 3533140655019473201896681)
        ·
          refine ⟨2649855491264604901422511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533140655019473201896681 2649855491264604901422511)
          ·
            refine ⟨3974783236896907352133767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649855491264604901422511 3974783236896907352133767)
            ·
              refine ⟨5962174855345361028200651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974783236896907352133767 5962174855345361028200651)
              ·
                refine ⟨8943262283018041542300977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962174855345361028200651 8943262283018041542300977)
                ·
                  refine ⟨6707446712263531156725733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943262283018041542300977 6707446712263531156725733)
                  ·
                    refine ⟨1257646258549412091886075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707446712263531156725733 1257646258549412091886075)
                    ·
                      rfl

theorem cell22_3673886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3673886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673886 prefixEnd_3673886 := by exact prefixLift 3673886
  have htrace : WordTrace (prefixWord ++ tailWord_3673886) baseStart_3673886 baseEnd_3673886 := by
    simpa [prefixWord, tailWord_3673886, baseEnd_3673886] using wordTrace_append hprefix tailTrace_3673886
  have hstable : (prefixWord ++ tailWord_3673886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673886).length < 2 ^ (prefixWord ++ tailWord_3673886).sum := by decide
  have hdescent : baseEnd_3673886 < baseStart_3673886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673910 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3673910 : Nat := 118140960795 + 3673910 * 2 ^ 59
def prefixEnd_3673910 : Nat := 4983230072969 + 3 ^ 40 * 3673910 * 2
def baseEnd_3673910 : Nat := 1257654474239884029286001

theorem tailTrace_3673910 : CollatzResearch.WordTrace tailWord_3673910 prefixEnd_3673910 1257654474239884029286001 := by
  unfold tailWord_3673910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374906632503687419934699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89332337413372665812636789 8374906632503687419934699)
  ·
    refine ⟨12562359948755531129902049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374906632503687419934699 12562359948755531129902049)
    ·
      refine ⟨9421769961566648347426537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562359948755531129902049 9421769961566648347426537)
      ·
        refine ⟨7066327471174986260569903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9421769961566648347426537 7066327471174986260569903)
        ·
          refine ⟨10599491206762479390854855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066327471174986260569903 10599491206762479390854855)
          ·
            refine ⟨15899236810143719086282283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599491206762479390854855 15899236810143719086282283)
            ·
              refine ⟨23848855215215578629423425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15899236810143719086282283 23848855215215578629423425)
              ·
                refine ⟨17886641411411683972067569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23848855215215578629423425 17886641411411683972067569)
                ·
                  refine ⟨13414981058558762979050677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17886641411411683972067569 13414981058558762979050677)
                  ·
                    refine ⟨1257654474239884029286001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13414981058558762979050677 1257654474239884029286001)
                    ·
                      rfl

theorem cell22_3673910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3673910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673910 prefixEnd_3673910 := by exact prefixLift 3673910
  have htrace : WordTrace (prefixWord ++ tailWord_3673910) baseStart_3673910 baseEnd_3673910 := by
    simpa [prefixWord, tailWord_3673910, baseEnd_3673910] using wordTrace_append hprefix tailTrace_3673910
  have hstable : (prefixWord ++ tailWord_3673910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673910).length < 2 ^ (prefixWord ++ tailWord_3673910).sum := by decide
  have hdescent : baseEnd_3673910 < baseStart_3673910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673923 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 6]
def baseStart_3673923 : Nat := 118140960795 + 3673923 * 2 ^ 59
def prefixEnd_3673923 : Nat := 4983230072969 + 3 ^ 40 * 3673923 * 2
def baseEnd_3673923 : Nat := 419219641468518776236987

theorem tailTrace_3673923 : CollatzResearch.WordTrace tailWord_3673923 prefixEnd_3673923 419219641468518776236987 := by
  unfold tailWord_3673923
  simp only [CollatzResearch.WordTrace]
  refine ⟨133998980269011901939178423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89332653512674601292785615 133998980269011901939178423)
  ·
    refine ⟨200998470403517852908767635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133998980269011901939178423 200998470403517852908767635)
    ·
      refine ⟨301497705605276779363151453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200998470403517852908767635 301497705605276779363151453)
      ·
        refine ⟨113061639601978792261181795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301497705605276779363151453 113061639601978792261181795)
        ·
          refine ⟨169592459402968188391772693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113061639601978792261181795 169592459402968188391772693)
          ·
            refine ⟨7949646534514133830864345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169592459402968188391772693 7949646534514133830864345)
            ·
              refine ⟨5962234900885600373148259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949646534514133830864345 5962234900885600373148259)
              ·
                refine ⟨8943352351328400559722389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962234900885600373148259 8943352351328400559722389)
                ·
                  refine ⟨419219641468518776236987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8943352351328400559722389 419219641468518776236987)
                  ·
                    rfl

theorem cell22_3673923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_3673923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673923 prefixEnd_3673923 := by exact prefixLift 3673923
  have htrace : WordTrace (prefixWord ++ tailWord_3673923) baseStart_3673923 baseEnd_3673923 := by
    simpa [prefixWord, tailWord_3673923, baseEnd_3673923] using wordTrace_append hprefix tailTrace_3673923
  have hstable : (prefixWord ++ tailWord_3673923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673923).length < 2 ^ (prefixWord ++ tailWord_3673923).sum := by decide
  have hdescent : baseEnd_3673923 < baseStart_3673923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673953 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3673953 : Nat := 118140960795 + 3673953 * 2 ^ 59
def prefixEnd_3673953 : Nat := 4983230072969 + 3 ^ 40 * 3673953 * 2
def baseEnd_3673953 : Nat := 1257669194018646250460869

theorem tailTrace_3673953 : CollatzResearch.WordTrace tailWord_3673953 prefixEnd_3673953 1257669194018646250460869 := by
  unfold tailWord_3673953
  simp only [CollatzResearch.WordTrace]
  refine ⟨134000074458903217062770513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89333382972602144708513675 134000074458903217062770513)
  ·
    refine ⟨100500055844177412797077885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134000074458903217062770513 100500055844177412797077885)
    ·
      refine ⟨37687520941566529798904207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100500055844177412797077885 37687520941566529798904207)
      ·
        refine ⟨56531281412349794698356311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37687520941566529798904207 56531281412349794698356311)
        ·
          refine ⟨84796922118524692047534467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56531281412349794698356311 84796922118524692047534467)
          ·
            refine ⟨127195383177787038071301701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84796922118524692047534467 127195383177787038071301701)
            ·
              refine ⟨23849134345835069638369069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127195383177787038071301701 23849134345835069638369069)
              ·
                refine ⟨8943425379688151114388401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23849134345835069638369069 8943425379688151114388401)
                ·
                  refine ⟨6707569034766113335791301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943425379688151114388401 6707569034766113335791301)
                  ·
                    refine ⟨1257669194018646250460869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707569034766113335791301 1257669194018646250460869)
                    ·
                      rfl

theorem cell22_3673953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3673953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673953 prefixEnd_3673953 := by exact prefixLift 3673953
  have htrace : WordTrace (prefixWord ++ tailWord_3673953) baseStart_3673953 baseEnd_3673953 := by
    simpa [prefixWord, tailWord_3673953, baseEnd_3673953] using wordTrace_append hprefix tailTrace_3673953
  have hstable : (prefixWord ++ tailWord_3673953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673953).length < 2 ^ (prefixWord ++ tailWord_3673953).sum := by decide
  have hdescent : baseEnd_3673953 < baseStart_3673953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673974 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3673974 : Nat := 118140960795 + 3673974 * 2 ^ 59
def prefixEnd_3673974 : Nat := 4983230072969 + 3 ^ 40 * 3673974 * 2
def baseEnd_3673974 : Nat := 419225460915936398561935

theorem tailTrace_3673974 : CollatzResearch.WordTrace tailWord_3673974 prefixEnd_3673974 419225460915936398561935 := by
  unfold tailWord_3673974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375052524489196103080311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89333893594551425099523317 8375052524489196103080311)
  ·
    refine ⟨12562578786733794154620467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8375052524489196103080311 12562578786733794154620467)
    ·
      refine ⟨18843868180100691231930701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12562578786733794154620467 18843868180100691231930701)
      ·
        refine ⟨7066450567537759211974013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18843868180100691231930701 7066450567537759211974013)
        ·
          refine ⟨2649918962826659704490255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7066450567537759211974013 2649918962826659704490255)
          ·
            refine ⟨3974878444239989556735383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649918962826659704490255 3974878444239989556735383)
            ·
              refine ⟨5962317666359984335103075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974878444239989556735383 5962317666359984335103075)
              ·
                refine ⟨8943476499539976502654613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962317666359984335103075 8943476499539976502654613)
                ·
                  refine ⟨419225460915936398561935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8943476499539976502654613 419225460915936398561935)
                  ·
                    rfl

theorem cell22_3673974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3673974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673974 prefixEnd_3673974 := by exact prefixLift 3673974
  have htrace : WordTrace (prefixWord ++ tailWord_3673974) baseStart_3673974 baseEnd_3673974 := by
    simpa [prefixWord, tailWord_3673974, baseEnd_3673974] using wordTrace_append hprefix tailTrace_3673974
  have hstable : (prefixWord ++ tailWord_3673974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673974).length < 2 ^ (prefixWord ++ tailWord_3673974).sum := by decide
  have hdescent : baseEnd_3673974 < baseStart_3673974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674043 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_3674043 : Nat := 118140960795 + 3674043 * 2 ^ 59
def prefixEnd_3674043 : Nat := 4983230072969 + 3 ^ 40 * 3674043 * 2
def baseEnd_3674043 : Nat := 1257700002857916015710593

theorem tailTrace_3674043 : CollatzResearch.WordTrace tailWord_3674043 prefixEnd_3674043 1257700002857916015710593 := by
  unfold tailWord_3674043
  simp only [CollatzResearch.WordTrace]
  refine ⟨134003357028577162433546783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89335571352384774955697855 134003357028577162433546783)
  ·
    refine ⟨201005035542865743650320175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134003357028577162433546783 201005035542865743650320175)
    ·
      refine ⟨301507553314298615475480263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201005035542865743650320175 301507553314298615475480263)
      ·
        refine ⟨452261329971447923213220395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301507553314298615475480263 452261329971447923213220395)
        ·
          refine ⟨678391994957171884819830593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452261329971447923213220395 678391994957171884819830593)
          ·
            refine ⟨508793996217878913614872945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678391994957171884819830593 508793996217878913614872945)
            ·
              refine ⟨381595497163409185211154709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508793996217878913614872945 381595497163409185211154709)
              ·
                refine ⟨17887288929534805556772877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381595497163409185211154709 17887288929534805556772877)
                ·
                  refine ⟨6707733348575552083789829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17887288929534805556772877 6707733348575552083789829)
                  ·
                    refine ⟨1257700002857916015710593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707733348575552083789829 1257700002857916015710593)
                    ·
                      rfl

theorem cell22_3674043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_3674043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674043 prefixEnd_3674043 := by exact prefixLift 3674043
  have htrace : WordTrace (prefixWord ++ tailWord_3674043) baseStart_3674043 baseEnd_3674043 := by
    simpa [prefixWord, tailWord_3674043, baseEnd_3674043] using wordTrace_append hprefix tailTrace_3674043
  have hstable : (prefixWord ++ tailWord_3674043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674043).length < 2 ^ (prefixWord ++ tailWord_3674043).sum := by decide
  have hdescent : baseEnd_3674043 < baseStart_3674043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674045 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3674045 : Nat := 118140960795 + 3674045 * 2 ^ 59
def prefixEnd_3674045 : Nat := 4983230072969 + 3 ^ 40 * 3674045 * 2
def baseEnd_3674045 : Nat := 1257700687498788677160587

theorem tailTrace_3674045 : CollatzResearch.WordTrace tailWord_3674045 prefixEnd_3674045 1257700687498788677160587 := by
  unfold tailWord_3674045
  simp only [CollatzResearch.WordTrace]
  refine ⟨134003429974569916775119589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89335619983046611183413059 134003429974569916775119589)
  ·
    refine ⟨25125643120231859395334923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134003429974569916775119589 25125643120231859395334923)
    ·
      refine ⟨37688464680347789093002385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25125643120231859395334923 37688464680347789093002385)
      ·
        refine ⟨28266348510260841819751789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37688464680347789093002385 28266348510260841819751789)
        ·
          refine ⟨10599880691347815682406921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28266348510260841819751789 10599880691347815682406921)
          ·
            refine ⟨7949910518510861761805191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10599880691347815682406921 7949910518510861761805191)
            ·
              refine ⟨11924865777766292642707787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949910518510861761805191 11924865777766292642707787)
              ·
                refine ⟨17887298666649438964061681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924865777766292642707787 17887298666649438964061681)
                ·
                  refine ⟨13415473999987079223046261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17887298666649438964061681 13415473999987079223046261)
                  ·
                    refine ⟨1257700687498788677160587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13415473999987079223046261 1257700687498788677160587)
                    ·
                      rfl

theorem cell22_3674045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3674045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674045 prefixEnd_3674045 := by exact prefixLift 3674045
  have htrace : WordTrace (prefixWord ++ tailWord_3674045) baseStart_3674045 baseEnd_3674045 := by
    simpa [prefixWord, tailWord_3674045, baseEnd_3674045] using wordTrace_append hprefix tailTrace_3674045
  have hstable : (prefixWord ++ tailWord_3674045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674045).length < 2 ^ (prefixWord ++ tailWord_3674045).sum := by decide
  have hdescent : baseEnd_3674045 < baseStart_3674045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674058 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_3674058 : Nat := 118140960795 + 3674058 * 2 ^ 59
def prefixEnd_3674058 : Nat := 4983230072969 + 3 ^ 40 * 3674058 * 2
def baseEnd_3674058 : Nat := 419235045888153658861849

theorem tailTrace_3674058 : CollatzResearch.WordTrace tailWord_3674058 prefixEnd_3674058 419235045888153658861849 := by
  unfold tailWord_3674058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500976030880704998835707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89335936082348546663561885 33500976030880704998835707)
  ·
    refine ⟨50251464046321057498253561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500976030880704998835707 50251464046321057498253561)
    ·
      refine ⟨37688598034740793123690171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50251464046321057498253561 37688598034740793123690171)
      ·
        refine ⟨56532897052111189685535257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37688598034740793123690171 56532897052111189685535257)
        ·
          refine ⟨42399672789083392264151443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56532897052111189685535257 42399672789083392264151443)
          ·
            refine ⟨63599509183625088396227165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42399672789083392264151443 63599509183625088396227165)
            ·
              refine ⟨23849815943859408148585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63599509183625088396227165 23849815943859408148585187)
              ·
                refine ⟨35774723915789112222877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23849815943859408148585187 35774723915789112222877781)
                ·
                  refine ⟨419235045888153658861849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35774723915789112222877781 419235045888153658861849)
                  ·
                    rfl

theorem cell22_3674058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_3674058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674058 prefixEnd_3674058 := by exact prefixLift 3674058
  have htrace : WordTrace (prefixWord ++ tailWord_3674058) baseStart_3674058 baseEnd_3674058 := by
    simpa [prefixWord, tailWord_3674058, baseEnd_3674058] using wordTrace_append hprefix tailTrace_3674058
  have hstable : (prefixWord ++ tailWord_3674058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674058).length < 2 ^ (prefixWord ++ tailWord_3674058).sum := by decide
  have hdescent : baseEnd_3674058 < baseStart_3674058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674060 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_3674060 : Nat := 118140960795 + 3674060 * 2 ^ 59
def prefixEnd_3674060 : Nat := 4983230072969 + 3 ^ 40 * 3674060 * 2
def baseEnd_3674060 : Nat := 1257705822305333638035541

theorem tailTrace_3674060 : CollatzResearch.WordTrace tailWord_3674060 prefixEnd_3674060 1257705822305333638035541 := by
  unfold tailWord_3674060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67001988534757787168457817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89335984713010382891277089 67001988534757787168457817)
  ·
    refine ⟨50251491401068340376343363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67001988534757787168457817 50251491401068340376343363)
    ·
      refine ⟨75377237101602510564515045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50251491401068340376343363 75377237101602510564515045)
      ·
        refine ⟨14133231956550470730846571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75377237101602510564515045 14133231956550470730846571)
        ·
          refine ⟨21199847934825706096269857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14133231956550470730846571 21199847934825706096269857)
          ·
            refine ⟨15899885951119279572202393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21199847934825706096269857 15899885951119279572202393)
            ·
              refine ⟨11924914463339459679151795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15899885951119279572202393 11924914463339459679151795)
              ·
                refine ⟨17887371695009189518727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924914463339459679151795 17887371695009189518727693)
                ·
                  refine ⟨6707764385628446069522885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17887371695009189518727693 6707764385628446069522885)
                  ·
                    refine ⟨1257705822305333638035541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707764385628446069522885 1257705822305333638035541)
                    ·
                      rfl

theorem cell22_3674060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_3674060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674060 prefixEnd_3674060 := by exact prefixLift 3674060
  have htrace : WordTrace (prefixWord ++ tailWord_3674060) baseStart_3674060 baseEnd_3674060 := by
    simpa [prefixWord, tailWord_3674060, baseEnd_3674060] using wordTrace_append hprefix tailTrace_3674060
  have hstable : (prefixWord ++ tailWord_3674060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674060).length < 2 ^ (prefixWord ++ tailWord_3674060).sum := by decide
  have hdescent : baseEnd_3674060 < baseStart_3674060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674244 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3674244 : Nat := 118140960795 + 3674244 * 2 ^ 59
def prefixEnd_3674244 : Nat := 4983230072969 + 3 ^ 40 * 3674244 * 2
def baseEnd_3674244 : Nat := 419256269755206163811659

theorem tailTrace_3674244 : CollatzResearch.WordTrace tailWord_3674244 prefixEnd_3674244 419256269755206163811659 := by
  unfold tailWord_3674244
  simp only [CollatzResearch.WordTrace]
  refine ⟨67005344050424486880806893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89340458733899315841075857 67005344050424486880806893)
  ·
    refine ⟨25127004018909182580302585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67005344050424486880806893 25127004018909182580302585)
    ·
      refine ⟨18845253014181886935226939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25127004018909182580302585 18845253014181886935226939)
      ·
        refine ⟨28267879521272830402840409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18845253014181886935226939 28267879521272830402840409)
        ·
          refine ⟨21200909640954622802130307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28267879521272830402840409 21200909640954622802130307)
          ·
            refine ⟨31801364461431934203195461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21200909640954622802130307 31801364461431934203195461)
            ·
              refine ⟨5962755836518487663099149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31801364461431934203195461 5962755836518487663099149)
              ·
                refine ⟨2236033438694432873662181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5962755836518487663099149 2236033438694432873662181)
                ·
                  refine ⟨419256269755206163811659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236033438694432873662181 419256269755206163811659)
                  ·
                    rfl

theorem cell22_3674244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3674244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674244 prefixEnd_3674244 := by exact prefixLift 3674244
  have htrace : WordTrace (prefixWord ++ tailWord_3674244) baseStart_3674244 baseEnd_3674244 := by
    simpa [prefixWord, tailWord_3674244, baseEnd_3674244] using wordTrace_append hprefix tailTrace_3674244
  have hstable : (prefixWord ++ tailWord_3674244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674244).length < 2 ^ (prefixWord ++ tailWord_3674244).sum := by decide
  have hdescent : baseEnd_3674244 < baseStart_3674244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674276 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3674276 : Nat := 118140960795 + 3674276 * 2 ^ 59
def prefixEnd_3674276 : Nat := 4983230072969 + 3 ^ 40 * 3674276 * 2
def baseEnd_3674276 : Nat := 1257779763519581074634879

theorem tailTrace_3674276 : CollatzResearch.WordTrace tailWord_3674276 prefixEnd_3674276 1257779763519581074634879 := by
  unfold tailWord_3674276
  simp only [CollatzResearch.WordTrace]
  refine ⟨67005927618366521613389341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89341236824488695484519121 67005927618366521613389341)
  ·
    refine ⟨25127222856887445605021003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67005927618366521613389341 25127222856887445605021003)
    ·
      refine ⟨37690834285331168407531505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25127222856887445605021003 37690834285331168407531505)
      ·
        refine ⟨28268125713998376305648629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37690834285331168407531505 28268125713998376305648629)
        ·
          refine ⟨2650136785687347778654559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28268125713998376305648629 2650136785687347778654559)
          ·
            refine ⟨3975205178531021667981839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650136785687347778654559 3975205178531021667981839)
            ·
              refine ⟨5962807767796532501972759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975205178531021667981839 5962807767796532501972759)
              ·
                refine ⟨8944211651694798752959139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962807767796532501972759 8944211651694798752959139)
                ·
                  refine ⟨13416317477542198129438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944211651694798752959139 13416317477542198129438709)
                  ·
                    refine ⟨1257779763519581074634879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13416317477542198129438709 1257779763519581074634879)
                    ·
                      rfl

theorem cell22_3674276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3674276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674276 prefixEnd_3674276 := by exact prefixLift 3674276
  have htrace : WordTrace (prefixWord ++ tailWord_3674276) baseStart_3674276 baseEnd_3674276 := by
    simpa [prefixWord, tailWord_3674276, baseEnd_3674276] using wordTrace_append hprefix tailTrace_3674276
  have hstable : (prefixWord ++ tailWord_3674276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674276).length < 2 ^ (prefixWord ++ tailWord_3674276).sum := by decide
  have hdescent : baseEnd_3674276 < baseStart_3674276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674306 : List Nat := [3, 5, 1, 1, 1, 3, 8]
def baseStart_3674306 : Nat := 118140960795 + 3674306 * 2 ^ 59
def prefixEnd_3674306 : Nat := 4983230072969 + 3 ^ 40 * 3674306 * 2
def baseEnd_3674306 : Nat := 46584816041950777643881

theorem tailTrace_3674306 : CollatzResearch.WordTrace tailWord_3674306 prefixEnd_3674306 46584816041950777643881 := by
  unfold tailWord_3674306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503237356656089587592693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89341966284416238900247181 33503237356656089587592693)
  ·
    refine ⟨3140928502186508398836815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33503237356656089587592693 3140928502186508398836815)
    ·
      refine ⟨4711392753279762598255223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3140928502186508398836815 4711392753279762598255223)
      ·
        refine ⟨7067089129919643897382835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711392753279762598255223 7067089129919643897382835)
        ·
          refine ⟨10600633694879465846074253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067089129919643897382835 10600633694879465846074253)
          ·
            refine ⟨3975237635579799692277845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10600633694879465846074253 3975237635579799692277845)
            ·
              refine ⟨46584816041950777643881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3975237635579799692277845 46584816041950777643881)
              ·
                rfl

theorem cell22_3674306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 8].length) (baseStart_3674306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674306 prefixEnd_3674306 := by exact prefixLift 3674306
  have htrace : WordTrace (prefixWord ++ tailWord_3674306) baseStart_3674306 baseEnd_3674306 := by
    simpa [prefixWord, tailWord_3674306, baseEnd_3674306] using wordTrace_append hprefix tailTrace_3674306
  have hstable : (prefixWord ++ tailWord_3674306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674306).length < 2 ^ (prefixWord ++ tailWord_3674306).sum := by decide
  have hdescent : baseEnd_3674306 < baseStart_3674306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674347 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_3674347 : Nat := 118140960795 + 3674347 * 2 ^ 59
def prefixEnd_3674347 : Nat := 4983230072969 + 3 ^ 40 * 3674347 * 2
def baseEnd_3674347 : Nat := 1257804068270560556109661

theorem tailTrace_3674347 : CollatzResearch.WordTrace tailWord_3674347 prefixEnd_3674347 1257804068270560556109661 := by
  unfold tailWord_3674347
  simp only [CollatzResearch.WordTrace]
  refine ⟨134014444819475822352613295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89342963212983881568408863 134014444819475822352613295)
  ·
    refine ⟨201021667229213733528919943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134014444819475822352613295 201021667229213733528919943)
    ·
      refine ⟨301532500843820600293379915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201021667229213733528919943 301532500843820600293379915)
      ·
        refine ⟨452298751265730900440069873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301532500843820600293379915 452298751265730900440069873)
        ·
          refine ⟨339224063449298175330052405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452298751265730900440069873 339224063449298175330052405)
          ·
            refine ⟨31802255948371703937192413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339224063449298175330052405 31802255948371703937192413)
            ·
              refine ⟨11925845980639388976447155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31802255948371703937192413 11925845980639388976447155)
              ·
                refine ⟨17888768970959083464670733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925845980639388976447155 17888768970959083464670733)
                ·
                  refine ⟨6708288364109656299251525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17888768970959083464670733 6708288364109656299251525)
                  ·
                    refine ⟨1257804068270560556109661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708288364109656299251525 1257804068270560556109661)
                    ·
                      rfl

theorem cell22_3674347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_3674347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674347 prefixEnd_3674347 := by exact prefixLift 3674347
  have htrace : WordTrace (prefixWord ++ tailWord_3674347) baseStart_3674347 baseEnd_3674347 := by
    simpa [prefixWord, tailWord_3674347, baseEnd_3674347] using wordTrace_append hprefix tailTrace_3674347
  have hstable : (prefixWord ++ tailWord_3674347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674347).length < 2 ^ (prefixWord ++ tailWord_3674347).sum := by decide
  have hdescent : baseEnd_3674347 < baseStart_3674347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674372 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3674372 : Nat := 118140960795 + 3674372 * 2 ^ 59
def prefixEnd_3674372 : Nat := 4983230072969 + 3 ^ 40 * 3674372 * 2
def baseEnd_3674372 : Nat := 1257812626281468824234585

theorem tailTrace_3674372 : CollatzResearch.WordTrace tailWord_3674372 prefixEnd_3674372 1257812626281468824234585 := by
  unfold tailWord_3674372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67007678322192625811136685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89343571096256834414848913 67007678322192625811136685)
  ·
    refine ⟨25127879370822234679176257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67007678322192625811136685 25127879370822234679176257)
    ·
      refine ⟨18845909528116676009382193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25127879370822234679176257 18845909528116676009382193)
      ·
        refine ⟨14134432146087507007036645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18845909528116676009382193 14134432146087507007036645)
        ·
          refine ⟨2650206027391407563819371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14134432146087507007036645 2650206027391407563819371)
          ·
            refine ⟨3975309041087111345729057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650206027391407563819371 3975309041087111345729057)
            ·
              refine ⟨2981481780815333509296793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975309041087111345729057 2981481780815333509296793)
              ·
                refine ⟨2236111335611500131972595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981481780815333509296793 2236111335611500131972595)
                ·
                  refine ⟨3354167003417250197958893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236111335611500131972595 3354167003417250197958893)
                  ·
                    refine ⟨1257812626281468824234585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354167003417250197958893 1257812626281468824234585)
                    ·
                      rfl

theorem cell22_3674372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3674372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674372 prefixEnd_3674372 := by exact prefixLift 3674372
  have htrace : WordTrace (prefixWord ++ tailWord_3674372) baseStart_3674372 baseEnd_3674372 := by
    simpa [prefixWord, tailWord_3674372, baseEnd_3674372] using wordTrace_append hprefix tailTrace_3674372
  have hstable : (prefixWord ++ tailWord_3674372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674372).length < 2 ^ (prefixWord ++ tailWord_3674372).sum := by decide
  have hdescent : baseEnd_3674372 < baseStart_3674372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674379 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 4]
def baseStart_3674379 : Nat := 118140960795 + 3674379 * 2 ^ 59
def prefixEnd_3674379 : Nat := 4983230072969 + 3 ^ 40 * 3674379 * 2
def baseEnd_3674379 : Nat := 419271674174841046436521

theorem tailTrace_3674379 : CollatzResearch.WordTrace tailWord_3674379 prefixEnd_3674379 419271674174841046436521 := by
  unfold tailWord_3674379
  simp only [CollatzResearch.WordTrace]
  refine ⟨134015611955359891817778191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89343741303573261211852127 134015611955359891817778191)
  ·
    refine ⟨201023417933039837726667287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134015611955359891817778191 201023417933039837726667287)
    ·
      refine ⟨301535126899559756590000931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201023417933039837726667287 301535126899559756590000931)
      ·
        refine ⟨452302690349339634885001397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301535126899559756590000931 452302690349339634885001397)
        ·
          refine ⟨42403377220250590770468881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452302690349339634885001397 42403377220250590770468881)
          ·
            refine ⟨31802532915187943077851661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42403377220250590770468881 31802532915187943077851661)
            ·
              refine ⟨11925949843195478654194373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31802532915187943077851661 11925949843195478654194373)
              ·
                refine ⟨2236115595599152247661445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11925949843195478654194373 2236115595599152247661445)
                ·
                  refine ⟨419271674174841046436521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236115595599152247661445 419271674174841046436521)
                  ·
                    rfl

theorem cell22_3674379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 4].length) (baseStart_3674379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674379 prefixEnd_3674379 := by exact prefixLift 3674379
  have htrace : WordTrace (prefixWord ++ tailWord_3674379) baseStart_3674379 baseEnd_3674379 := by
    simpa [prefixWord, tailWord_3674379, baseEnd_3674379] using wordTrace_append hprefix tailTrace_3674379
  have hstable : (prefixWord ++ tailWord_3674379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674379).length < 2 ^ (prefixWord ++ tailWord_3674379).sum := by decide
  have hdescent : baseEnd_3674379 < baseStart_3674379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674392 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_3674392 : Nat := 118140960795 + 3674392 * 2 ^ 59
def prefixEnd_3674392 : Nat := 4983230072969 + 3 ^ 40 * 3674392 * 2
def baseEnd_3674392 : Nat := 1257819472690195438734523

theorem tailTrace_3674392 : CollatzResearch.WordTrace tailWord_3674392 prefixEnd_3674392 1257819472690195438734523 := by
  unfold tailWord_3674392
  simp only [CollatzResearch.WordTrace]
  refine ⟨67008043052156397519000715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89344057402875196692000953 67008043052156397519000715)
  ·
    refine ⟨100512064578234596278501073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67008043052156397519000715 100512064578234596278501073)
    ·
      refine ⟨75384048433675947208875805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100512064578234596278501073 75384048433675947208875805)
      ·
        refine ⟨28269018162628480203328427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75384048433675947208875805 28269018162628480203328427)
        ·
          refine ⟨42403527243942720304992641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269018162628480203328427 42403527243942720304992641)
          ·
            refine ⟨31802645432957040228744481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42403527243942720304992641 31802645432957040228744481)
            ·
              refine ⟨23851984074717780171558361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31802645432957040228744481 23851984074717780171558361)
              ·
                refine ⟨17888988056038335128668771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23851984074717780171558361 17888988056038335128668771)
                ·
                  refine ⟨26833482084057502693003157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17888988056038335128668771 26833482084057502693003157)
                  ·
                    refine ⟨1257819472690195438734523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26833482084057502693003157 1257819472690195438734523)
                    ·
                      rfl

theorem cell22_3674392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_3674392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674392 prefixEnd_3674392 := by exact prefixLift 3674392
  have htrace : WordTrace (prefixWord ++ tailWord_3674392) baseStart_3674392 baseEnd_3674392 := by
    simpa [prefixWord, tailWord_3674392, baseEnd_3674392] using wordTrace_append hprefix tailTrace_3674392
  have hstable : (prefixWord ++ tailWord_3674392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674392).length < 2 ^ (prefixWord ++ tailWord_3674392).sum := by decide
  have hdescent : baseEnd_3674392 < baseStart_3674392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674578 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3674578 : Nat := 118140960795 + 3674578 * 2 ^ 59
def prefixEnd_3674578 : Nat := 4983230072969 + 3 ^ 40 * 3674578 * 2
def baseEnd_3674578 : Nat := 1257883144291352953583953

theorem tailTrace_3674578 : CollatzResearch.WordTrace tailWord_3674578 prefixEnd_3674578 1257883144291352953583953 := by
  unfold tailWord_3674578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505717520409737201068097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89348580054425965869514925 33505717520409737201068097)
  ·
    refine ⟨25129288140307302900801073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33505717520409737201068097 25129288140307302900801073)
    ·
      refine ⟨18846966105230477175600805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129288140307302900801073 18846966105230477175600805)
      ·
        refine ⟨3533806144730714470425151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18846966105230477175600805 3533806144730714470425151)
        ·
          refine ⟨5300709217096071705637727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533806144730714470425151 5300709217096071705637727)
          ·
            refine ⟨7951063825644107558456591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300709217096071705637727 7951063825644107558456591)
            ·
              refine ⟨11926595738466161337684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951063825644107558456591 11926595738466161337684887)
              ·
                refine ⟨17889893607699242006527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926595738466161337684887 17889893607699242006527331)
                ·
                  refine ⟨26834840411548863009790997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17889893607699242006527331 26834840411548863009790997)
                  ·
                    refine ⟨1257883144291352953583953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26834840411548863009790997 1257883144291352953583953)
                    ·
                      rfl

theorem cell22_3674578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3674578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674578 prefixEnd_3674578 := by exact prefixLift 3674578
  have htrace : WordTrace (prefixWord ++ tailWord_3674578) baseStart_3674578 baseEnd_3674578 := by
    simpa [prefixWord, tailWord_3674578, baseEnd_3674578] using wordTrace_append hprefix tailTrace_3674578
  have hstable : (prefixWord ++ tailWord_3674578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674578).length < 2 ^ (prefixWord ++ tailWord_3674578).sum := by decide
  have hdescent : baseEnd_3674578 < baseStart_3674578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674597 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_3674597 : Nat := 118140960795 + 3674597 * 2 ^ 59
def prefixEnd_3674597 : Nat := 4983230072969 + 3 ^ 40 * 3674597 * 2
def baseEnd_3674597 : Nat := 1257889648379643237358895

theorem tailTrace_3674597 : CollatzResearch.WordTrace tailWord_3674597 prefixEnd_3674597 1257889648379643237358895 := by
  unfold tailWord_3674597
  simp only [CollatzResearch.WordTrace]
  refine ⟨134023563068570115049214045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89349042045713410032809363 134023563068570115049214045)
  ·
    refine ⟨50258836150713793143455267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134023563068570115049214045 50258836150713793143455267)
    ·
      refine ⟨75388254226070689715182901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50258836150713793143455267 75388254226070689715182901)
      ·
        refine ⟨7067648833694127160798397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75388254226070689715182901 7067648833694127160798397)
        ·
          refine ⟨2650368312635297685299399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7067648833694127160798397 2650368312635297685299399)
          ·
            refine ⟨3975552468952946527949099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650368312635297685299399 3975552468952946527949099)
            ·
              refine ⟨5963328703429419791923649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975552468952946527949099 5963328703429419791923649)
              ·
                refine ⟨4472496527572064843942737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963328703429419791923649 4472496527572064843942737)
                ·
                  refine ⟨3354372395679048632957053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472496527572064843942737 3354372395679048632957053)
                  ·
                    refine ⟨1257889648379643237358895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354372395679048632957053 1257889648379643237358895)
                    ·
                      rfl

theorem cell22_3674597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_3674597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674597 prefixEnd_3674597 := by exact prefixLift 3674597
  have htrace : WordTrace (prefixWord ++ tailWord_3674597) baseStart_3674597 baseEnd_3674597 := by
    simpa [prefixWord, tailWord_3674597, baseEnd_3674597] using wordTrace_append hprefix tailTrace_3674597
  have hstable : (prefixWord ++ tailWord_3674597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674597).length < 2 ^ (prefixWord ++ tailWord_3674597).sum := by decide
  have hdescent : baseEnd_3674597 < baseStart_3674597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674604 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_3674604 : Nat := 118140960795 + 3674604 * 2 ^ 59
def prefixEnd_3674604 : Nat := 4983230072969 + 3 ^ 40 * 3674604 * 2
def baseEnd_3674604 : Nat := 419297348207565850811291

theorem tailTrace_3674604 : CollatzResearch.WordTrace tailWord_3674604 prefixEnd_3674604 419297348207565850811291 := by
  unfold tailWord_3674604
  simp only [CollatzResearch.WordTrace]
  refine ⟨67011909189772377622359433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89349212253029836829812577 67011909189772377622359433)
  ·
    refine ⟨50258931892329283216769575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67011909189772377622359433 50258931892329283216769575)
    ·
      refine ⟨75388397838493924825154363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50258931892329283216769575 75388397838493924825154363)
      ·
        refine ⟨113082596757740887237731545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75388397838493924825154363 113082596757740887237731545)
        ·
          refine ⟨84811947568305665428298659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113082596757740887237731545 84811947568305665428298659)
          ·
            refine ⟨127217921352458498142447989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84811947568305665428298659 127217921352458498142447989)
            ·
              refine ⟨11926680126792984200854499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127217921352458498142447989 11926680126792984200854499)
              ·
                refine ⟨17890020190189476301281749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926680126792984200854499 17890020190189476301281749)
                ·
                  refine ⟨419297348207565850811291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17890020190189476301281749 419297348207565850811291)
                  ·
                    rfl

theorem cell22_3674604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_3674604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674604 prefixEnd_3674604 := by exact prefixLift 3674604
  have htrace : WordTrace (prefixWord ++ tailWord_3674604) baseStart_3674604 baseEnd_3674604 := by
    simpa [prefixWord, tailWord_3674604, baseEnd_3674604] using wordTrace_append hprefix tailTrace_3674604
  have hstable : (prefixWord ++ tailWord_3674604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674604).length < 2 ^ (prefixWord ++ tailWord_3674604).sum := by decide
  have hdescent : baseEnd_3674604 < baseStart_3674604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674608 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_3674608 : Nat := 118140960795 + 3674608 * 2 ^ 59
def prefixEnd_3674608 : Nat := 4983230072969 + 3 ^ 40 * 3674608 * 2
def baseEnd_3674608 : Nat := 1257893413904442875333861

theorem tailTrace_3674608 : CollatzResearch.WordTrace tailWord_3674608 prefixEnd_3674608 1257893413904442875333861 := by
  unfold tailWord_3674608
  simp only [CollatzResearch.WordTrace]
  refine ⟨67011982135765131963932239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89349309514353509285242985 67011982135765131963932239)
  ·
    refine ⟨100517973203647697945898359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67011982135765131963932239 100517973203647697945898359)
    ·
      refine ⟨150776959805471546918847539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100517973203647697945898359 150776959805471546918847539)
      ·
        refine ⟨226165439708207320378271309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150776959805471546918847539 226165439708207320378271309)
        ·
          refine ⟨84812039890577745141851741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226165439708207320378271309 84812039890577745141851741)
          ·
            refine ⟨31804514958966654428194403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84812039890577745141851741 31804514958966654428194403)
            ·
              refine ⟨47706772438449981642291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31804514958966654428194403 47706772438449981642291605)
              ·
                refine ⟨2236254958052342889482419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47706772438449981642291605 2236254958052342889482419)
                ·
                  refine ⟨3354382437078514334223629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236254958052342889482419 3354382437078514334223629)
                  ·
                    refine ⟨1257893413904442875333861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354382437078514334223629 1257893413904442875333861)
                    ·
                      rfl

theorem cell22_3674608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_3674608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674608 prefixEnd_3674608 := by exact prefixLift 3674608
  have htrace : WordTrace (prefixWord ++ tailWord_3674608) baseStart_3674608 baseEnd_3674608 := by
    simpa [prefixWord, tailWord_3674608, baseEnd_3674608] using wordTrace_append hprefix tailTrace_3674608
  have hstable : (prefixWord ++ tailWord_3674608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674608).length < 2 ^ (prefixWord ++ tailWord_3674608).sum := by decide
  have hdescent : baseEnd_3674608 < baseStart_3674608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674681 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_3674681 : Nat := 118140960795 + 3674681 * 2 ^ 59
def prefixEnd_3674681 : Nat := 4983230072969 + 3 ^ 40 * 3674681 * 2
def baseEnd_3674681 : Nat := 1257918403296295018258637

theorem tailTrace_3674681 : CollatzResearch.WordTrace tailWord_3674681 prefixEnd_3674681 1257918403296295018258637 := by
  unfold tailWord_3674681
  simp only [CollatzResearch.WordTrace]
  refine ⟨134026626800265797395271897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89351084533510531596847931 134026626800265797395271897)
  ·
    refine ⟨100519970100199348046453923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134026626800265797395271897 100519970100199348046453923)
    ·
      refine ⟨150779955150299022069680885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100519970100199348046453923 150779955150299022069680885)
      ·
        refine ⟨14135620795340533319032583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150779955150299022069680885 14135620795340533319032583)
        ·
          refine ⟨21203431193010799978548875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135620795340533319032583 21203431193010799978548875)
          ·
            refine ⟨31805146789516199967823313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21203431193010799978548875 31805146789516199967823313)
            ·
              refine ⟨23853860092137149975867485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31805146789516199967823313 23853860092137149975867485)
              ·
                refine ⟨8945197534551431240950307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23853860092137149975867485 8945197534551431240950307)
                ·
                  refine ⟨13417796301827146861425461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945197534551431240950307 13417796301827146861425461)
                  ·
                    refine ⟨1257918403296295018258637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13417796301827146861425461 1257918403296295018258637)
                    ·
                      rfl

theorem cell22_3674681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_3674681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674681 prefixEnd_3674681 := by exact prefixLift 3674681
  have htrace : WordTrace (prefixWord ++ tailWord_3674681) baseStart_3674681 baseEnd_3674681 := by
    simpa [prefixWord, tailWord_3674681, baseEnd_3674681] using wordTrace_append hprefix tailTrace_3674681
  have hstable : (prefixWord ++ tailWord_3674681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674681).length < 2 ^ (prefixWord ++ tailWord_3674681).sum := by decide
  have hdescent : baseEnd_3674681 < baseStart_3674681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674685 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3674685 : Nat := 118140960795 + 3674685 * 2 ^ 59
def prefixEnd_3674685 : Nat := 4983230072969 + 3 ^ 40 * 3674685 * 2
def baseEnd_3674685 : Nat := 1257919772578040341158625

theorem tailTrace_3674685 : CollatzResearch.WordTrace tailWord_3674685 prefixEnd_3674685 1257919772578040341158625 := by
  unfold tailWord_3674685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134026772692251306078417509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89351181794834204052278339 134026772692251306078417509)
  ·
    refine ⟨25130019879797119889703283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134026772692251306078417509 25130019879797119889703283)
    ·
      refine ⟨37695029819695679834554925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25130019879797119889703283 37695029819695679834554925)
      ·
        refine ⟨14135636182385879937958097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37695029819695679834554925 14135636182385879937958097)
        ·
          refine ⟨10601727136789409953468573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14135636182385879937958097 10601727136789409953468573)
          ·
            refine ⟨3975647676296028732550715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10601727136789409953468573 3975647676296028732550715)
            ·
              refine ⟨5963471514444043098826073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975647676296028732550715 5963471514444043098826073)
              ·
                refine ⟨4472603635833032324119555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963471514444043098826073 4472603635833032324119555)
                ·
                  refine ⟨6708905453749548486179333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472603635833032324119555 6708905453749548486179333)
                  ·
                    refine ⟨1257919772578040341158625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708905453749548486179333 1257919772578040341158625)
                    ·
                      rfl

theorem cell22_3674685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3674685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674685 prefixEnd_3674685 := by exact prefixLift 3674685
  have htrace : WordTrace (prefixWord ++ tailWord_3674685) baseStart_3674685 baseEnd_3674685 := by
    simpa [prefixWord, tailWord_3674685, baseEnd_3674685] using wordTrace_append hprefix tailTrace_3674685
  have hstable : (prefixWord ++ tailWord_3674685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674685).length < 2 ^ (prefixWord ++ tailWord_3674685).sum := by decide
  have hdescent : baseEnd_3674685 < baseStart_3674685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674803 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 1, 4]
def baseStart_3674803 : Nat := 118140960795 + 3674803 * 2 ^ 59
def prefixEnd_3674803 : Nat := 4983230072969 + 3 ^ 40 * 3674803 * 2
def baseEnd_3674803 : Nat := 1257960166389527366708263

theorem tailTrace_3674803 : CollatzResearch.WordTrace tailWord_3674803 prefixEnd_3674803 1257960166389527366708263 := by
  unfold tailWord_3674803
  simp only [CollatzResearch.WordTrace]
  refine ⟨134031076505823812231213063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89354051003882541487475375 134031076505823812231213063)
  ·
    refine ⟨201046614758735718346819595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134031076505823812231213063 201046614758735718346819595)
    ·
      refine ⟨301569922138103577520229393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201046614758735718346819595 301569922138103577520229393)
      ·
        refine ⟨226177441603577683140172045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301569922138103577520229393 226177441603577683140172045)
        ·
          refine ⟨84816540601341631177564517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226177441603577683140172045 84816540601341631177564517)
          ·
            refine ⟨15903101362751555845793347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84816540601341631177564517 15903101362751555845793347)
            ·
              refine ⟨23854652044127333768690021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903101362751555845793347 23854652044127333768690021)
              ·
                refine ⟨4472747258273875081629379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23854652044127333768690021 4472747258273875081629379)
                ·
                  refine ⟨6709120887410812622444069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472747258273875081629379 6709120887410812622444069)
                  ·
                    refine ⟨1257960166389527366708263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709120887410812622444069 1257960166389527366708263)
                    ·
                      rfl

theorem cell22_3674803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_3674803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674803 prefixEnd_3674803 := by exact prefixLift 3674803
  have htrace : WordTrace (prefixWord ++ tailWord_3674803) baseStart_3674803 baseEnd_3674803 := by
    simpa [prefixWord, tailWord_3674803, baseEnd_3674803] using wordTrace_append hprefix tailTrace_3674803
  have hstable : (prefixWord ++ tailWord_3674803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674803).length < 2 ^ (prefixWord ++ tailWord_3674803).sum := by decide
  have hdescent : baseEnd_3674803 < baseStart_3674803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674820 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3674820 : Nat := 118140960795 + 3674820 * 2 ^ 59
def prefixEnd_3674820 : Nat := 4983230072969 + 3 ^ 40 * 3674820 * 2
def baseEnd_3674820 : Nat := 1257965985836944989033211

theorem tailTrace_3674820 : CollatzResearch.WordTrace tailWord_3674820 prefixEnd_3674820 1257965985836944989033211 := by
  unfold tailWord_3674820
  simp only [CollatzResearch.WordTrace]
  refine ⟨67015848273381112067290957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89354464364508149423054609 67015848273381112067290957)
  ·
    refine ⟨25130943102517917025234109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67015848273381112067290957 25130943102517917025234109)
    ·
      refine ⟨9424103663444218884462791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25130943102517917025234109 9424103663444218884462791)
      ·
        refine ⟨14136155495166328326694187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424103663444218884462791 14136155495166328326694187)
        ·
          refine ⟨21204233242749492490041281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14136155495166328326694187 21204233242749492490041281)
          ·
            refine ⟨15903174932062119367530961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21204233242749492490041281 15903174932062119367530961)
            ·
              refine ⟨11927381199046589525648221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15903174932062119367530961 11927381199046589525648221)
              ·
                refine ⟨4472767949642471072118083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11927381199046589525648221 4472767949642471072118083)
                ·
                  refine ⟨6709151924463706608177125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472767949642471072118083 6709151924463706608177125)
                  ·
                    refine ⟨1257965985836944989033211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709151924463706608177125 1257965985836944989033211)
                    ·
                      rfl

theorem cell22_3674820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3674820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674820 prefixEnd_3674820 := by exact prefixLift 3674820
  have htrace : WordTrace (prefixWord ++ tailWord_3674820) baseStart_3674820 baseEnd_3674820 := by
    simpa [prefixWord, tailWord_3674820, baseEnd_3674820] using wordTrace_append hprefix tailTrace_3674820
  have hstable : (prefixWord ++ tailWord_3674820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674820).length < 2 ^ (prefixWord ++ tailWord_3674820).sum := by decide
  have hdescent : baseEnd_3674820 < baseStart_3674820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674833 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_3674833 : Nat := 118140960795 + 3674833 * 2 ^ 59
def prefixEnd_3674833 : Nat := 4983230072969 + 3 ^ 40 * 3674833 * 2
def baseEnd_3674833 : Nat := 1257970436002617288458171

theorem tailTrace_3674833 : CollatzResearch.WordTrace tailWord_3674833 prefixEnd_3674833 1257970436002617288458171 := by
  unfold tailWord_3674833
  simp only [CollatzResearch.WordTrace]
  refine ⟨134032170695715127354805153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89354780463810084903203435 134032170695715127354805153)
  ·
    refine ⟨100524128021786345516103865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134032170695715127354805153 100524128021786345516103865)
    ·
      refine ⟨75393096016339759137077899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100524128021786345516103865 75393096016339759137077899)
      ·
        refine ⟨113089644024509638705616849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75393096016339759137077899 113089644024509638705616849)
        ·
          refine ⟨84817233018382229029212637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113089644024509638705616849 84817233018382229029212637)
          ·
            refine ⟨31806462381893335885954739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84817233018382229029212637 31806462381893335885954739)
            ·
              refine ⟨47709693572840003828932109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31806462381893335885954739 47709693572840003828932109)
              ·
                refine ⟨17891135089815001435849541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47709693572840003828932109 17891135089815001435849541)
                ·
                  refine ⟨3354587829340312769221789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17891135089815001435849541 3354587829340312769221789)
                  ·
                    refine ⟨1257970436002617288458171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354587829340312769221789 1257970436002617288458171)
                    ·
                      rfl

theorem cell22_3674833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_3674833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674833 prefixEnd_3674833 := by exact prefixLift 3674833
  have htrace : WordTrace (prefixWord ++ tailWord_3674833) baseStart_3674833 baseEnd_3674833 := by
    simpa [prefixWord, tailWord_3674833, baseEnd_3674833] using wordTrace_append hprefix tailTrace_3674833
  have hstable : (prefixWord ++ tailWord_3674833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674833).length < 2 ^ (prefixWord ++ tailWord_3674833).sum := by decide
  have hdescent : baseEnd_3674833 < baseStart_3674833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674953 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 6]
def baseStart_3674953 : Nat := 118140960795 + 3674953 * 2 ^ 59
def prefixEnd_3674953 : Nat := 4983230072969 + 3 ^ 40 * 3674953 * 2
def baseEnd_3674953 : Nat := 419337171484992325152601

theorem tailTrace_3674953 : CollatzResearch.WordTrace tailWord_3674953 prefixEnd_3674953 419337171484992325152601 := by
  unfold tailWord_3674953
  simp only [CollatzResearch.WordTrace]
  refine ⟨134036547455280387849173513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89357698303520258566115675 134036547455280387849173513)
  ·
    refine ⟨100527410591460290886880135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134036547455280387849173513 100527410591460290886880135)
    ·
      refine ⟨150791115887190436330320203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100527410591460290886880135 150791115887190436330320203)
      ·
        refine ⟨226186673830785654495480305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150791115887190436330320203 226186673830785654495480305)
        ·
          refine ⟨169640005373089240871610229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226186673830785654495480305 169640005373089240871610229)
          ·
            refine ⟨15903750503727116331713459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169640005373089240871610229 15903750503727116331713459)
            ·
              refine ⟨23855625755590674497570189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903750503727116331713459 23855625755590674497570189)
              ·
                refine ⟨8945859658346502936588821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23855625755590674497570189 8945859658346502936588821)
                ·
                  refine ⟨419337171484992325152601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8945859658346502936588821 419337171484992325152601)
                  ·
                    rfl

theorem cell22_3674953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_3674953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674953 prefixEnd_3674953 := by exact prefixLift 3674953
  have htrace : WordTrace (prefixWord ++ tailWord_3674953) baseStart_3674953 baseEnd_3674953 := by
    simpa [prefixWord, tailWord_3674953, baseEnd_3674953] using wordTrace_append hprefix tailTrace_3674953
  have hstable : (prefixWord ++ tailWord_3674953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674953).length < 2 ^ (prefixWord ++ tailWord_3674953).sum := by decide
  have hdescent : baseEnd_3674953 < baseStart_3674953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674972 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3674972 : Nat := 118140960795 + 3674972 * 2 ^ 59
def prefixEnd_3674972 : Nat := 4983230072969 + 3 ^ 40 * 3674972 * 2
def baseEnd_3674972 : Nat := 1258018018543267259232745

theorem tailTrace_3674972 : CollatzResearch.WordTrace tailWord_3674972 prefixEnd_3674972 1258018018543267259232745 := by
  unfold tailWord_3674972
  simp only [CollatzResearch.WordTrace]
  refine ⟨67018620221105777047057585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89358160294807702729410113 67018620221105777047057585)
  ·
    refine ⟨50263965165829332785293189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67018620221105777047057585 50263965165829332785293189)
    ·
      refine ⟨9424493468592999897242473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50263965165829332785293189 9424493468592999897242473)
      ·
        refine ⟨7068370101444749922931855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424493468592999897242473 7068370101444749922931855)
        ·
          refine ⟨10602555152167124884397783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068370101444749922931855 10602555152167124884397783)
          ·
            refine ⟨15903832728250687326596675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602555152167124884397783 15903832728250687326596675)
            ·
              refine ⟨23855749092376030989895013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903832728250687326596675 23855749092376030989895013)
              ·
                refine ⟨4472952954820505810605315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23855749092376030989895013 4472952954820505810605315)
                ·
                  refine ⟨6709429432230758715907973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472952954820505810605315 6709429432230758715907973)
                  ·
                    refine ⟨1258018018543267259232745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709429432230758715907973 1258018018543267259232745)
                    ·
                      rfl

theorem cell22_3674972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3674972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3674972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3674972 prefixEnd_3674972 := by exact prefixLift 3674972
  have htrace : WordTrace (prefixWord ++ tailWord_3674972) baseStart_3674972 baseEnd_3674972 := by
    simpa [prefixWord, tailWord_3674972, baseEnd_3674972] using wordTrace_append hprefix tailTrace_3674972
  have hstable : (prefixWord ++ tailWord_3674972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674972).length < 2 ^ (prefixWord ++ tailWord_3674972).sum := by decide
  have hdescent : baseEnd_3674972 < baseStart_3674972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675015 : List Nat := [1, 1, 4, 2, 3, 2, 2, 7]
def baseStart_3675015 : Nat := 118140960795 + 3675015 * 2 ^ 59
def prefixEnd_3675015 : Nat := 4983230072969 + 3 ^ 40 * 3675015 * 2
def baseEnd_3675015 : Nat := 139781415369114386711957

theorem tailTrace_3675015 : CollatzResearch.WordTrace tailWord_3675015 prefixEnd_3675015 139781415369114386711957 := by
  unfold tailWord_3675015
  simp only [CollatzResearch.WordTrace]
  refine ⟨134038808781055772437930499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89359205854037181625286999 134038808781055772437930499)
  ·
    refine ⟨201058213171583658656895749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134038808781055772437930499 201058213171583658656895749)
    ·
      refine ⟨37698414969671935998167953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201058213171583658656895749 37698414969671935998167953)
      ·
        refine ⟨28273811227253951998625965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37698414969671935998167953 28273811227253951998625965)
        ·
          refine ⟨10602679210220231999484737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28273811227253951998625965 10602679210220231999484737)
          ·
            refine ⟨7952009407665173999613553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10602679210220231999484737 7952009407665173999613553)
            ·
              refine ⟨5964007055748880499710165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952009407665173999613553 5964007055748880499710165)
              ·
                refine ⟨139781415369114386711957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5964007055748880499710165 139781415369114386711957)
                ·
                  rfl

theorem cell22_3675015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 7].length) (baseStart_3675015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675015 prefixEnd_3675015 := by exact prefixLift 3675015
  have htrace : WordTrace (prefixWord ++ tailWord_3675015) baseStart_3675015 baseEnd_3675015 := by
    simpa [prefixWord, tailWord_3675015, baseEnd_3675015] using wordTrace_append hprefix tailTrace_3675015
  have hstable : (prefixWord ++ tailWord_3675015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675015).length < 2 ^ (prefixWord ++ tailWord_3675015).sum := by decide
  have hdescent : baseEnd_3675015 < baseStart_3675015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675043 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 9]
def baseStart_3675043 : Nat := 118140960795 + 3675043 * 2 ^ 59
def prefixEnd_3675043 : Nat := 4983230072969 + 3 ^ 40 * 3675043 * 2
def baseEnd_3675043 : Nat := 419347441098082246902509

theorem tailTrace_3675043 : CollatzResearch.WordTrace tailWord_3675043 prefixEnd_3675043 419347441098082246902509 := by
  unfold tailWord_3675043
  simp only [CollatzResearch.WordTrace]
  refine ⟨134039830024954333219949783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89359886683302888813299855 134039830024954333219949783)
  ·
    refine ⟨201059745037431499829924675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134039830024954333219949783 201059745037431499829924675)
    ·
      refine ⟨301589617556147249744887013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201059745037431499829924675 301589617556147249744887013)
      ·
        refine ⟨56548053291777609327166315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301589617556147249744887013 56548053291777609327166315)
        ·
          refine ⟨84822079937666413990749473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56548053291777609327166315 84822079937666413990749473)
          ·
            refine ⟨63616559953249810493062105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84822079937666413990749473 63616559953249810493062105)
            ·
              refine ⟨47712419964937357869796579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63616559953249810493062105 47712419964937357869796579)
              ·
                refine ⟨71568629947406036804694869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47712419964937357869796579 71568629947406036804694869)
                ·
                  refine ⟨419347441098082246902509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71568629947406036804694869 419347441098082246902509)
                  ·
                    rfl

theorem cell22_3675043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_3675043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675043 prefixEnd_3675043 := by exact prefixLift 3675043
  have htrace : WordTrace (prefixWord ++ tailWord_3675043) baseStart_3675043 baseEnd_3675043 := by
    simpa [prefixWord, tailWord_3675043, baseEnd_3675043] using wordTrace_append hprefix tailTrace_3675043
  have hstable : (prefixWord ++ tailWord_3675043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675043).length < 2 ^ (prefixWord ++ tailWord_3675043).sum := by decide
  have hdescent : baseEnd_3675043 < baseStart_3675043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675064 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_3675064 : Nat := 118140960795 + 3675064 * 2 ^ 59
def prefixEnd_3675064 : Nat := 4983230072969 + 3 ^ 40 * 3675064 * 2
def baseEnd_3675064 : Nat := 1258049512023409685932463

theorem tailTrace_3675064 : CollatzResearch.WordTrace tailWord_3675064 prefixEnd_3675064 1258049512023409685932463 := by
  unfold tailWord_3675064
  simp only [CollatzResearch.WordTrace]
  refine ⟨67020297978939126903232123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89360397305252169204309497 67020297978939126903232123)
  ·
    refine ⟨100530446968408690354848185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67020297978939126903232123 100530446968408690354848185)
    ·
      refine ⟨75397835226306517766136139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100530446968408690354848185 75397835226306517766136139)
      ·
        refine ⟨113096752839459776649204209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75397835226306517766136139 113096752839459776649204209)
        ·
          refine ⟨84822564629594832486903157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113096752839459776649204209 84822564629594832486903157)
          ·
            refine ⟨7952115434024515545647171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84822564629594832486903157 7952115434024515545647171)
            ·
              refine ⟨11928173151036773318470757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952115434024515545647171 11928173151036773318470757)
              ·
                refine ⟨2236532465819394997213267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11928173151036773318470757 2236532465819394997213267)
                ·
                  refine ⟨3354798698729092495819901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236532465819394997213267 3354798698729092495819901)
                  ·
                    refine ⟨1258049512023409685932463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354798698729092495819901 1258049512023409685932463)
                    ·
                      rfl

theorem cell22_3675064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_3675064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675064 prefixEnd_3675064 := by exact prefixLift 3675064
  have htrace : WordTrace (prefixWord ++ tailWord_3675064) baseStart_3675064 baseEnd_3675064 := by
    simpa [prefixWord, tailWord_3675064, baseEnd_3675064] using wordTrace_append hprefix tailTrace_3675064
  have hstable : (prefixWord ++ tailWord_3675064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675064).length < 2 ^ (prefixWord ++ tailWord_3675064).sum := by decide
  have hdescent : baseEnd_3675064 < baseStart_3675064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675085 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3675085 : Nat := 118140960795 + 3675085 * 2 ^ 59
def prefixEnd_3675085 : Nat := 4983230072969 + 3 ^ 40 * 3675085 * 2
def baseEnd_3675085 : Nat := 1258056700752572631157399

theorem tailTrace_3675085 : CollatzResearch.WordTrace tailWord_3675085 prefixEnd_3675085 1258056700752572631157399 := by
  unfold tailWord_3675085
  simp only [CollatzResearch.WordTrace]
  refine ⟨134041361890802174392978709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89360907927201449595319139 134041361890802174392978709)
  ·
    refine ⟨6283188838631351924670877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134041361890802174392978709 6283188838631351924670877)
    ·
      refine ⟨2356195814486756971751579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6283188838631351924670877 2356195814486756971751579)
      ·
        refine ⟨3534293721730135457627369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356195814486756971751579 3534293721730135457627369)
        ·
          refine ⟨2650720291297601593220527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3534293721730135457627369 2650720291297601593220527)
          ·
            refine ⟨3976080436946402389830791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650720291297601593220527 3976080436946402389830791)
            ·
              refine ⟨5964120655419603584746187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976080436946402389830791 5964120655419603584746187)
              ·
                refine ⟨8946180983129405377119281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964120655419603584746187 8946180983129405377119281)
                ·
                  refine ⟨6709635737347054032839461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946180983129405377119281 6709635737347054032839461)
                  ·
                    refine ⟨1258056700752572631157399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709635737347054032839461 1258056700752572631157399)
                    ·
                      rfl

theorem cell22_3675085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3675085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675085 prefixEnd_3675085 := by exact prefixLift 3675085
  have htrace : WordTrace (prefixWord ++ tailWord_3675085) baseStart_3675085 baseEnd_3675085 := by
    simpa [prefixWord, tailWord_3675085, baseEnd_3675085] using wordTrace_append hprefix tailTrace_3675085
  have hstable : (prefixWord ++ tailWord_3675085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675085).length < 2 ^ (prefixWord ++ tailWord_3675085).sum := by decide
  have hdescent : baseEnd_3675085 < baseStart_3675085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675107 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 1, 4]
def baseStart_3675107 : Nat := 118140960795 + 3675107 * 2 ^ 59
def prefixEnd_3675107 : Nat := 4983230072969 + 3 ^ 40 * 3675107 * 2
def baseEnd_3675107 : Nat := 1258064231802171907107331

theorem tailTrace_3675107 : CollatzResearch.WordTrace tailWord_3675107 prefixEnd_3675107 1258064231802171907107331 := by
  unfold tailWord_3675107
  simp only [CollatzResearch.WordTrace]
  refine ⟨134042164296722472150279575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89361442864481648100186383 134042164296722472150279575)
  ·
    refine ⟨201063246445083708225419363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134042164296722472150279575 201063246445083708225419363)
    ·
      refine ⟨301594869667625562338129045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201063246445083708225419363 301594869667625562338129045)
      ·
        refine ⟨14137259515669948234599799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301594869667625562338129045 14137259515669948234599799)
        ·
          refine ⟨21205889273504922351899699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137259515669948234599799 21205889273504922351899699)
          ·
            refine ⟨31808833910257383527849549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21205889273504922351899699 31808833910257383527849549)
            ·
              refine ⟨11928312716346518822943581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31808833910257383527849549 11928312716346518822943581)
              ·
                refine ⟨4473117268629944558603843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11928312716346518822943581 4473117268629944558603843)
                ·
                  refine ⟨6709675902944916837905765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473117268629944558603843 6709675902944916837905765)
                  ·
                    refine ⟨1258064231802171907107331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709675902944916837905765 1258064231802171907107331)
                    ·
                      rfl

theorem cell22_3675107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_3675107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675107 prefixEnd_3675107 := by exact prefixLift 3675107
  have htrace : WordTrace (prefixWord ++ tailWord_3675107) baseStart_3675107 baseEnd_3675107 := by
    simpa [prefixWord, tailWord_3675107, baseEnd_3675107] using wordTrace_append hprefix tailTrace_3675107
  have hstable : (prefixWord ++ tailWord_3675107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675107).length < 2 ^ (prefixWord ++ tailWord_3675107).sum := by decide
  have hdescent : baseEnd_3675107 < baseStart_3675107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675137 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3675137 : Nat := 118140960795 + 3675137 * 2 ^ 59
def prefixEnd_3675137 : Nat := 4983230072969 + 3 ^ 40 * 3675137 * 2
def baseEnd_3675137 : Nat := 1258074501415261828857239

theorem tailTrace_3675137 : CollatzResearch.WordTrace tailWord_3675137 prefixEnd_3675137 1258074501415261828857239 := by
  unfold tailWord_3675137
  simp only [CollatzResearch.WordTrace]
  refine ⟨134043258486613787273871665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89362172324409191515914443 134043258486613787273871665)
  ·
    refine ⟨100532443864960340455403749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134043258486613787273871665 100532443864960340455403749)
    ·
      refine ⟨18849833224680063835388203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100532443864960340455403749 18849833224680063835388203)
      ·
        refine ⟨28274749837020095753082305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18849833224680063835388203 28274749837020095753082305)
        ·
          refine ⟨21206062377765071814811729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28274749837020095753082305 21206062377765071814811729)
          ·
            refine ⟨15904546783323803861108797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21206062377765071814811729 15904546783323803861108797)
            ·
              refine ⟨5964205043746426447915799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15904546783323803861108797 5964205043746426447915799)
              ·
                refine ⟨8946307565619639671873699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964205043746426447915799 8946307565619639671873699)
                ·
                  refine ⟨13419461348429459507810549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946307565619639671873699 13419461348429459507810549)
                  ·
                    refine ⟨1258074501415261828857239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13419461348429459507810549 1258074501415261828857239)
                    ·
                      rfl

theorem cell22_3675137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3675137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675137 prefixEnd_3675137 := by exact prefixLift 3675137
  have htrace : WordTrace (prefixWord ++ tailWord_3675137) baseStart_3675137 baseEnd_3675137 := by
    simpa [prefixWord, tailWord_3675137, baseEnd_3675137] using wordTrace_append hprefix tailTrace_3675137
  have hstable : (prefixWord ++ tailWord_3675137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675137).length < 2 ^ (prefixWord ++ tailWord_3675137).sum := by decide
  have hdescent : baseEnd_3675137 < baseStart_3675137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675180 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3675180 : Nat := 118140960795 + 3675180 * 2 ^ 59
def prefixEnd_3675180 : Nat := 4983230072969 + 3 ^ 40 * 3675180 * 2
def baseEnd_3675180 : Nat := 1258089221194024050032107

theorem tailTrace_3675180 : CollatzResearch.WordTrace tailWord_3675180 prefixEnd_3675180 1258089221194024050032107 := by
  unfold tailWord_3675180
  simp only [CollatzResearch.WordTrace]
  refine ⟨67022413412729002808843497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89363217883638670411791329 67022413412729002808843497)
  ·
    refine ⟨50266810059546752106632623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67022413412729002808843497 50266810059546752106632623)
    ·
      refine ⟨75400215089320128159948935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50266810059546752106632623 75400215089320128159948935)
      ·
        refine ⟨113100322633980192239923403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75400215089320128159948935 113100322633980192239923403)
        ·
          refine ⟨169650483950970288359885105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113100322633980192239923403 169650483950970288359885105)
          ·
            refine ⟨127237862963227716269913829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169650483950970288359885105 127237862963227716269913829)
            ·
              refine ⟨23857099305605196800608843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127237862963227716269913829 23857099305605196800608843)
              ·
                refine ⟨35785648958407795200913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23857099305605196800608843 35785648958407795200913265)
                ·
                  refine ⟨26839236718805846400684949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35785648958407795200913265 26839236718805846400684949)
                  ·
                    refine ⟨1258089221194024050032107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26839236718805846400684949 1258089221194024050032107)
                    ·
                      rfl

theorem cell22_3675180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3675180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675180 prefixEnd_3675180 := by exact prefixLift 3675180
  have htrace : WordTrace (prefixWord ++ tailWord_3675180) baseStart_3675180 baseEnd_3675180 := by
    simpa [prefixWord, tailWord_3675180, baseEnd_3675180] using wordTrace_append hprefix tailTrace_3675180
  have hstable : (prefixWord ++ tailWord_3675180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675180).length < 2 ^ (prefixWord ++ tailWord_3675180).sum := by decide
  have hdescent : baseEnd_3675180 < baseStart_3675180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675188 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3675188 : Nat := 118140960795 + 3675188 * 2 ^ 59
def prefixEnd_3675188 : Nat := 4983230072969 + 3 ^ 40 * 3675188 * 2
def baseEnd_3675188 : Nat := 1258091959757514695832083

theorem tailTrace_3675188 : CollatzResearch.WordTrace tailWord_3675188 prefixEnd_3675188 1258091959757514695832083 := by
  unfold tailWord_3675188
  simp only [CollatzResearch.WordTrace]
  refine ⟨67022559304714511491989109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89363412406286015322652145 67022559304714511491989109)
  ·
    refine ⟨6283364934816985452373979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67022559304714511491989109 6283364934816985452373979)
    ·
      refine ⟨9425047402225478178560969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283364934816985452373979 9425047402225478178560969)
      ·
        refine ⟨7068785551669108633920727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425047402225478178560969 7068785551669108633920727)
        ·
          refine ⟨10603178327503662950881091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068785551669108633920727 10603178327503662950881091)
          ·
            refine ⟨15904767491255494426321637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603178327503662950881091 15904767491255494426321637)
            ·
              refine ⟨2982143904610405204935307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15904767491255494426321637 2982143904610405204935307)
              ·
                refine ⟨4473215856915607807402961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982143904610405204935307 4473215856915607807402961)
                ·
                  refine ⟨3354911892686705855552221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473215856915607807402961 3354911892686705855552221)
                  ·
                    refine ⟨1258091959757514695832083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354911892686705855552221 1258091959757514695832083)
                    ·
                      rfl

theorem cell22_3675188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3675188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675188 prefixEnd_3675188 := by exact prefixLift 3675188
  have htrace : WordTrace (prefixWord ++ tailWord_3675188) baseStart_3675188 baseEnd_3675188 := by
    simpa [prefixWord, tailWord_3675188, baseEnd_3675188] using wordTrace_append hprefix tailTrace_3675188
  have hstable : (prefixWord ++ tailWord_3675188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675188).length < 2 ^ (prefixWord ++ tailWord_3675188).sum := by decide
  have hdescent : baseEnd_3675188 < baseStart_3675188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675306 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3675306 : Nat := 118140960795 + 3675306 * 2 ^ 59
def prefixEnd_3675306 : Nat := 4983230072969 + 3 ^ 40 * 3675306 * 2
def baseEnd_3675306 : Nat := 1258132353569001721381721

theorem tailTrace_3675306 : CollatzResearch.WordTrace tailWord_3675306 prefixEnd_3675306 1258132353569001721381721 := by
  unfold tailWord_3675306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33512355605750382284193443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89366281615334352757849181 33512355605750382284193443)
  ·
    refine ⟨50268533408625573426290165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33512355605750382284193443 50268533408625573426290165)
    ·
      refine ⟨4712675007058647508714703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50268533408625573426290165 4712675007058647508714703)
      ·
        refine ⟨7069012510587971263072055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4712675007058647508714703 7069012510587971263072055)
        ·
          refine ⟨10603518765881956894608083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069012510587971263072055 10603518765881956894608083)
          ·
            refine ⟨15905278148822935341912125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603518765881956894608083 15905278148822935341912125)
            ·
              refine ⟨5964479305808600753217047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15905278148822935341912125 5964479305808600753217047)
              ·
                refine ⟨8946718958712901129825571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964479305808600753217047 8946718958712901129825571)
                ·
                  refine ⟨13420078438069351694738357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946718958712901129825571 13420078438069351694738357)
                  ·
                    refine ⟨1258132353569001721381721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13420078438069351694738357 1258132353569001721381721)
                    ·
                      rfl

theorem cell22_3675306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3675306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675306 prefixEnd_3675306 := by exact prefixLift 3675306
  have htrace : WordTrace (prefixWord ++ tailWord_3675306) baseStart_3675306 baseEnd_3675306 := by
    simpa [prefixWord, tailWord_3675306, baseEnd_3675306] using wordTrace_append hprefix tailTrace_3675306
  have hstable : (prefixWord ++ tailWord_3675306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675306).length < 2 ^ (prefixWord ++ tailWord_3675306).sum := by decide
  have hdescent : baseEnd_3675306 < baseStart_3675306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675351 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 1, 3]
def baseStart_3675351 : Nat := 118140960795 + 3675351 * 2 ^ 59
def prefixEnd_3675351 : Nat := 4983230072969 + 3 ^ 40 * 3675351 * 2
def baseEnd_3675351 : Nat := 1258147757988636604006583

theorem tailTrace_3675351 : CollatzResearch.WordTrace tailWord_3675351 prefixEnd_3675351 1258147757988636604006583 := by
  unfold tailWord_3675351
  simp only [CollatzResearch.WordTrace]
  refine ⟨134051063707838501822161907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89367375805225667881441271 134051063707838501822161907)
  ·
    refine ⟨201076595561757752733242861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134051063707838501822161907 201076595561757752733242861)
    ·
      refine ⟨75403723335659157274966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201076595561757752733242861 75403723335659157274966073)
      ·
        refine ⟨56552792501744367956224555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75403723335659157274966073 56552792501744367956224555)
        ·
          refine ⟨84829188752616551934336833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56552792501744367956224555 84829188752616551934336833)
          ·
            refine ⟨63621891564462413950752625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84829188752616551934336833 63621891564462413950752625)
            ·
              refine ⟨47716418673346810463064469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63621891564462413950752625 47716418673346810463064469)
              ·
                refine ⟨2236707125313131740456147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47716418673346810463064469 2236707125313131740456147)
                ·
                  refine ⟨3355060687969697610684221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236707125313131740456147 3355060687969697610684221)
                  ·
                    refine ⟨1258147757988636604006583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355060687969697610684221 1258147757988636604006583)
                    ·
                      rfl

theorem cell22_3675351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_3675351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675351 prefixEnd_3675351 := by exact prefixLift 3675351
  have htrace : WordTrace (prefixWord ++ tailWord_3675351) baseStart_3675351 baseEnd_3675351 := by
    simpa [prefixWord, tailWord_3675351, baseEnd_3675351] using wordTrace_append hprefix tailTrace_3675351
  have hstable : (prefixWord ++ tailWord_3675351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675351).length < 2 ^ (prefixWord ++ tailWord_3675351).sum := by decide
  have hdescent : baseEnd_3675351 < baseStart_3675351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675357 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3675357 : Nat := 118140960795 + 3675357 * 2 ^ 59
def prefixEnd_3675357 : Nat := 4983230072969 + 3 ^ 40 * 3675357 * 2
def baseEnd_3675357 : Nat := 1258149811911254588356565

theorem tailTrace_3675357 : CollatzResearch.WordTrace tailWord_3675357 prefixEnd_3675357 1258149811911254588356565 := by
  unfold tailWord_3675357
  simp only [CollatzResearch.WordTrace]
  refine ⟨134051282545816764846880325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89367521697211176564586883 134051282545816764846880325)
  ·
    refine ⟨25134615477340643408790061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134051282545816764846880325 25134615477340643408790061)
    ·
      refine ⟨9425480804002741278296273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25134615477340643408790061 9425480804002741278296273)
      ·
        refine ⟨7069110603002055958722205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425480804002741278296273 7069110603002055958722205)
        ·
          refine ⟨2650916476125770984520827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7069110603002055958722205 2650916476125770984520827)
          ·
            refine ⟨3976374714188656476781241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650916476125770984520827 3976374714188656476781241)
            ·
              refine ⟨2982281035641492357585931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976374714188656476781241 2982281035641492357585931)
              ·
                refine ⟨4473421553462238536378897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982281035641492357585931 4473421553462238536378897)
                ·
                  refine ⟨3355066165096678902284173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473421553462238536378897 3355066165096678902284173)
                  ·
                    refine ⟨1258149811911254588356565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355066165096678902284173 1258149811911254588356565)
                    ·
                      rfl

theorem cell22_3675357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3675357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675357 prefixEnd_3675357 := by exact prefixLift 3675357
  have htrace : WordTrace (prefixWord ++ tailWord_3675357) baseStart_3675357 baseEnd_3675357 := by
    simpa [prefixWord, tailWord_3675357, baseEnd_3675357] using wordTrace_append hprefix tailTrace_3675357
  have hstable : (prefixWord ++ tailWord_3675357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675357).length < 2 ^ (prefixWord ++ tailWord_3675357).sum := by decide
  have hdescent : baseEnd_3675357 < baseStart_3675357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675426 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3675426 : Nat := 118140960795 + 3675426 * 2 ^ 59
def prefixEnd_3675426 : Nat := 4983230072969 + 3 ^ 40 * 3675426 * 2
def baseEnd_3675426 : Nat := 419391144007120469460451

theorem tailTrace_3675426 : CollatzResearch.WordTrace tailWord_3675426 prefixEnd_3675426 419391144007120469460451 := by
  unfold tailWord_3675426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513449795641697407785533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89369199455044526420761421 33513449795641697407785533)
  ·
    refine ⟨12567543673365636527919575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33513449795641697407785533 12567543673365636527919575)
    ·
      refine ⟨18851315510048454791879363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567543673365636527919575 18851315510048454791879363)
      ·
        refine ⟨28276973265072682187819045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851315510048454791879363 28276973265072682187819045)
        ·
          refine ⟨5301932487201127910216071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28276973265072682187819045 5301932487201127910216071)
          ·
            refine ⟨7952898730801691865324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301932487201127910216071 7952898730801691865324107)
            ·
              refine ⟨11929348096202537797986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952898730801691865324107 11929348096202537797986161)
              ·
                refine ⟨8947011072151903348489621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11929348096202537797986161 8947011072151903348489621)
                ·
                  refine ⟨419391144007120469460451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8947011072151903348489621 419391144007120469460451)
                  ·
                    rfl

theorem cell22_3675426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3675426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675426 prefixEnd_3675426 := by exact prefixLift 3675426
  have htrace : WordTrace (prefixWord ++ tailWord_3675426) baseStart_3675426 baseEnd_3675426 := by
    simpa [prefixWord, tailWord_3675426, baseEnd_3675426] using wordTrace_append hprefix tailTrace_3675426
  have hstable : (prefixWord ++ tailWord_3675426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675426).length < 2 ^ (prefixWord ++ tailWord_3675426).sum := by decide
  have hdescent : baseEnd_3675426 < baseStart_3675426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675454 : List Nat := [4, 2, 1, 2, 1, 1, 11]
def baseStart_3675454 : Nat := 118140960795 + 3675454 * 2 ^ 59
def prefixEnd_3675454 : Nat := 4983230072969 + 3 ^ 40 * 3675454 * 2
def baseEnd_3675454 : Nat := 46599370999762172914121

theorem tailTrace_3675454 : CollatzResearch.WordTrace tailWord_3675454 prefixEnd_3675454 46599370999762172914121 := by
  unfold tailWord_3675454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756852553308168801645177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89369880284310233608774277 16756852553308168801645177)
  ·
    refine ⟨12567639414981126601233883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16756852553308168801645177 12567639414981126601233883)
    ·
      refine ⟨18851459122471689901850825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567639414981126601233883 18851459122471689901850825)
      ·
        refine ⟨14138594341853767426388119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18851459122471689901850825 14138594341853767426388119)
        ·
          refine ⟨21207891512780651139582179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14138594341853767426388119 21207891512780651139582179)
          ·
            refine ⟨31811837269170976709373269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21207891512780651139582179 31811837269170976709373269)
            ·
              refine ⟨46599370999762172914121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31811837269170976709373269 46599370999762172914121)
              ·
                rfl

theorem cell22_3675454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 11].length) (baseStart_3675454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675454 prefixEnd_3675454 := by exact prefixLift 3675454
  have htrace : WordTrace (prefixWord ++ tailWord_3675454) baseStart_3675454 baseEnd_3675454 := by
    simpa [prefixWord, tailWord_3675454, baseEnd_3675454] using wordTrace_append hprefix tailTrace_3675454
  have hstable : (prefixWord ++ tailWord_3675454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675454).length < 2 ^ (prefixWord ++ tailWord_3675454).sum := by decide
  have hdescent : baseEnd_3675454 < baseStart_3675454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675546 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3675546 : Nat := 118140960795 + 3675546 * 2 ^ 59
def prefixEnd_3675546 : Nat := 4983230072969 + 3 ^ 40 * 3675546 * 2
def baseEnd_3675546 : Nat := 1258214510473721095380985

theorem tailTrace_3675546 : CollatzResearch.WordTrace tailWord_3675546 prefixEnd_3675546 1258214510473721095380985 := by
  unfold tailWord_3675546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514543985533012531377623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89372117294754700083673661 33514543985533012531377623)
  ·
    refine ⟨50271815978299518797066435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33514543985533012531377623 50271815978299518797066435)
    ·
      refine ⟨75407723967449278195599653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50271815978299518797066435 75407723967449278195599653)
      ·
        refine ⟨14138948243896739661674935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75407723967449278195599653 14138948243896739661674935)
        ·
          refine ⟨21208422365845109492512403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14138948243896739661674935 21208422365845109492512403)
          ·
            refine ⟨31812633548767664238768605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21208422365845109492512403 31812633548767664238768605)
            ·
              refine ⟨11929737580787874089538227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31812633548767664238768605 11929737580787874089538227)
              ·
                refine ⟨17894606371181811134307341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929737580787874089538227 17894606371181811134307341)
                ·
                  refine ⟨6710477389193179175365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17894606371181811134307341 6710477389193179175365253)
                  ·
                    refine ⟨1258214510473721095380985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710477389193179175365253 1258214510473721095380985)
                    ·
                      rfl

theorem cell22_3675546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3675546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675546 prefixEnd_3675546 := by exact prefixLift 3675546
  have htrace : WordTrace (prefixWord ++ tailWord_3675546) baseStart_3675546 baseEnd_3675546 := by
    simpa [prefixWord, tailWord_3675546, baseEnd_3675546] using wordTrace_append hprefix tailTrace_3675546
  have hstable : (prefixWord ++ tailWord_3675546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675546).length < 2 ^ (prefixWord ++ tailWord_3675546).sum := by decide
  have hdescent : baseEnd_3675546 < baseStart_3675546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675576 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_3675576 : Nat := 118140960795 + 3675576 * 2 ^ 59
def prefixEnd_3675576 : Nat := 4983230072969 + 3 ^ 40 * 3675576 * 2
def baseEnd_3675576 : Nat := 1258224780086811017130893

theorem tailTrace_3675576 : CollatzResearch.WordTrace tailWord_3675576 prefixEnd_3675576 1258224780086811017130893 := by
  unfold tailWord_3675576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67029635066011682624551291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89372846754682243499401721 67029635066011682624551291)
  ·
    refine ⟨100544452599017523936826937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67029635066011682624551291 100544452599017523936826937)
    ·
      refine ⟨75408339449263142952620203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100544452599017523936826937 75408339449263142952620203)
      ·
        refine ⟨113112509173894714428930305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75408339449263142952620203 113112509173894714428930305)
        ·
          refine ⟨84834381880421035821697729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113112509173894714428930305 84834381880421035821697729)
          ·
            refine ⟨63625786410315776866273297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84834381880421035821697729 63625786410315776866273297)
            ·
              refine ⟨47719339807736832649704973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63625786410315776866273297 47719339807736832649704973)
              ·
                refine ⟨17894752427901312243639365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47719339807736832649704973 17894752427901312243639365)
                ·
                  refine ⟨3355266080231496045682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17894752427901312243639365 3355266080231496045682381)
                  ·
                    refine ⟨1258224780086811017130893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355266080231496045682381 1258224780086811017130893)
                    ·
                      rfl

theorem cell22_3675576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_3675576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675576 prefixEnd_3675576 := by exact prefixLift 3675576
  have htrace : WordTrace (prefixWord ++ tailWord_3675576) baseStart_3675576 baseEnd_3675576 := by
    simpa [prefixWord, tailWord_3675576, baseEnd_3675576] using wordTrace_append hprefix tailTrace_3675576
  have hstable : (prefixWord ++ tailWord_3675576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675576).length < 2 ^ (prefixWord ++ tailWord_3675576).sum := by decide
  have hdescent : baseEnd_3675576 < baseStart_3675576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675745 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3675745 : Nat := 118140960795 + 3675745 * 2 ^ 59
def prefixEnd_3675745 : Nat := 4983230072969 + 3 ^ 40 * 3675745 * 2
def baseEnd_3675745 : Nat := 1258282632240550909655375

theorem tailTrace_3675745 : CollatzResearch.WordTrace tailWord_3675745 prefixEnd_3675745 1258282632240550909655375 := by
  unfold tailWord_3675745
  simp only [CollatzResearch.WordTrace]
  refine ⟨134065434068411107112004689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89376956045607404741336459 134065434068411107112004689)
  ·
    refine ⟨100549075551308330334003517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134065434068411107112004689 100549075551308330334003517)
    ·
      refine ⟨37705903331740623875251319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100549075551308330334003517 37705903331740623875251319)
      ·
        refine ⟨56558854997610935812876979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37705903331740623875251319 56558854997610935812876979)
        ·
          refine ⟨84838282496416403719315469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56558854997610935812876979 84838282496416403719315469)
          ·
            refine ⟨31814355936156151394743301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84838282496416403719315469 31814355936156151394743301)
            ·
              refine ⟨5965191738029278386514369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31814355936156151394743301 5965191738029278386514369)
              ·
                refine ⟨4473893803521958789885777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5965191738029278386514369 4473893803521958789885777)
                ·
                  refine ⟨3355420352641469092414333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473893803521958789885777 3355420352641469092414333)
                  ·
                    refine ⟨1258282632240550909655375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355420352641469092414333 1258282632240550909655375)
                    ·
                      rfl

theorem cell22_3675745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3675745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675745 prefixEnd_3675745 := by exact prefixLift 3675745
  have htrace : WordTrace (prefixWord ++ tailWord_3675745) baseStart_3675745 baseEnd_3675745 := by
    simpa [prefixWord, tailWord_3675745, baseEnd_3675745] using wordTrace_append hprefix tailTrace_3675745
  have hstable : (prefixWord ++ tailWord_3675745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675745).length < 2 ^ (prefixWord ++ tailWord_3675745).sum := by decide
  have hdescent : baseEnd_3675745 < baseStart_3675745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675747 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 4]
def baseStart_3675747 : Nat := 118140960795 + 3675747 * 2 ^ 59
def prefixEnd_3675747 : Nat := 4983230072969 + 3 ^ 40 * 3675747 * 2
def baseEnd_3675747 : Nat := 419427772293807857035123

theorem tailTrace_3675747 : CollatzResearch.WordTrace tailWord_3675747 prefixEnd_3675747 419427772293807857035123 := by
  unfold tailWord_3675747
  simp only [CollatzResearch.WordTrace]
  refine ⟨134065507014403861453577495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89377004676269240969051663 134065507014403861453577495)
  ·
    refine ⟨201098260521605792180366243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134065507014403861453577495 201098260521605792180366243)
    ·
      refine ⟨301647390782408688270549365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201098260521605792180366243 301647390782408688270549365)
      ·
        refine ⟨28279442885850814525364003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301647390782408688270549365 28279442885850814525364003)
        ·
          refine ⟨42419164328776221788046005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28279442885850814525364003 42419164328776221788046005)
          ·
            refine ⟨3976796655822770792629313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42419164328776221788046005 3976796655822770792629313)
            ·
              refine ⟨2982597491867078094471985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976796655822770792629313 2982597491867078094471985)
              ·
                refine ⟨2236948118900308570853989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982597491867078094471985 2236948118900308570853989)
                ·
                  refine ⟨419427772293807857035123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2236948118900308570853989 419427772293807857035123)
                  ·
                    rfl

theorem cell22_3675747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 4].length) (baseStart_3675747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675747 prefixEnd_3675747 := by exact prefixLift 3675747
  have htrace : WordTrace (prefixWord ++ tailWord_3675747) baseStart_3675747 baseEnd_3675747 := by
    simpa [prefixWord, tailWord_3675747, baseEnd_3675747] using wordTrace_append hprefix tailTrace_3675747
  have hstable : (prefixWord ++ tailWord_3675747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675747).length < 2 ^ (prefixWord ++ tailWord_3675747).sum := by decide
  have hdescent : baseEnd_3675747 < baseStart_3675747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3675756 : Nat := 118140960795 + 3675756 * 2 ^ 59
def prefixEnd_3675756 : Nat := 4983230072969 + 3 ^ 40 * 3675756 * 2
def baseEnd_3675756 : Nat := 1258286397765350547630341

theorem tailTrace_3675756 : CollatzResearch.WordTrace tailWord_3675756 prefixEnd_3675756 1258286397765350547630341 := by
  unfold tailWord_3675756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67032917635685627995327561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89377223514247503993770081 67032917635685627995327561)
  ·
    refine ⟨50274688226764220996495671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67032917635685627995327561 50274688226764220996495671)
    ·
      refine ⟨75412032340146331494743507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50274688226764220996495671 75412032340146331494743507)
      ·
        refine ⟨113118048510219497242115261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75412032340146331494743507 113118048510219497242115261)
        ·
          refine ⟨42419268191332311465793223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113118048510219497242115261 42419268191332311465793223)
          ·
            refine ⟨63628902286998467198689835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42419268191332311465793223 63628902286998467198689835)
            ·
              refine ⟨95443353430497700798034753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63628902286998467198689835 95443353430497700798034753)
              ·
                refine ⟨71582515072873275598526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95443353430497700798034753 71582515072873275598526065)
                ·
                  refine ⟨53686886304654956698894549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71582515072873275598526065 53686886304654956698894549)
                  ·
                    refine ⟨1258286397765350547630341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53686886304654956698894549 1258286397765350547630341)
                    ·
                      rfl

theorem cell22_3675756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3675756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675756 prefixEnd_3675756 := by exact prefixLift 3675756
  have htrace : WordTrace (prefixWord ++ tailWord_3675756) baseStart_3675756 baseEnd_3675756 := by
    simpa [prefixWord, tailWord_3675756, baseEnd_3675756] using wordTrace_append hprefix tailTrace_3675756
  have hstable : (prefixWord ++ tailWord_3675756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675756).length < 2 ^ (prefixWord ++ tailWord_3675756).sum := by decide
  have hdescent : baseEnd_3675756 < baseStart_3675756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675771 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_3675771 : Nat := 118140960795 + 3675771 * 2 ^ 59
def prefixEnd_3675771 : Nat := 4983230072969 + 3 ^ 40 * 3675771 * 2
def baseEnd_3675771 : Nat := 1258291532571895508505295

theorem tailTrace_3675771 : CollatzResearch.WordTrace tailWord_3675771 prefixEnd_3675771 1258291532571895508505295 := by
  unfold tailWord_3675771
  simp only [CollatzResearch.WordTrace]
  refine ⟨134066382366316913552451167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89377588244211275701634111 134066382366316913552451167)
  ·
    refine ⟨201099573549475370328676751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134066382366316913552451167 201099573549475370328676751)
    ·
      refine ⟨301649360324213055493015127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201099573549475370328676751 301649360324213055493015127)
      ·
        refine ⟨452474040486319583239522691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301649360324213055493015127 452474040486319583239522691)
        ·
          refine ⟨678711060729479374859284037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452474040486319583239522691 678711060729479374859284037)
          ·
            refine ⟨127258323886777382786115757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 678711060729479374859284037 127258323886777382786115757)
            ·
              refine ⟨47721871457541518544793409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127258323886777382786115757 47721871457541518544793409)
              ·
                refine ⟨35791403593156138908595057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47721871457541518544793409 35791403593156138908595057)
                ·
                  refine ⟨26843552694867104181446293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35791403593156138908595057 26843552694867104181446293)
                  ·
                    refine ⟨1258291532571895508505295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26843552694867104181446293 1258291532571895508505295)
                    ·
                      rfl

theorem cell22_3675771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_3675771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675771 prefixEnd_3675771 := by exact prefixLift 3675771
  have htrace : WordTrace (prefixWord ++ tailWord_3675771) baseStart_3675771 baseEnd_3675771 := by
    simpa [prefixWord, tailWord_3675771, baseEnd_3675771] using wordTrace_append hprefix tailTrace_3675771
  have hstable : (prefixWord ++ tailWord_3675771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675771).length < 2 ^ (prefixWord ++ tailWord_3675771).sum := by decide
  have hdescent : baseEnd_3675771 < baseStart_3675771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675796 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3675796 : Nat := 118140960795 + 3675796 * 2 ^ 59
def prefixEnd_3675796 : Nat := 4983230072969 + 3 ^ 40 * 3675796 * 2
def baseEnd_3675796 : Nat := 1258300090582803776630219

theorem tailTrace_3675796 : CollatzResearch.WordTrace tailWord_3675796 prefixEnd_3675796 1258300090582803776630219 := by
  unfold tailWord_3675796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67033647095613171411055621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89378196127484228548074161 67033647095613171411055621)
  ·
    refine ⟨12568808830427469639572929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67033647095613171411055621 12568808830427469639572929)
    ·
      refine ⟨9426606622820602229679697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12568808830427469639572929 9426606622820602229679697)
      ·
        refine ⟨7069954967115451672259773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426606622820602229679697 7069954967115451672259773)
        ·
          refine ⟨2651233112668294377097415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7069954967115451672259773 2651233112668294377097415)
          ·
            refine ⟨3976849669002441565646123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651233112668294377097415 3976849669002441565646123)
            ·
              refine ⟨5965274503503662348469185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976849669002441565646123 5965274503503662348469185)
              ·
                refine ⟨4473955877627746761351889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5965274503503662348469185 4473955877627746761351889)
                ·
                  refine ⟨3355466908220810071013917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473955877627746761351889 3355466908220810071013917)
                  ·
                    refine ⟨1258300090582803776630219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355466908220810071013917 1258300090582803776630219)
                    ·
                      rfl

theorem cell22_3675796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3675796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675796 prefixEnd_3675796 := by exact prefixLift 3675796
  have htrace : WordTrace (prefixWord ++ tailWord_3675796) baseStart_3675796 baseEnd_3675796 := by
    simpa [prefixWord, tailWord_3675796, baseEnd_3675796] using wordTrace_append hprefix tailTrace_3675796
  have hstable : (prefixWord ++ tailWord_3675796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675796).length < 2 ^ (prefixWord ++ tailWord_3675796).sum := by decide
  have hdescent : baseEnd_3675796 < baseStart_3675796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675833 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_3675833 : Nat := 118140960795 + 3675833 * 2 ^ 59
def prefixEnd_3675833 : Nat := 4983230072969 + 3 ^ 40 * 3675833 * 2
def baseEnd_3675833 : Nat := 1258312756438948013455105

theorem tailTrace_3675833 : CollatzResearch.WordTrace tailWord_3675833 prefixEnd_3675833 1258312756438948013455105 := by
  unfold tailWord_3675833
  simp only [CollatzResearch.WordTrace]
  refine ⟨134068643692092298141208153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89379095794728198760805435 134068643692092298141208153)
  ·
    refine ⟨100551482769069223605906115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134068643692092298141208153 100551482769069223605906115)
    ·
      refine ⟨150827224153603835408859173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100551482769069223605906115 150827224153603835408859173)
      ·
        refine ⟨28280104528800719139161095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150827224153603835408859173 28280104528800719139161095)
        ·
          refine ⟨42420156793201078708741643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28280104528800719139161095 42420156793201078708741643)
          ·
            refine ⟨63630235189801618063112465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42420156793201078708741643 63630235189801618063112465)
            ·
              refine ⟨47722676392351213547334349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63630235189801618063112465 47722676392351213547334349)
              ·
                refine ⟨17896003647131705080250381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47722676392351213547334349 17896003647131705080250381)
                ·
                  refine ⟨6711001367674389405093893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17896003647131705080250381 6711001367674389405093893)
                  ·
                    refine ⟨1258312756438948013455105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711001367674389405093893 1258312756438948013455105)
                    ·
                      rfl

theorem cell22_3675833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_3675833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675833 prefixEnd_3675833 := by exact prefixLift 3675833
  have htrace : WordTrace (prefixWord ++ tailWord_3675833) baseStart_3675833 baseEnd_3675833 := by
    simpa [prefixWord, tailWord_3675833, baseEnd_3675833] using wordTrace_append hprefix tailTrace_3675833
  have hstable : (prefixWord ++ tailWord_3675833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675833).length < 2 ^ (prefixWord ++ tailWord_3675833).sum := by decide
  have hdescent : baseEnd_3675833 < baseStart_3675833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675865 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 6]
def baseStart_3675865 : Nat := 118140960795 + 3675865 * 2 ^ 59
def prefixEnd_3675865 : Nat := 4983230072969 + 3 ^ 40 * 3675865 * 2
def baseEnd_3675865 : Nat := 419441236897636865551669

theorem tailTrace_3675865 : CollatzResearch.WordTrace tailWord_3675865 prefixEnd_3675865 419441236897636865551669 := by
  unfold tailWord_3675865
  simp only [CollatzResearch.WordTrace]
  refine ⟨134069810827976367606373049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89379873885317578404248699 134069810827976367606373049)
  ·
    refine ⟨100552358120982275704779787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134069810827976367606373049 100552358120982275704779787)
    ·
      refine ⟨150828537181473413557169681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100552358120982275704779787 150828537181473413557169681)
      ·
        refine ⟨113121402886105060167877261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150828537181473413557169681 113121402886105060167877261)
        ·
          refine ⟨42420526082289397562953973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113121402886105060167877261 42420526082289397562953973)
          ·
            refine ⟨3976924320214631021526935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42420526082289397562953973 3976924320214631021526935)
            ·
              refine ⟨5965386480321946532290403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976924320214631021526935 5965386480321946532290403)
              ·
                refine ⟨8948079720482919798435605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965386480321946532290403 8948079720482919798435605)
                ·
                  refine ⟨419441236897636865551669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8948079720482919798435605 419441236897636865551669)
                  ·
                    rfl

theorem cell22_3675865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_3675865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3675865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3675865 prefixEnd_3675865 := by exact prefixLift 3675865
  have htrace : WordTrace (prefixWord ++ tailWord_3675865) baseStart_3675865 baseEnd_3675865 := by
    simpa [prefixWord, tailWord_3675865, baseEnd_3675865] using wordTrace_append hprefix tailTrace_3675865
  have hstable : (prefixWord ++ tailWord_3675865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675865).length < 2 ^ (prefixWord ++ tailWord_3675865).sum := by decide
  have hdescent : baseEnd_3675865 < baseStart_3675865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676000 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_3676000 : Nat := 118140960795 + 3676000 * 2 ^ 59
def prefixEnd_3676000 : Nat := 4983230072969 + 3 ^ 40 * 3676000 * 2
def baseEnd_3676000 : Nat := 419456641317271748176531

theorem tailTrace_3676000 : CollatzResearch.WordTrace tailWord_3676000 prefixEnd_3676000 419456641317271748176531 := by
  unfold tailWord_3676000
  simp only [CollatzResearch.WordTrace]
  refine ⟨67037367341243642831268727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89383156454991523775024969 67037367341243642831268727)
  ·
    refine ⟨100556051011865464246903091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67037367341243642831268727 100556051011865464246903091)
    ·
      refine ⟨150834076517798196370354637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100556051011865464246903091 150834076517798196370354637)
      ·
        refine ⟨56562778694174323638882989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150834076517798196370354637 56562778694174323638882989)
        ·
          refine ⟨21211042010315371364581121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56562778694174323638882989 21211042010315371364581121)
          ·
            refine ⟨15908281507736528523435841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21211042010315371364581121 15908281507736528523435841)
            ·
              refine ⟨11931211130802396392576881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15908281507736528523435841 11931211130802396392576881)
              ·
                refine ⟨8948408348101797294432661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11931211130802396392576881 8948408348101797294432661)
                ·
                  refine ⟨419456641317271748176531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8948408348101797294432661 419456641317271748176531)
                  ·
                    rfl

theorem cell22_3676000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_3676000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676000 prefixEnd_3676000 := by exact prefixLift 3676000
  have htrace : WordTrace (prefixWord ++ tailWord_3676000) baseStart_3676000 baseEnd_3676000 := by
    simpa [prefixWord, tailWord_3676000, baseEnd_3676000] using wordTrace_append hprefix tailTrace_3676000
  have hstable : (prefixWord ++ tailWord_3676000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676000).length < 2 ^ (prefixWord ++ tailWord_3676000).sum := by decide
  have hdescent : baseEnd_3676000 < baseStart_3676000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676010 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3676010 : Nat := 118140960795 + 3676010 * 2 ^ 59
def prefixEnd_3676010 : Nat := 4983230072969 + 3 ^ 40 * 3676010 * 2
def baseEnd_3676010 : Nat := 1258373347156178551779563

theorem tailTrace_3676010 : CollatzResearch.WordTrace tailWord_3676010 prefixEnd_3676010 1258373347156178551779563 := by
  unfold tailWord_3676010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33518774853112764342600371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89383399608300704913600989 33518774853112764342600371)
  ·
    refine ⟨50278162279669146513900557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33518774853112764342600371 50278162279669146513900557)
    ·
      refine ⟨18854310854875929942712709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50278162279669146513900557 18854310854875929942712709)
      ·
        refine ⟨3535183285289236864258633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18854310854875929942712709 3535183285289236864258633)
        ·
          refine ⟨2651387463966927648193975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535183285289236864258633 2651387463966927648193975)
          ·
            refine ⟨3977081195950391472290963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651387463966927648193975 3977081195950391472290963)
            ·
              refine ⟨5965621793925587208436445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977081195950391472290963 5965621793925587208436445)
              ·
                refine ⟨2237108172722095203163667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5965621793925587208436445 2237108172722095203163667)
                ·
                  refine ⟨3355662259083142804745501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237108172722095203163667 3355662259083142804745501)
                  ·
                    refine ⟨1258373347156178551779563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355662259083142804745501 1258373347156178551779563)
                    ·
                      rfl

theorem cell22_3676010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3676010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676010 prefixEnd_3676010 := by exact prefixLift 3676010
  have htrace : WordTrace (prefixWord ++ tailWord_3676010) baseStart_3676010 baseEnd_3676010 := by
    simpa [prefixWord, tailWord_3676010, baseEnd_3676010] using wordTrace_append hprefix tailTrace_3676010
  have hstable : (prefixWord ++ tailWord_3676010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676010).length < 2 ^ (prefixWord ++ tailWord_3676010).sum := by decide
  have hdescent : baseEnd_3676010 < baseStart_3676010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676032 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_3676032 : Nat := 118140960795 + 3676032 * 2 ^ 59
def prefixEnd_3676032 : Nat := 4983230072969 + 3 ^ 40 * 3676032 * 2
def baseEnd_3676032 : Nat := 1258380878205777827729495

theorem tailTrace_3676032 : CollatzResearch.WordTrace tailWord_3676032 prefixEnd_3676032 1258380878205777827729495 := by
  unfold tailWord_3676032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67037950909185677563851175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89383934545580903418468233 67037950909185677563851175)
  ·
    refine ⟨100556926363778516345776763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67037950909185677563851175 100556926363778516345776763)
    ·
      refine ⟨150835389545667774518665145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100556926363778516345776763 150835389545667774518665145)
      ·
        refine ⟨113126542159250830888998859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150835389545667774518665145 113126542159250830888998859)
        ·
          refine ⟨169689813238876246333498289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113126542159250830888998859 169689813238876246333498289)
          ·
            refine ⟨127267359929157184750123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169689813238876246333498289 127267359929157184750123717)
            ·
              refine ⟨23862629986716972140648197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127267359929157184750123717 23862629986716972140648197)
              ·
                refine ⟨4474243122509432276371537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23862629986716972140648197 4474243122509432276371537)
                ·
                  refine ⟨3355682341882074207278653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474243122509432276371537 3355682341882074207278653)
                  ·
                    refine ⟨1258380878205777827729495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355682341882074207278653 1258380878205777827729495)
                    ·
                      rfl

theorem cell22_3676032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_3676032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676032 prefixEnd_3676032 := by exact prefixLift 3676032
  have htrace : WordTrace (prefixWord ++ tailWord_3676032) baseStart_3676032 baseEnd_3676032 := by
    simpa [prefixWord, tailWord_3676032, baseEnd_3676032] using wordTrace_append hprefix tailTrace_3676032
  have hstable : (prefixWord ++ tailWord_3676032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676032).length < 2 ^ (prefixWord ++ tailWord_3676032).sum := by decide
  have hdescent : baseEnd_3676032 < baseStart_3676032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676049 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_3676049 : Nat := 118140960795 + 3676049 * 2 ^ 59
def prefixEnd_3676049 : Nat := 4983230072969 + 3 ^ 40 * 3676049 * 2
def baseEnd_3676049 : Nat := 1258386697653195450054443

theorem tailTrace_3676049 : CollatzResearch.WordTrace tailWord_3676049 prefixEnd_3676049 1258386697653195450054443 := by
  unfold tailWord_3676049
  simp only [CollatzResearch.WordTrace]
  refine ⟨134076521859309767031071201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89384347906206511354047467 134076521859309767031071201)
  ·
    refine ⟨100557391394482325273303401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134076521859309767031071201 100557391394482325273303401)
    ·
      refine ⟨75418043545861743954977551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100557391394482325273303401 75418043545861743954977551)
      ·
        refine ⟨113127065318792615932466327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75418043545861743954977551 113127065318792615932466327)
        ·
          refine ⟨169690597978188923898699491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113127065318792615932466327 169690597978188923898699491)
          ·
            refine ⟨254535896967283385848049237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169690597978188923898699491 254535896967283385848049237)
            ·
              refine ⟨2982842542585352177906827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 254535896967283385848049237 2982842542585352177906827)
              ·
                refine ⟨4474263813878028266860241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982842542585352177906827 4474263813878028266860241)
                ·
                  refine ⟨3355697860408521200145181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474263813878028266860241 3355697860408521200145181)
                  ·
                    refine ⟨1258386697653195450054443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355697860408521200145181 1258386697653195450054443)
                    ·
                      rfl

theorem cell22_3676049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_3676049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676049 prefixEnd_3676049 := by exact prefixLift 3676049
  have htrace : WordTrace (prefixWord ++ tailWord_3676049) baseStart_3676049 baseEnd_3676049 := by
    simpa [prefixWord, tailWord_3676049, baseEnd_3676049] using wordTrace_append hprefix tailTrace_3676049
  have hstable : (prefixWord ++ tailWord_3676049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676049).length < 2 ^ (prefixWord ++ tailWord_3676049).sum := by decide
  have hdescent : baseEnd_3676049 < baseStart_3676049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676105 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_3676105 : Nat := 118140960795 + 3676105 * 2 ^ 59
def prefixEnd_3676105 : Nat := 4983230072969 + 3 ^ 40 * 3676105 * 2
def baseEnd_3676105 : Nat := 1258405867597629970654271

theorem tailTrace_3676105 : CollatzResearch.WordTrace tailWord_3676105 prefixEnd_3676105 1258405867597629970654271 := by
  unfold tailWord_3676105
  simp only [CollatzResearch.WordTrace]
  refine ⟨134078564347106888595109769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89385709564737925730073179 134078564347106888595109769)
  ·
    refine ⟨100558923260330166446332327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134078564347106888595109769 100558923260330166446332327)
    ·
      refine ⟨150838384890495249669498491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100558923260330166446332327 150838384890495249669498491)
      ·
        refine ⟨226257577335742874504247737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150838384890495249669498491 226257577335742874504247737)
        ·
          refine ⟨169693183001807155878185803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226257577335742874504247737 169693183001807155878185803)
          ·
            refine ⟨254539774502710733817278705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169693183001807155878185803 254539774502710733817278705)
            ·
              refine ⟨190904830877033050362959029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254539774502710733817278705 190904830877033050362959029)
              ·
                refine ⟨17897327894721848471527409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190904830877033050362959029 17897327894721848471527409)
                ·
                  refine ⟨13422995921041386353645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17897327894721848471527409 13422995921041386353645557)
                  ·
                    refine ⟨1258405867597629970654271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13422995921041386353645557 1258405867597629970654271)
                    ·
                      rfl

theorem cell22_3676105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_3676105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676105 prefixEnd_3676105 := by exact prefixLift 3676105
  have htrace : WordTrace (prefixWord ++ tailWord_3676105) baseStart_3676105 baseEnd_3676105 := by
    simpa [prefixWord, tailWord_3676105, baseEnd_3676105] using wordTrace_append hprefix tailTrace_3676105
  have hstable : (prefixWord ++ tailWord_3676105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676105).length < 2 ^ (prefixWord ++ tailWord_3676105).sum := by decide
  have hdescent : baseEnd_3676105 < baseStart_3676105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676186 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3676186 : Nat := 118140960795 + 3676186 * 2 ^ 59
def prefixEnd_3676186 : Nat := 4983230072969 + 3 ^ 40 * 3676186 * 2
def baseEnd_3676186 : Nat := 419477865184324253126341

theorem tailTrace_3676186 : CollatzResearch.WordTrace tailWord_3676186 prefixEnd_3676186 419477865184324253126341 := by
  unfold tailWord_3676186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33520379664953359857202103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89387679106542292952538941 33520379664953359857202103)
  ·
    refine ⟨50280569497430039785803155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33520379664953359857202103 50280569497430039785803155)
    ·
      refine ⟨75420854246145059678704733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50280569497430039785803155 75420854246145059678704733)
      ·
        refine ⟨28282820342304397379514275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75420854246145059678704733 28282820342304397379514275)
        ·
          refine ⟨42424230513456596069271413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282820342304397379514275 42424230513456596069271413)
          ·
            refine ⟨3977271610636555881494195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42424230513456596069271413 3977271610636555881494195)
            ·
              refine ⟨5965907415954833822241293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977271610636555881494195 5965907415954833822241293)
              ·
                refine ⟨2237215280983062683340485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5965907415954833822241293 2237215280983062683340485)
                ·
                  refine ⟨419477865184324253126341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237215280983062683340485 419477865184324253126341)
                  ·
                    rfl

theorem cell22_3676186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3676186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676186 prefixEnd_3676186 := by exact prefixLift 3676186
  have htrace : WordTrace (prefixWord ++ tailWord_3676186) baseStart_3676186 baseEnd_3676186 := by
    simpa [prefixWord, tailWord_3676186, baseEnd_3676186] using wordTrace_append hprefix tailTrace_3676186
  have hstable : (prefixWord ++ tailWord_3676186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676186).length < 2 ^ (prefixWord ++ tailWord_3676186).sum := by decide
  have hdescent : baseEnd_3676186 < baseStart_3676186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676197 : List Nat := [1, 3, 1, 2, 2, 5, 8]
def baseStart_3676197 : Nat := 118140960795 + 3676197 * 2 ^ 59
def prefixEnd_3676197 : Nat := 4983230072969 + 3 ^ 40 * 3676197 * 2
def baseEnd_3676197 : Nat := 46608791151028607309407

theorem tailTrace_3676197 : CollatzResearch.WordTrace tailWord_3676197 prefixEnd_3676197 46608791151028607309407 := by
  unfold tailWord_3676197
  simp only [CollatzResearch.WordTrace]
  refine ⟨134081919862773588307458845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89387946575182392204972563 134081919862773588307458845)
  ·
    refine ⟨50280719948540095615297067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134081919862773588307458845 50280719948540095615297067)
    ·
      refine ⟨75421079922810143422945601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50280719948540095615297067 75421079922810143422945601)
      ·
        refine ⟨56565809942107607567209201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75421079922810143422945601 56565809942107607567209201)
        ·
          refine ⟨42424357456580705675406901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56565809942107607567209201 42424357456580705675406901)
          ·
            refine ⟨3977283511554441157069397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42424357456580705675406901 3977283511554441157069397)
            ·
              refine ⟨46608791151028607309407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3977283511554441157069397 46608791151028607309407)
              ·
                rfl

theorem cell22_3676197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 8].length) (baseStart_3676197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676197 prefixEnd_3676197 := by exact prefixLift 3676197
  have htrace : WordTrace (prefixWord ++ tailWord_3676197) baseStart_3676197 baseEnd_3676197 := by
    simpa [prefixWord, tailWord_3676197, baseEnd_3676197] using wordTrace_append hprefix tailTrace_3676197
  have hstable : (prefixWord ++ tailWord_3676197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676197).length < 2 ^ (prefixWord ++ tailWord_3676197).sum := by decide
  have hdescent : baseEnd_3676197 < baseStart_3676197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676214 : List Nat := [5, 1, 2, 1, 1, 1, 4, 7]
def baseStart_3676214 : Nat := 118140960795 + 3676214 * 2 ^ 59
def prefixEnd_3676214 : Nat := 4983230072969 + 3 ^ 40 * 3676214 * 2
def baseEnd_3676214 : Nat := 139827020058354446630993

theorem tailTrace_3676214 : CollatzResearch.WordTrace tailWord_3676214 prefixEnd_3676214 139827020058354446630993 := by
  unfold tailWord_3676214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380158743982000013176731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89388359935808000140551797 8380158743982000013176731)
  ·
    refine ⟨12570238115973000019765097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8380158743982000013176731 12570238115973000019765097)
    ·
      refine ⟨9427678586979750014823823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12570238115973000019765097 9427678586979750014823823)
      ·
        refine ⟨14141517880469625022235735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427678586979750014823823 14141517880469625022235735)
        ·
          refine ⟨21212276820704437533353603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141517880469625022235735 21212276820704437533353603)
          ·
            refine ⟨31818415231056656300030405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212276820704437533353603 31818415231056656300030405)
            ·
              refine ⟨5965952855823123056255701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31818415231056656300030405 5965952855823123056255701)
              ·
                refine ⟨139827020058354446630993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5965952855823123056255701 139827020058354446630993)
                ·
                  rfl

theorem cell22_3676214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_3676214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676214 prefixEnd_3676214 := by exact prefixLift 3676214
  have htrace : WordTrace (prefixWord ++ tailWord_3676214) baseStart_3676214 baseEnd_3676214 := by
    simpa [prefixWord, tailWord_3676214, baseEnd_3676214] using wordTrace_append hprefix tailTrace_3676214
  have hstable : (prefixWord ++ tailWord_3676214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676214).length < 2 ^ (prefixWord ++ tailWord_3676214).sum := by decide
  have hdescent : baseEnd_3676214 < baseStart_3676214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676254 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3676254 : Nat := 118140960795 + 3676254 * 2 ^ 59
def prefixEnd_3676254 : Nat := 4983230072969 + 3 ^ 40 * 3676254 * 2
def baseEnd_3676254 : Nat := 419485624447547749559605

theorem tailTrace_3676254 : CollatzResearch.WordTrace tailWord_3676254 prefixEnd_3676254 419485624447547749559605 := by
  unfold tailWord_3676254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760499852945885880285477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89389332549044724694855877 16760499852945885880285477)
  ·
    refine ⟨3142593722427353602553527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16760499852945885880285477 3142593722427353602553527)
    ·
      refine ⟨4713890583641030403830291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142593722427353602553527 4713890583641030403830291)
      ·
        refine ⟨7070835875461545605745437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713890583641030403830291 7070835875461545605745437)
        ·
          refine ⟨2651563453298079602154539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7070835875461545605745437 2651563453298079602154539)
          ·
            refine ⟨3977345179947119403231809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651563453298079602154539 3977345179947119403231809)
            ·
              refine ⟨2983008884960339552423857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977345179947119403231809 2983008884960339552423857)
              ·
                refine ⟨2237256663720254664317893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983008884960339552423857 2237256663720254664317893)
                ·
                  refine ⟨419485624447547749559605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237256663720254664317893 419485624447547749559605)
                  ·
                    rfl

theorem cell22_3676254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3676254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676254 prefixEnd_3676254 := by exact prefixLift 3676254
  have htrace : WordTrace (prefixWord ++ tailWord_3676254) baseStart_3676254 baseEnd_3676254 := by
    simpa [prefixWord, tailWord_3676254, baseEnd_3676254] using wordTrace_append hprefix tailTrace_3676254
  have hstable : (prefixWord ++ tailWord_3676254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676254).length < 2 ^ (prefixWord ++ tailWord_3676254).sum := by decide
  have hdescent : baseEnd_3676254 < baseStart_3676254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676257 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3676257 : Nat := 118140960795 + 3676257 * 2 ^ 59
def prefixEnd_3676257 : Nat := 4983230072969 + 3 ^ 40 * 3676257 * 2
def baseEnd_3676257 : Nat := 1258457900303952240853805

theorem tailTrace_3676257 : CollatzResearch.WordTrace tailWord_3676257 prefixEnd_3676257 1258457900303952240853805 := by
  unfold tailWord_3676257
  simp only [CollatzResearch.WordTrace]
  refine ⟨134084108242556218554643025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89389405495037479036428683 134084108242556218554643025)
  ·
    refine ⟨100563081181917163915982269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134084108242556218554643025 100563081181917163915982269)
    ·
      refine ⟨37711155443218936468493351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100563081181917163915982269 37711155443218936468493351)
      ·
        refine ⟨56566733164828404702740027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37711155443218936468493351 56566733164828404702740027)
        ·
          refine ⟨84850099747242607054110041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56566733164828404702740027 84850099747242607054110041)
          ·
            refine ⟨63637574810431955290582531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84850099747242607054110041 63637574810431955290582531)
            ·
              refine ⟨95456362215647932935873797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63637574810431955290582531 95456362215647932935873797)
              ·
                refine ⟨17898067915433987425476337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95456362215647932935873797 17898067915433987425476337)
                ·
                  refine ⟨13423550936575490569107253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17898067915433987425476337 13423550936575490569107253)
                  ·
                    refine ⟨1258457900303952240853805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13423550936575490569107253 1258457900303952240853805)
                    ·
                      rfl

theorem cell22_3676257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3676257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676257 prefixEnd_3676257 := by exact prefixLift 3676257
  have htrace : WordTrace (prefixWord ++ tailWord_3676257) baseStart_3676257 baseEnd_3676257 := by
    simpa [prefixWord, tailWord_3676257, baseEnd_3676257] using wordTrace_append hprefix tailTrace_3676257
  have hstable : (prefixWord ++ tailWord_3676257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676257).length < 2 ^ (prefixWord ++ tailWord_3676257).sum := by decide
  have hdescent : baseEnd_3676257 < baseStart_3676257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676274 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_3676274 : Nat := 118140960795 + 3676274 * 2 ^ 59
def prefixEnd_3676274 : Nat := 4983230072969 + 3 ^ 40 * 3676274 * 2
def baseEnd_3676274 : Nat := 1258463719751369863178753

theorem tailTrace_3676274 : CollatzResearch.WordTrace tailWord_3676274 prefixEnd_3676274 1258463719751369863178753 := by
  unfold tailWord_3676274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521182070873657614502969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89389818855663086972007917 33521182070873657614502969)
  ·
    refine ⟨25140886553155243210877227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33521182070873657614502969 25140886553155243210877227)
    ·
      refine ⟨37711329829732864816315841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25140886553155243210877227 37711329829732864816315841)
      ·
        refine ⟨28283497372299648612236881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37711329829732864816315841 28283497372299648612236881)
        ·
          refine ⟨21212623029224736459177661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28283497372299648612236881 21212623029224736459177661)
          ·
            refine ⟨7954733635959276172191623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21212623029224736459177661 7954733635959276172191623)
            ·
              refine ⟨11932100453938914258287435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954733635959276172191623 11932100453938914258287435)
              ·
                refine ⟨17898150680908371387431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11932100453938914258287435 17898150680908371387431153)
                ·
                  refine ⟨13423613010681278540573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17898150680908371387431153 13423613010681278540573365)
                  ·
                    refine ⟨1258463719751369863178753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13423613010681278540573365 1258463719751369863178753)
                    ·
                      rfl

theorem cell22_3676274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_3676274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676274 prefixEnd_3676274 := by exact prefixLift 3676274
  have htrace : WordTrace (prefixWord ++ tailWord_3676274) baseStart_3676274 baseEnd_3676274 := by
    simpa [prefixWord, tailWord_3676274, baseEnd_3676274] using wordTrace_append hprefix tailTrace_3676274
  have hstable : (prefixWord ++ tailWord_3676274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676274).length < 2 ^ (prefixWord ++ tailWord_3676274).sum := by decide
  have hdescent : baseEnd_3676274 < baseStart_3676274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676306 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3676306 : Nat := 118140960795 + 3676306 * 2 ^ 59
def prefixEnd_3676306 : Nat := 4983230072969 + 3 ^ 40 * 3676306 * 2
def baseEnd_3676306 : Nat := 1258474674005332446378655

theorem tailTrace_3676306 : CollatzResearch.WordTrace tailWord_3676306 prefixEnd_3676306 1258474674005332446378655 := by
  unfold tailWord_3676306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521473854844674980794193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89390596946252466615451181 33521473854844674980794193)
  ·
    refine ⟨25141105391133506235595645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33521473854844674980794193 25141105391133506235595645)
    ·
      refine ⟨9427914521675064838348367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25141105391133506235595645 9427914521675064838348367)
      ·
        refine ⟨14141871782512597257522551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427914521675064838348367 14141871782512597257522551)
        ·
          refine ⟨21212807673768895886283827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141871782512597257522551 21212807673768895886283827)
          ·
            refine ⟨31819211510653343829425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212807673768895886283827 31819211510653343829425741)
            ·
              refine ⟨11932204316495003936034653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31819211510653343829425741 11932204316495003936034653)
              ·
                refine ⟨4474576618685626476012995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932204316495003936034653 4474576618685626476012995)
                ·
                  refine ⟨6711864928028439714019493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474576618685626476012995 6711864928028439714019493)
                  ·
                    refine ⟨1258474674005332446378655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711864928028439714019493 1258474674005332446378655)
                    ·
                      rfl

theorem cell22_3676306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3676306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676306 prefixEnd_3676306 := by exact prefixLift 3676306
  have htrace : WordTrace (prefixWord ++ tailWord_3676306) baseStart_3676306 baseEnd_3676306 := by
    simpa [prefixWord, tailWord_3676306, baseEnd_3676306] using wordTrace_append hprefix tailTrace_3676306
  have hstable : (prefixWord ++ tailWord_3676306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676306).length < 2 ^ (prefixWord ++ tailWord_3676306).sum := by decide
  have hdescent : baseEnd_3676306 < baseStart_3676306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676321 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 4]
def baseStart_3676321 : Nat := 118140960795 + 3676321 * 2 ^ 59
def prefixEnd_3676321 : Nat := 4983230072969 + 3 ^ 40 * 3676321 * 2
def baseEnd_3676321 : Nat := 419493269603959135751203

theorem tailTrace_3676321 : CollatzResearch.WordTrace tailWord_3676321 prefixEnd_3676321 419493269603959135751203 := by
  unfold tailWord_3676321
  simp only [CollatzResearch.WordTrace]
  refine ⟨134086442514324357484972817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89390961676216238323315211 134086442514324357484972817)
  ·
    refine ⟨100564831885743268113729613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134086442514324357484972817 100564831885743268113729613)
    ·
      refine ⟨37711811957153725542648605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100564831885743268113729613 37711811957153725542648605)
      ·
        refine ⟨14141929483932647078493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37711811957153725542648605 14141929483932647078493227)
        ·
          refine ⟨21212894225898970617739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141929483932647078493227 21212894225898970617739841)
          ·
            refine ⟨15909670669424227963304881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21212894225898970617739841 15909670669424227963304881)
            ·
              refine ⟨11932253002068170972478661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15909670669424227963304881 11932253002068170972478661)
              ·
                refine ⟨2237297437887782057339749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11932253002068170972478661 2237297437887782057339749)
                ·
                  refine ⟨419493269603959135751203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237297437887782057339749 419493269603959135751203)
                  ·
                    rfl

theorem cell22_3676321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_3676321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676321 prefixEnd_3676321 := by exact prefixLift 3676321
  have htrace : WordTrace (prefixWord ++ tailWord_3676321) baseStart_3676321 baseEnd_3676321 := by
    simpa [prefixWord, tailWord_3676321, baseEnd_3676321] using wordTrace_append hprefix tailTrace_3676321
  have hstable : (prefixWord ++ tailWord_3676321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676321).length < 2 ^ (prefixWord ++ tailWord_3676321).sum := by decide
  have hdescent : baseEnd_3676321 < baseStart_3676321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676347 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_3676347 : Nat := 118140960795 + 3676347 * 2 ^ 59
def prefixEnd_3676347 : Nat := 4983230072969 + 3 ^ 40 * 3676347 * 2
def baseEnd_3676347 : Nat := 1258488709143222006103529

theorem tailTrace_3676347 : CollatzResearch.WordTrace tailWord_3676347 prefixEnd_3676347 1258488709143222006103529 := by
  unfold tailWord_3676347
  simp only [CollatzResearch.WordTrace]
  refine ⟨134087390812230163925419295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89391593874820109283612863 134087390812230163925419295)
  ·
    refine ⟨201131086218345245888128943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134087390812230163925419295 201131086218345245888128943)
    ·
      refine ⟨301696629327517868832193415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201131086218345245888128943 301696629327517868832193415)
      ·
        refine ⟨452544943991276803248290123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301696629327517868832193415 452544943991276803248290123)
        ·
          refine ⟨678817415986915204872435185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452544943991276803248290123 678817415986915204872435185)
          ·
            refine ⟨509113061990186403654326389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678817415986915204872435185 509113061990186403654326389)
            ·
              refine ⟨47729349561579975342593099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509113061990186403654326389 47729349561579975342593099)
              ·
                refine ⟨71594024342369963013889649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47729349561579975342593099 71594024342369963013889649)
                ·
                  refine ⟨53695518256777472260417237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71594024342369963013889649 53695518256777472260417237)
                  ·
                    refine ⟨1258488709143222006103529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53695518256777472260417237 1258488709143222006103529)
                    ·
                      rfl

theorem cell22_3676347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_3676347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676347 prefixEnd_3676347 := by exact prefixLift 3676347
  have htrace : WordTrace (prefixWord ++ tailWord_3676347) baseStart_3676347 baseEnd_3676347 := by
    simpa [prefixWord, tailWord_3676347, baseEnd_3676347] using wordTrace_append hprefix tailTrace_3676347
  have hstable : (prefixWord ++ tailWord_3676347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676347).length < 2 ^ (prefixWord ++ tailWord_3676347).sum := by decide
  have hdescent : baseEnd_3676347 < baseStart_3676347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676387 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 2, 3]
def baseStart_3676387 : Nat := 118140960795 + 3676387 * 2 ^ 59
def prefixEnd_3676387 : Nat := 4983230072969 + 3 ^ 40 * 3676387 * 2
def baseEnd_3676387 : Nat := 1258502401960675235103407

theorem tailTrace_3676387 : CollatzResearch.WordTrace tailWord_3676387 prefixEnd_3676387 1258502401960675235103407 := by
  unfold tailWord_3676387
  simp only [CollatzResearch.WordTrace]
  refine ⟨134088849732085250756875415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89392566488056833837916943 134088849732085250756875415)
  ·
    refine ⟨201133274598127876135313123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134088849732085250756875415 201133274598127876135313123)
    ·
      refine ⟨301699911897191814202969685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201133274598127876135313123 301699911897191814202969685)
      ·
        refine ⟨3535545842545216572691051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 301699911897191814202969685 3535545842545216572691051)
        ·
          refine ⟨5303318763817824859036577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535545842545216572691051 5303318763817824859036577)
          ·
            refine ⟨3977489072863368644277433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303318763817824859036577 3977489072863368644277433)
            ·
              refine ⟨2983116804647526483208075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977489072863368644277433 2983116804647526483208075)
              ·
                refine ⟨4474675206971289724812113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983116804647526483208075 4474675206971289724812113)
                ·
                  refine ⟨3356006405228467293609085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474675206971289724812113 3356006405228467293609085)
                  ·
                    refine ⟨1258502401960675235103407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356006405228467293609085 1258502401960675235103407)
                    ·
                      rfl

theorem cell22_3676387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 3].length) (baseStart_3676387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676387 prefixEnd_3676387 := by exact prefixLift 3676387
  have htrace : WordTrace (prefixWord ++ tailWord_3676387) baseStart_3676387 baseEnd_3676387 := by
    simpa [prefixWord, tailWord_3676387, baseEnd_3676387] using wordTrace_append hprefix tailTrace_3676387
  have hstable : (prefixWord ++ tailWord_3676387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676387).length < 2 ^ (prefixWord ++ tailWord_3676387).sum := by decide
  have hdescent : baseEnd_3676387 < baseStart_3676387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676473 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 4]
def baseStart_3676473 : Nat := 118140960795 + 3676473 * 2 ^ 59
def prefixEnd_3676473 : Nat := 4983230072969 + 3 ^ 40 * 3676473 * 2
def baseEnd_3676473 : Nat := 419510613839399892484381

theorem tailTrace_3676473 : CollatzResearch.WordTrace tailWord_3676473 prefixEnd_3676473 419510613839399892484381 := by
  unfold tailWord_3676473
  simp only [CollatzResearch.WordTrace]
  refine ⟨134091986409773687444506073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89394657606515791629670715 134091986409773687444506073)
  ·
    refine ⟨100568989807330265583379555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134091986409773687444506073 100568989807330265583379555)
    ·
      refine ⟨150853484710995398375069333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100568989807330265583379555 150853484710995398375069333)
      ·
        refine ⟨7071257095827909298831375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150853484710995398375069333 7071257095827909298831375)
        ·
          refine ⟨10606885643741863948247063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071257095827909298831375 10606885643741863948247063)
          ·
            refine ⟨15910328465612795922370595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606885643741863948247063 15910328465612795922370595)
            ·
              refine ⟨23865492698419193883555893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910328465612795922370595 23865492698419193883555893)
              ·
                refine ⟨2237389940476799426583365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23865492698419193883555893 2237389940476799426583365)
                ·
                  refine ⟨419510613839399892484381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237389940476799426583365 419510613839399892484381)
                  ·
                    rfl

theorem cell22_3676473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_3676473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676473 prefixEnd_3676473 := by exact prefixLift 3676473
  have htrace : WordTrace (prefixWord ++ tailWord_3676473) baseStart_3676473 baseEnd_3676473 := by
    simpa [prefixWord, tailWord_3676473, baseEnd_3676473] using wordTrace_append hprefix tailTrace_3676473
  have hstable : (prefixWord ++ tailWord_3676473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676473).length < 2 ^ (prefixWord ++ tailWord_3676473).sum := by decide
  have hdescent : baseEnd_3676473 < baseStart_3676473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676488 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_3676488 : Nat := 118140960795 + 3676488 * 2 ^ 59
def prefixEnd_3676488 : Nat := 4983230072969 + 3 ^ 40 * 3676488 * 2
def baseEnd_3676488 : Nat := 1258536976324744638328097

theorem tailTrace_3676488 : CollatzResearch.WordTrace tailWord_3676488 prefixEnd_3676488 1258536976324744638328097 := by
  unfold tailWord_3676488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67046266752359672503151059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89395022336479563337534745 67046266752359672503151059)
  ·
    refine ⟨100569400128539508754726589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67046266752359672503151059 100569400128539508754726589)
    ·
      refine ⟨37713525048202315783022471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100569400128539508754726589 37713525048202315783022471)
      ·
        refine ⟨56570287572303473674533707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37713525048202315783022471 56570287572303473674533707)
        ·
          refine ⟨84855431358455210511800561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56570287572303473674533707 84855431358455210511800561)
          ·
            refine ⟨63641573518841407883850421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84855431358455210511800561 63641573518841407883850421)
            ·
              refine ⟨5966397517391381989110977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63641573518841407883850421 5966397517391381989110977)
              ·
                refine ⟨4474798138043536491833233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966397517391381989110977 4474798138043536491833233)
                ·
                  refine ⟨3356098603532652368874925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474798138043536491833233 3356098603532652368874925)
                  ·
                    refine ⟨1258536976324744638328097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356098603532652368874925 1258536976324744638328097)
                    ·
                      rfl

theorem cell22_3676488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_3676488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676488 prefixEnd_3676488 := by exact prefixLift 3676488
  have htrace : WordTrace (prefixWord ++ tailWord_3676488) baseStart_3676488 baseEnd_3676488 := by
    simpa [prefixWord, tailWord_3676488, baseEnd_3676488] using wordTrace_append hprefix tailTrace_3676488
  have hstable : (prefixWord ++ tailWord_3676488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676488).length < 2 ^ (prefixWord ++ tailWord_3676488).sum := by decide
  have hdescent : baseEnd_3676488 < baseStart_3676488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676653 : List Nat := [1, 5, 1, 3, 1, 2, 9]
def baseStart_3676653 : Nat := 118140960795 + 3676653 * 2 ^ 59
def prefixEnd_3676653 : Nat := 4983230072969 + 3 ^ 40 * 3676653 * 2
def baseEnd_3676653 : Nat := 46614572562842192887133

theorem tailTrace_3676653 : CollatzResearch.WordTrace tailWord_3676653 prefixEnd_3676653 46614572562842192887133 := by
  unfold tailWord_3676653
  simp only [CollatzResearch.WordTrace]
  refine ⟨134098551549121578186058613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89399034366081052124039075 134098551549121578186058613)
  ·
    refine ⟨12571739207730147954942995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134098551549121578186058613 12571739207730147954942995)
    ·
      refine ⟨18857608811595221932414493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12571739207730147954942995 18857608811595221932414493)
      ·
        refine ⟨7071603304348208224655435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18857608811595221932414493 7071603304348208224655435)
        ·
          refine ⟨10607404956522312336983153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071603304348208224655435 10607404956522312336983153)
          ·
            refine ⟨7955553717391734252737365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10607404956522312336983153 7955553717391734252737365)
            ·
              refine ⟨46614572562842192887133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7955553717391734252737365 46614572562842192887133)
              ·
                rfl

theorem cell22_3676653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 9].length) (baseStart_3676653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676653 prefixEnd_3676653 := by exact prefixLift 3676653
  have htrace : WordTrace (prefixWord ++ tailWord_3676653) baseStart_3676653 baseEnd_3676653 := by
    simpa [prefixWord, tailWord_3676653, baseEnd_3676653] using wordTrace_append hprefix tailTrace_3676653
  have hstable : (prefixWord ++ tailWord_3676653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676653).length < 2 ^ (prefixWord ++ tailWord_3676653).sum := by decide
  have hdescent : baseEnd_3676653 < baseStart_3676653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676666 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3676666 : Nat := 118140960795 + 3676666 * 2 ^ 59
def prefixEnd_3676666 : Nat := 4983230072969 + 3 ^ 40 * 3676666 * 2
def baseEnd_3676666 : Nat := 1258597909362411507377551

theorem tailTrace_3676666 : CollatzResearch.WordTrace tailWord_3676666 prefixEnd_3676666 1258597909362411507377551 := by
  unfold tailWord_3676666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33524756424518620351570463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89399350465382987604187901 33524756424518620351570463)
  ·
    refine ⟨50287134636777930527355695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33524756424518620351570463 50287134636777930527355695)
    ·
      refine ⟨75430701955166895791033543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50287134636777930527355695 75430701955166895791033543)
      ·
        refine ⟨113146052932750343686550315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75430701955166895791033543 113146052932750343686550315)
        ·
          refine ⟨169719079399125515529825473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113146052932750343686550315 169719079399125515529825473)
          ·
            refine ⟨127289309549344136647369105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169719079399125515529825473 127289309549344136647369105)
            ·
              refine ⟨95466982162008102485526829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127289309549344136647369105 95466982162008102485526829)
              ·
                refine ⟨35800118310753038432072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95466982162008102485526829 35800118310753038432072561)
                ·
                  refine ⟨26850088733064778824054421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35800118310753038432072561 26850088733064778824054421)
                  ·
                    refine ⟨1258597909362411507377551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26850088733064778824054421 1258597909362411507377551)
                    ·
                      rfl

theorem cell22_3676666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3676666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676666 prefixEnd_3676666 := by exact prefixLift 3676666
  have htrace : WordTrace (prefixWord ++ tailWord_3676666) baseStart_3676666 baseEnd_3676666 := by
    simpa [prefixWord, tailWord_3676666, baseEnd_3676666] using wordTrace_append hprefix tailTrace_3676666
  have hstable : (prefixWord ++ tailWord_3676666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676666).length < 2 ^ (prefixWord ++ tailWord_3676666).sum := by decide
  have hdescent : baseEnd_3676666 < baseStart_3676666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676674 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3676674 : Nat := 118140960795 + 3676674 * 2 ^ 59
def prefixEnd_3676674 : Nat := 4983230072969 + 3 ^ 40 * 3676674 * 2
def baseEnd_3676674 : Nat := 1258600647925902153177527

theorem tailTrace_3676674 : CollatzResearch.WordTrace tailWord_3676674 prefixEnd_3676674 1258600647925902153177527 := by
  unfold tailWord_3676674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33524829370511374693143269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89399544988030332515048717 33524829370511374693143269)
  ·
    refine ⟨6285905506970882754964363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33524829370511374693143269 6285905506970882754964363)
    ·
      refine ⟨9428858260456324132446545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285905506970882754964363 9428858260456324132446545)
      ·
        refine ⟨7071643695342243099334909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9428858260456324132446545 7071643695342243099334909)
        ·
          refine ⟨2651866385753341162250591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7071643695342243099334909 2651866385753341162250591)
          ·
            refine ⟨3977799578630011743375887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651866385753341162250591 3977799578630011743375887)
            ·
              refine ⟨5966699367945017615063831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977799578630011743375887 5966699367945017615063831)
              ·
                refine ⟨8950049051917526422595747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966699367945017615063831 8950049051917526422595747)
                ·
                  refine ⟨13425073577876289633893621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950049051917526422595747 13425073577876289633893621)
                  ·
                    refine ⟨1258600647925902153177527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13425073577876289633893621 1258600647925902153177527)
                    ·
                      rfl

theorem cell22_3676674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3676674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676674 prefixEnd_3676674 := by exact prefixLift 3676674
  have htrace : WordTrace (prefixWord ++ tailWord_3676674) baseStart_3676674 baseEnd_3676674 := by
    simpa [prefixWord, tailWord_3676674, baseEnd_3676674] using wordTrace_append hprefix tailTrace_3676674
  have hstable : (prefixWord ++ tailWord_3676674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676674).length < 2 ^ (prefixWord ++ tailWord_3676674).sum := by decide
  have hdescent : baseEnd_3676674 < baseStart_3676674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676728 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_3676728 : Nat := 118140960795 + 3676728 * 2 ^ 59
def prefixEnd_3676728 : Nat := 4983230072969 + 3 ^ 40 * 3676728 * 2
def baseEnd_3676728 : Nat := 1258619133229464012327361

theorem tailTrace_3676728 : CollatzResearch.WordTrace tailWord_3676728 prefixEnd_3676728 1258619133229464012327361 := by
  unfold tailWord_3676728
  simp only [CollatzResearch.WordTrace]
  refine ⟨67050643511924932997519419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89400858015899910663359225 67050643511924932997519419)
  ·
    refine ⟨100575965267887399496279129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67050643511924932997519419 100575965267887399496279129)
    ·
      refine ⟨75431973950915549622209347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100575965267887399496279129 75431973950915549622209347)
      ·
        refine ⟨113147960926373324433314021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75431973950915549622209347 113147960926373324433314021)
        ·
          refine ⟨21215242673694998331246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113147960926373324433314021 21215242673694998331246379)
          ·
            refine ⟨31822864010542497496869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21215242673694998331246379 31822864010542497496869569)
            ·
              refine ⟨23867148007906873122652177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31822864010542497496869569 23867148007906873122652177)
              ·
                refine ⟨17900361005930154841989133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23867148007906873122652177 17900361005930154841989133)
                ·
                  refine ⟨6712635377223808065745925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17900361005930154841989133 6712635377223808065745925)
                  ·
                    refine ⟨1258619133229464012327361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6712635377223808065745925 1258619133229464012327361)
                    ·
                      rfl

theorem cell22_3676728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_3676728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676728 prefixEnd_3676728 := by exact prefixLift 3676728
  have htrace : WordTrace (prefixWord ++ tailWord_3676728) baseStart_3676728 baseEnd_3676728 := by
    simpa [prefixWord, tailWord_3676728, baseEnd_3676728] using wordTrace_append hprefix tailTrace_3676728
  have hstable : (prefixWord ++ tailWord_3676728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676728).length < 2 ^ (prefixWord ++ tailWord_3676728).sum := by decide
  have hdescent : baseEnd_3676728 < baseStart_3676728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676732 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_3676732 : Nat := 118140960795 + 3676732 * 2 ^ 59
def prefixEnd_3676732 : Nat := 4983230072969 + 3 ^ 40 * 3676732 * 2
def baseEnd_3676732 : Nat := 419540167503736445075783

theorem tailTrace_3676732 : CollatzResearch.WordTrace tailWord_3676732 prefixEnd_3676732 419540167503736445075783 := by
  unfold tailWord_3676732
  simp only [CollatzResearch.WordTrace]
  refine ⟨67050716457917687339092225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89400955277223583118789633 67050716457917687339092225)
  ·
    refine ⟨50288037343438265504319169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67050716457917687339092225 50288037343438265504319169)
    ·
      refine ⟨37716028007578699128239377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50288037343438265504319169 37716028007578699128239377)
      ·
        refine ⟨28287021005684024346179533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37716028007578699128239377 28287021005684024346179533)
        ·
          refine ⟨10607632877131509129817325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28287021005684024346179533 10607632877131509129817325)
          ·
            refine ⟨3977862328924315923681497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10607632877131509129817325 3977862328924315923681497)
            ·
              refine ⟨2983396746693236942761123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977862328924315923681497 2983396746693236942761123)
              ·
                refine ⟨4475095120039855414141685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983396746693236942761123 4475095120039855414141685)
                ·
                  refine ⟨419540167503736445075783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475095120039855414141685 419540167503736445075783)
                  ·
                    rfl

theorem cell22_3676732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_3676732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676732 prefixEnd_3676732 := by exact prefixLift 3676732
  have htrace : WordTrace (prefixWord ++ tailWord_3676732) baseStart_3676732 baseEnd_3676732 := by
    simpa [prefixWord, tailWord_3676732, baseEnd_3676732] using wordTrace_append hprefix tailTrace_3676732
  have hstable : (prefixWord ++ tailWord_3676732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676732).length < 2 ^ (prefixWord ++ tailWord_3676732).sum := by decide
  have hdescent : baseEnd_3676732 < baseStart_3676732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676766 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3676766 : Nat := 118140960795 + 3676766 * 2 ^ 59
def prefixEnd_3676766 : Nat := 4983230072969 + 3 ^ 40 * 3676766 * 2
def baseEnd_3676766 : Nat := 419544047135348193292415

theorem tailTrace_3676766 : CollatzResearch.WordTrace tailWord_3676766 prefixEnd_3676766 419544047135348193292415 := by
  unfold tailWord_3676766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762834124714024810615269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89401781998474798989948101 16762834124714024810615269)
  ·
    refine ⟨3143031398383879651990363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16762834124714024810615269 3143031398383879651990363)
    ·
      refine ⟨4714547097575819477985545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143031398383879651990363 4714547097575819477985545)
      ·
        refine ⟨3535910323181864608489159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4714547097575819477985545 3535910323181864608489159)
        ·
          refine ⟨5303865484772796912733739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535910323181864608489159 5303865484772796912733739)
          ·
            refine ⟨7955798227159195369100609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303865484772796912733739 7955798227159195369100609)
            ·
              refine ⟨5966848670369396526825457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7955798227159195369100609 5966848670369396526825457)
              ·
                refine ⟨4475136502777047395119093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966848670369396526825457 4475136502777047395119093)
                ·
                  refine ⟨419544047135348193292415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475136502777047395119093 419544047135348193292415)
                  ·
                    rfl

theorem cell22_3676766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3676766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676766 prefixEnd_3676766 := by exact prefixLift 3676766
  have htrace : WordTrace (prefixWord ++ tailWord_3676766) baseStart_3676766 baseEnd_3676766 := by
    simpa [prefixWord, tailWord_3676766, baseEnd_3676766] using wordTrace_append hprefix tailTrace_3676766
  have hstable : (prefixWord ++ tailWord_3676766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676766).length < 2 ^ (prefixWord ++ tailWord_3676766).sum := by decide
  have hdescent : baseEnd_3676766 < baseStart_3676766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676770 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3676770 : Nat := 118140960795 + 3676770 * 2 ^ 59
def prefixEnd_3676770 : Nat := 4983230072969 + 3 ^ 40 * 3676770 * 2
def baseEnd_3676770 : Nat := 1258633510687789902777233

theorem tailTrace_3676770 : CollatzResearch.WordTrace tailWord_3676770 prefixEnd_3676770 1258633510687789902777233 := by
  unfold tailWord_3676770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33525704722424426792016941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89401879259798471445378509 33525704722424426792016941)
  ·
    refine ⟨12572139270909160047006353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33525704722424426792016941 12572139270909160047006353)
    ·
      refine ⟨9429104453181870035254765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12572139270909160047006353 9429104453181870035254765)
      ·
        refine ⟨3535914169943201263220537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9429104453181870035254765 3535914169943201263220537)
        ·
          refine ⟨2651935627457400947415403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535914169943201263220537 2651935627457400947415403)
          ·
            refine ⟨3977903441186101421123105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651935627457400947415403 3977903441186101421123105)
            ·
              refine ⟨2983427580889576065842329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977903441186101421123105 2983427580889576065842329)
              ·
                refine ⟨2237570685667182049381747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983427580889576065842329 2237570685667182049381747)
                ·
                  refine ⟨3356356028500773074072621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237570685667182049381747 3356356028500773074072621)
                  ·
                    refine ⟨1258633510687789902777233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356356028500773074072621 1258633510687789902777233)
                    ·
                      rfl

theorem cell22_3676770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3676770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676770 prefixEnd_3676770 := by exact prefixLift 3676770
  have htrace : WordTrace (prefixWord ++ tailWord_3676770) baseStart_3676770 baseEnd_3676770 := by
    simpa [prefixWord, tailWord_3676770, baseEnd_3676770] using wordTrace_append hprefix tailTrace_3676770
  have hstable : (prefixWord ++ tailWord_3676770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676770).length < 2 ^ (prefixWord ++ tailWord_3676770).sum := by decide
  have hdescent : baseEnd_3676770 < baseStart_3676770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676805 : List Nat := [1, 3, 1, 1, 4, 3, 3, 6]
def baseStart_3676805 : Nat := 118140960795 + 3676805 * 2 ^ 59
def prefixEnd_3676805 : Nat := 4983230072969 + 3 ^ 40 * 3676805 * 2
def baseEnd_3676805 : Nat := 139849499100340164239125

theorem tailTrace_3676805 : CollatzResearch.WordTrace tailWord_3676805 prefixEnd_3676805 139849499100340164239125 := by
  unfold tailWord_3676805
  simp only [CollatzResearch.WordTrace]
  refine ⟨134104095444570908145591869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89402730296380605430394579 134104095444570908145591869)
  ·
    refine ⟨50289035791714090554596951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134104095444570908145591869 50289035791714090554596951)
    ·
      refine ⟨75433553687571135831895427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50289035791714090554596951 75433553687571135831895427)
      ·
        refine ⟨113150330531356703747843141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75433553687571135831895427 113150330531356703747843141)
        ·
          refine ⟨21215686974629381952720589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113150330531356703747843141 21215686974629381952720589)
          ·
            refine ⟨7955882615486018232270221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21215686974629381952720589 7955882615486018232270221)
            ·
              refine ⟨2983455980807256837101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7955882615486018232270221 2983455980807256837101333)
              ·
                refine ⟨139849499100340164239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2983455980807256837101333 139849499100340164239125)
                ·
                  rfl

theorem cell22_3676805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 6].length) (baseStart_3676805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676805 prefixEnd_3676805 := by exact prefixLift 3676805
  have htrace : WordTrace (prefixWord ++ tailWord_3676805) baseStart_3676805 baseEnd_3676805 := by
    simpa [prefixWord, tailWord_3676805, baseEnd_3676805] using wordTrace_append hprefix tailTrace_3676805
  have hstable : (prefixWord ++ tailWord_3676805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676805).length < 2 ^ (prefixWord ++ tailWord_3676805).sum := by decide
  have hdescent : baseEnd_3676805 < baseStart_3676805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676826 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_3676826 : Nat := 118140960795 + 3676826 * 2 ^ 59
def prefixEnd_3676826 : Nat := 4983230072969 + 3 ^ 40 * 3676826 * 2
def baseEnd_3676826 : Nat := 1258652680632224423377061

theorem tailTrace_3676826 : CollatzResearch.WordTrace tailWord_3676826 prefixEnd_3676826 1258652680632224423377061 := by
  unfold tailWord_3676826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526215344373707183026583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89403240918329885821404221 33526215344373707183026583)
  ·
    refine ⟨50289323016560560774539875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33526215344373707183026583 50289323016560560774539875)
    ·
      refine ⟨75433984524840841161809813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50289323016560560774539875 75433984524840841161809813)
      ·
        refine ⟨3535968024601914429459835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75433984524840841161809813 3535968024601914429459835)
        ·
          refine ⟨5303952036902871644189753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535968024601914429459835 5303952036902871644189753)
          ·
            refine ⟨3977964027677153733142315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303952036902871644189753 3977964027677153733142315)
            ·
              refine ⟨5966946041515730599713473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977964027677153733142315 5966946041515730599713473)
              ·
                refine ⟨4475209531136797949785105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966946041515730599713473 4475209531136797949785105)
                ·
                  refine ⟨3356407148352598462338829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475209531136797949785105 3356407148352598462338829)
                  ·
                    refine ⟨1258652680632224423377061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356407148352598462338829 1258652680632224423377061)
                    ·
                      rfl

theorem cell22_3676826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_3676826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676826 prefixEnd_3676826 := by exact prefixLift 3676826
  have htrace : WordTrace (prefixWord ++ tailWord_3676826) baseStart_3676826 baseEnd_3676826 := by
    simpa [prefixWord, tailWord_3676826, baseEnd_3676826] using wordTrace_append hprefix tailTrace_3676826
  have hstable : (prefixWord ++ tailWord_3676826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676826).length < 2 ^ (prefixWord ++ tailWord_3676826).sum := by decide
  have hdescent : baseEnd_3676826 < baseStart_3676826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676895 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 6]
def baseStart_3676895 : Nat := 118140960795 + 3676895 * 2 ^ 59
def prefixEnd_3676895 : Nat := 4983230072969 + 3 ^ 40 * 3676895 * 2
def baseEnd_3676895 : Nat := 419558766914110414467283

theorem tailTrace_3676895 : CollatzResearch.WordTrace tailWord_3676895 prefixEnd_3676895 419558766914110414467283 := by
  unfold tailWord_3676895
  simp only [CollatzResearch.WordTrace]
  refine ⟨134107378014244853516368139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89404918676163235677578759 134107378014244853516368139)
  ·
    refine ⟨201161067021367280274552209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134107378014244853516368139 201161067021367280274552209)
    ·
      refine ⟨150870800266025460205914157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201161067021367280274552209 150870800266025460205914157)
      ·
        refine ⟨56576550099759547577217809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150870800266025460205914157 56576550099759547577217809)
        ·
          refine ⟨42432412574819660682913357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56576550099759547577217809 42432412574819660682913357)
          ·
            refine ⟨15912154715557372756092509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42432412574819660682913357 15912154715557372756092509)
            ·
              refine ⟨5967058018334014783534691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15912154715557372756092509 5967058018334014783534691)
              ·
                refine ⟨8950587027501022175302037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967058018334014783534691 8950587027501022175302037)
                ·
                  refine ⟨419558766914110414467283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8950587027501022175302037 419558766914110414467283)
                  ·
                    rfl

theorem cell22_3676895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_3676895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676895 prefixEnd_3676895 := by exact prefixLift 3676895
  have htrace : WordTrace (prefixWord ++ tailWord_3676895) baseStart_3676895 baseEnd_3676895 := by
    simpa [prefixWord, tailWord_3676895, baseEnd_3676895] using wordTrace_append hprefix tailTrace_3676895
  have hstable : (prefixWord ++ tailWord_3676895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676895).length < 2 ^ (prefixWord ++ tailWord_3676895).sum := by decide
  have hdescent : baseEnd_3676895 < baseStart_3676895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676914 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_3676914 : Nat := 118140960795 + 3676914 * 2 ^ 59
def prefixEnd_3676914 : Nat := 4983230072969 + 3 ^ 40 * 3676914 * 2
def baseEnd_3676914 : Nat := 1258682804830621527176791

theorem tailTrace_3676914 : CollatzResearch.WordTrace tailWord_3676914 prefixEnd_3676914 1258682804830621527176791 := by
  unfold tailWord_3676914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527017750294004940327449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89405380667450679840873197 33527017750294004940327449)
  ·
    refine ⟨25145263312720503705245587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33527017750294004940327449 25145263312720503705245587)
    ·
      refine ⟨37717894969080755557868381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25145263312720503705245587 37717894969080755557868381)
      ·
        refine ⟨14144210613405283334200643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37717894969080755557868381 14144210613405283334200643)
        ·
          refine ⟨21216315920107925001300965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144210613405283334200643 21216315920107925001300965)
          ·
            refine ⟨3978059235020235937743931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21216315920107925001300965 3978059235020235937743931)
            ·
              refine ⟨5967088852530353906615897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978059235020235937743931 5967088852530353906615897)
              ·
                refine ⟨4475316639397765429961923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5967088852530353906615897 4475316639397765429961923)
                ·
                  refine ⟨6712974959096648144942885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475316639397765429961923 6712974959096648144942885)
                  ·
                    refine ⟨1258682804830621527176791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6712974959096648144942885 1258682804830621527176791)
                    ·
                      rfl

theorem cell22_3676914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_3676914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676914 prefixEnd_3676914 := by exact prefixLift 3676914
  have htrace : WordTrace (prefixWord ++ tailWord_3676914) baseStart_3676914 baseEnd_3676914 := by
    simpa [prefixWord, tailWord_3676914, baseEnd_3676914] using wordTrace_append hprefix tailTrace_3676914
  have hstable : (prefixWord ++ tailWord_3676914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676914).length < 2 ^ (prefixWord ++ tailWord_3676914).sum := by decide
  have hdescent : baseEnd_3676914 < baseStart_3676914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676946 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_3676946 : Nat := 118140960795 + 3676946 * 2 ^ 59
def prefixEnd_3676946 : Nat := 4983230072969 + 3 ^ 40 * 3676946 * 2
def baseEnd_3676946 : Nat := 419564586361528036792231

theorem tailTrace_3676946 : CollatzResearch.WordTrace tailWord_3676946 prefixEnd_3676946 419564586361528036792231 := by
  unfold tailWord_3676946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527309534265022306618673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89406158758040059484316461 33527309534265022306618673)
  ·
    refine ⟨25145482150698766729964005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33527309534265022306618673 25145482150698766729964005)
    ·
      refine ⟨4714777903256018761868251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25145482150698766729964005 4714777903256018761868251)
      ·
        refine ⟨7072166854884028142802377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714777903256018761868251 7072166854884028142802377)
        ·
          refine ⟨5304125141163021107101783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7072166854884028142802377 5304125141163021107101783)
          ·
            refine ⟨7956187711744531660652675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304125141163021107101783 7956187711744531660652675)
            ·
              refine ⟨11934281567616797490979013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956187711744531660652675 11934281567616797490979013)
              ·
                refine ⟨2237677793928149529558565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11934281567616797490979013 2237677793928149529558565)
                ·
                  refine ⟨419564586361528036792231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2237677793928149529558565 419564586361528036792231)
                  ·
                    rfl

theorem cell22_3676946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_3676946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676946 prefixEnd_3676946 := by exact prefixLift 3676946
  have htrace : WordTrace (prefixWord ++ tailWord_3676946) baseStart_3676946 baseEnd_3676946 := by
    simpa [prefixWord, tailWord_3676946, baseEnd_3676946] using wordTrace_append hprefix tailTrace_3676946
  have hstable : (prefixWord ++ tailWord_3676946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676946).length < 2 ^ (prefixWord ++ tailWord_3676946).sum := by decide
  have hdescent : baseEnd_3676946 < baseStart_3676946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676972 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_3676972 : Nat := 118140960795 + 3676972 * 2 ^ 59
def prefixEnd_3676972 : Nat := 4983230072969 + 3 ^ 40 * 3676972 * 2
def baseEnd_3676972 : Nat := 1258702659415928709226613

theorem tailTrace_3676972 : CollatzResearch.WordTrace tailWord_3676972 prefixEnd_3676972 1258702659415928709226613 := by
  unfold tailWord_3676972
  simp only [CollatzResearch.WordTrace]
  refine ⟨67055093217482947833460585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89406790956643930444614113 67055093217482947833460585)
  ·
    refine ⟨50291319913112210875095439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67055093217482947833460585 50291319913112210875095439)
    ·
      refine ⟨75436979869668316312643159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50291319913112210875095439 75436979869668316312643159)
      ·
        refine ⟨113155469804502474468964739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75436979869668316312643159 113155469804502474468964739)
        ·
          refine ⟨169733204706753711703447109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113155469804502474468964739 169733204706753711703447109)
          ·
            refine ⟨31824975882516320944396333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169733204706753711703447109 31824975882516320944396333)
            ·
              refine ⟨11934365955943620354148625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31824975882516320944396333 11934365955943620354148625)
              ·
                refine ⟨8950774466957715265611469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934365955943620354148625 8950774466957715265611469)
                ·
                  refine ⟨3356540425109143224604301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8950774466957715265611469 3356540425109143224604301)
                  ·
                    refine ⟨1258702659415928709226613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356540425109143224604301 1258702659415928709226613)
                    ·
                      rfl

theorem cell22_3676972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_3676972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676972 prefixEnd_3676972 := by exact prefixLift 3676972
  have htrace : WordTrace (prefixWord ++ tailWord_3676972) baseStart_3676972 baseEnd_3676972 := by
    simpa [prefixWord, tailWord_3676972, baseEnd_3676972] using wordTrace_append hprefix tailTrace_3676972
  have hstable : (prefixWord ++ tailWord_3676972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676972).length < 2 ^ (prefixWord ++ tailWord_3676972).sum := by decide
  have hdescent : baseEnd_3676972 < baseStart_3676972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676974 : List Nat := [4, 1, 3, 2, 1, 2, 3, 6]
def baseStart_3676974 : Nat := 118140960795 + 3676974 * 2 ^ 59
def prefixEnd_3676974 : Nat := 4983230072969 + 3 ^ 40 * 3676974 * 2
def baseEnd_3676974 : Nat := 139855927117422374519623

theorem tailTrace_3676974 : CollatzResearch.WordTrace tailWord_3676974 prefixEnd_3676974 139855927117422374519623 := by
  unfold tailWord_3676974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763782422619831251061747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89406839587305766672329317 16763782422619831251061747)
  ·
    refine ⟨25145673633929746876592621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16763782422619831251061747 25145673633929746876592621)
    ·
      refine ⟨9429627612723655078722233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25145673633929746876592621 9429627612723655078722233)
      ·
        refine ⟨7072220709542741309041675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429627612723655078722233 7072220709542741309041675)
        ·
          refine ⟨10608331064314111963562513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072220709542741309041675 10608331064314111963562513)
          ·
            refine ⟨7956248298235583972671885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608331064314111963562513 7956248298235583972671885)
            ·
              refine ⟨2983593111838343989751957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7956248298235583972671885 2983593111838343989751957)
              ·
                refine ⟨139855927117422374519623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2983593111838343989751957 139855927117422374519623)
                ·
                  rfl

theorem cell22_3676974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_3676974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3676974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3676974 prefixEnd_3676974 := by exact prefixLift 3676974
  have htrace : WordTrace (prefixWord ++ tailWord_3676974) baseStart_3676974 baseEnd_3676974 := by
    simpa [prefixWord, tailWord_3676974, baseEnd_3676974] using wordTrace_append hprefix tailTrace_3676974
  have hstable : (prefixWord ++ tailWord_3676974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676974).length < 2 ^ (prefixWord ++ tailWord_3676974).sum := by decide
  have hdescent : baseEnd_3676974 < baseStart_3676974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677000 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3677000 : Nat := 118140960795 + 3677000 * 2 ^ 59
def prefixEnd_3677000 : Nat := 4983230072969 + 3 ^ 40 * 3677000 * 2
def baseEnd_3677000 : Nat := 1258712244388145969526527

theorem tailTrace_3677000 : CollatzResearch.WordTrace tailWord_3677000 prefixEnd_3677000 1258712244388145969526527 := by
  unfold tailWord_3677000
  simp only [CollatzResearch.WordTrace]
  refine ⟨67055603839432228224470227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89407471785909637632626969 67055603839432228224470227)
  ·
    refine ⟨100583405759148342336705341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67055603839432228224470227 100583405759148342336705341)
    ·
      refine ⟨37718777159680628376264503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100583405759148342336705341 37718777159680628376264503)
      ·
        refine ⟨56578165739520942564396755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37718777159680628376264503 56578165739520942564396755)
        ·
          refine ⟨84867248609281413846595133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56578165739520942564396755 84867248609281413846595133)
          ·
            refine ⟨31825218228480530192473175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84867248609281413846595133 31825218228480530192473175)
            ·
              refine ⟨47737827342720795288709763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31825218228480530192473175 47737827342720795288709763)
              ·
                refine ⟨71606741014081192933064645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47737827342720795288709763 71606741014081192933064645)
                ·
                  refine ⟨13426263940140223674949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71606741014081192933064645 13426263940140223674949621)
                  ·
                    refine ⟨1258712244388145969526527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13426263940140223674949621 1258712244388145969526527)
                    ·
                      rfl

theorem cell22_3677000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3677000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677000 prefixEnd_3677000 := by exact prefixLift 3677000
  have htrace : WordTrace (prefixWord ++ tailWord_3677000) baseStart_3677000 baseEnd_3677000 := by
    simpa [prefixWord, tailWord_3677000, baseEnd_3677000] using wordTrace_append hprefix tailTrace_3677000
  have hstable : (prefixWord ++ tailWord_3677000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677000).length < 2 ^ (prefixWord ++ tailWord_3677000).sum := by decide
  have hdescent : baseEnd_3677000 < baseStart_3677000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677064 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_3677064 : Nat := 118140960795 + 3677064 * 2 ^ 59
def prefixEnd_3677064 : Nat := 4983230072969 + 3 ^ 40 * 3677064 * 2
def baseEnd_3677064 : Nat := 419578050965357045308777

theorem tailTrace_3677064 : CollatzResearch.WordTrace tailWord_3677064 prefixEnd_3677064 419578050965357045308777 := by
  unfold tailWord_3677064
  simp only [CollatzResearch.WordTrace]
  refine ⟨67056770975316297689635123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89409027967088396919513497 67056770975316297689635123)
  ·
    refine ⟨100585156462974446534452685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67056770975316297689635123 100585156462974446534452685)
    ·
      refine ⟨37719433673615417450419757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100585156462974446534452685 37719433673615417450419757)
      ·
        refine ⟨14144787627605781543907409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37719433673615417450419757 14144787627605781543907409)
        ·
          refine ⟨10608590720704336157930557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144787627605781543907409 10608590720704336157930557)
          ·
            refine ⟨3978221520264126059223959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10608590720704336157930557 3978221520264126059223959)
            ·
              refine ⟨5967332280396189088835939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978221520264126059223959 5967332280396189088835939)
              ·
                refine ⟨8950998420594283633253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967332280396189088835939 8950998420594283633253909)
                ·
                  refine ⟨419578050965357045308777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8950998420594283633253909 419578050965357045308777)
                  ·
                    rfl

theorem cell22_3677064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_3677064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677064 prefixEnd_3677064 := by exact prefixLift 3677064
  have htrace : WordTrace (prefixWord ++ tailWord_3677064) baseStart_3677064 baseEnd_3677064 := by
    simpa [prefixWord, tailWord_3677064, baseEnd_3677064] using wordTrace_append hprefix tailTrace_3677064
  have hstable : (prefixWord ++ tailWord_3677064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677064).length < 2 ^ (prefixWord ++ tailWord_3677064).sum := by decide
  have hdescent : baseEnd_3677064 < baseStart_3677064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677079 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 2, 3]
def baseStart_3677079 : Nat := 118140960795 + 3677079 * 2 ^ 59
def prefixEnd_3677079 : Nat := 4983230072969 + 3 ^ 40 * 3677079 * 2
def baseEnd_3677079 : Nat := 1258739287702616096801285

theorem tailTrace_3677079 : CollatzResearch.WordTrace tailWord_3677079 prefixEnd_3677079 1258739287702616096801285 := by
  unfold tailWord_3677079
  simp only [CollatzResearch.WordTrace]
  refine ⟨134114089045578252941066291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89409392697052168627377527 134114089045578252941066291)
  ·
    refine ⟨201171133568367379411599437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134114089045578252941066291 201171133568367379411599437)
    ·
      refine ⟨75439175088137767279349789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201171133568367379411599437 75439175088137767279349789)
      ·
        refine ⟨28289690658051662729756171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75439175088137767279349789 28289690658051662729756171)
        ·
          refine ⟨42434535987077494094634257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28289690658051662729756171 42434535987077494094634257)
          ·
            refine ⟨31825901990308120570975693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42434535987077494094634257 31825901990308120570975693)
            ·
              refine ⟨11934713246365545214115885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31825901990308120570975693 11934713246365545214115885)
              ·
                refine ⟨4475517467387079455293457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11934713246365545214115885 4475517467387079455293457)
                ·
                  refine ⟨3356638100540309591470093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475517467387079455293457 3356638100540309591470093)
                  ·
                    refine ⟨1258739287702616096801285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356638100540309591470093 1258739287702616096801285)
                    ·
                      rfl

theorem cell22_3677079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_3677079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677079 prefixEnd_3677079 := by exact prefixLift 3677079
  have htrace : WordTrace (prefixWord ++ tailWord_3677079) baseStart_3677079 baseEnd_3677079 := by
    simpa [prefixWord, tailWord_3677079, baseEnd_3677079] using wordTrace_append hprefix tailTrace_3677079
  have hstable : (prefixWord ++ tailWord_3677079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677079).length < 2 ^ (prefixWord ++ tailWord_3677079).sum := by decide
  have hdescent : baseEnd_3677079 < baseStart_3677079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677107 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 7, 3]
def baseStart_3677107 : Nat := 118140960795 + 3677107 * 2 ^ 59
def prefixEnd_3677107 : Nat := 4983230072969 + 3 ^ 40 * 3677107 * 2
def baseEnd_3677107 : Nat := 1258748872674833357101199

theorem tailTrace_3677107 : CollatzResearch.WordTrace tailWord_3677107 prefixEnd_3677107 1258748872674833357101199 := by
  unfold tailWord_3677107
  simp only [CollatzResearch.WordTrace]
  refine ⟨134115110289476813723085575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89410073526317875815390383 134115110289476813723085575)
  ·
    refine ⟨201172665434215220584628363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134115110289476813723085575 201172665434215220584628363)
    ·
      refine ⟨301758998151322830876942545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201172665434215220584628363 301758998151322830876942545)
      ·
        refine ⟨226319248613492123157706909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301758998151322830876942545 226319248613492123157706909)
        ·
          refine ⟨84869718230059546184140091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226319248613492123157706909 84869718230059546184140091)
          ·
            refine ⟨127304577345089319276210137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84869718230059546184140091 127304577345089319276210137)
            ·
              refine ⟨95478433008816989457157603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127304577345089319276210137 95478433008816989457157603)
              ·
                refine ⟨143217649513225484185736405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95478433008816989457157603 143217649513225484185736405)
                ·
                  refine ⟨3356663660466222285603197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143217649513225484185736405 3356663660466222285603197)
                  ·
                    refine ⟨1258748872674833357101199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356663660466222285603197 1258748872674833357101199)
                    ·
                      rfl

theorem cell22_3677107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].length) (baseStart_3677107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677107 prefixEnd_3677107 := by exact prefixLift 3677107
  have htrace : WordTrace (prefixWord ++ tailWord_3677107) baseStart_3677107 baseEnd_3677107 := by
    simpa [prefixWord, tailWord_3677107, baseEnd_3677107] using wordTrace_append hprefix tailTrace_3677107
  have hstable : (prefixWord ++ tailWord_3677107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677107).length < 2 ^ (prefixWord ++ tailWord_3677107).sum := by decide
  have hdescent : baseEnd_3677107 < baseStart_3677107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677137 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 5]
def baseStart_3677137 : Nat := 118140960795 + 3677137 * 2 ^ 59
def prefixEnd_3677137 : Nat := 4983230072969 + 3 ^ 40 * 3677137 * 2
def baseEnd_3677137 : Nat := 419586380762641092950369

theorem tailTrace_3677137 : CollatzResearch.WordTrace tailWord_3677137 prefixEnd_3677137 419586380762641092950369 := by
  unfold tailWord_3677137
  simp only [CollatzResearch.WordTrace]
  refine ⟨134116204479368128846677665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89410802986245419231118443 134116204479368128846677665)
  ·
    refine ⟨100587153359526096635008249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134116204479368128846677665 100587153359526096635008249)
    ·
      refine ⟨75440365019644572476256187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100587153359526096635008249 75440365019644572476256187)
      ·
        refine ⟨113160547529466858714384281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75440365019644572476256187 113160547529466858714384281)
        ·
          refine ⟨84870410647100144035788211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113160547529466858714384281 84870410647100144035788211)
          ·
            refine ⟨127305615970650216053682317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84870410647100144035788211 127305615970650216053682317)
            ·
              refine ⟨47739605988993831020130869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127305615970650216053682317 47739605988993831020130869)
              ·
                refine ⟨4475588061468171658137269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47739605988993831020130869 4475588061468171658137269)
                ·
                  refine ⟨419586380762641092950369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475588061468171658137269 419586380762641092950369)
                  ·
                    rfl

theorem cell22_3677137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_3677137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677137 prefixEnd_3677137 := by exact prefixLift 3677137
  have htrace : WordTrace (prefixWord ++ tailWord_3677137) baseStart_3677137 baseEnd_3677137 := by
    simpa [prefixWord, tailWord_3677137, baseEnd_3677137] using wordTrace_append hprefix tailTrace_3677137
  have hstable : (prefixWord ++ tailWord_3677137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677137).length < 2 ^ (prefixWord ++ tailWord_3677137).sum := by decide
  have hdescent : baseEnd_3677137 < baseStart_3677137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677141 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3677141 : Nat := 118140960795 + 3677141 * 2 ^ 59
def prefixEnd_3677141 : Nat := 4983230072969 + 3 ^ 40 * 3677141 * 2
def baseEnd_3677141 : Nat := 1258760511569668601751095

theorem tailTrace_3677141 : CollatzResearch.WordTrace tailWord_3677141 prefixEnd_3677141 1258760511569668601751095 := by
  unfold tailWord_3677141
  simp only [CollatzResearch.WordTrace]
  refine ⟨134116350371353637529823277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89410900247569091686548851 134116350371353637529823277)
  ·
    refine ⟨50293631389257614073683729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134116350371353637529823277 50293631389257614073683729)
    ·
      refine ⟨37720223541943210555262797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50293631389257614073683729 37720223541943210555262797)
      ·
        refine ⟨14145083828228703958223549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37720223541943210555262797 14145083828228703958223549)
        ·
          refine ⟨5304406435585763984333831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14145083828228703958223549 5304406435585763984333831)
          ·
            refine ⟨7956609653378645976500747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304406435585763984333831 7956609653378645976500747)
            ·
              refine ⟨11934914480067968964751121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956609653378645976500747 11934914480067968964751121)
              ·
                refine ⟨8951185860050976723563341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934914480067968964751121 8951185860050976723563341)
                ·
                  refine ⟨3356694697519116271336253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8951185860050976723563341 3356694697519116271336253)
                  ·
                    refine ⟨1258760511569668601751095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356694697519116271336253 1258760511569668601751095)
                    ·
                      rfl

theorem cell22_3677141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3677141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677141 prefixEnd_3677141 := by exact prefixLift 3677141
  have htrace : WordTrace (prefixWord ++ tailWord_3677141) baseStart_3677141 baseEnd_3677141 := by
    simpa [prefixWord, tailWord_3677141, baseEnd_3677141] using wordTrace_append hprefix tailTrace_3677141
  have hstable : (prefixWord ++ tailWord_3677141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677141).length < 2 ^ (prefixWord ++ tailWord_3677141).sum := by decide
  have hdescent : baseEnd_3677141 < baseStart_3677141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677244 : List Nat := [2, 2, 2, 2, 2, 3, 2, 7]
def baseStart_3677244 : Nat := 118140960795 + 3677244 * 2 ^ 59
def prefixEnd_3677244 : Nat := 4983230072969 + 3 ^ 40 * 3677244 * 2
def baseEnd_3677244 : Nat := 139866196730512296269531

theorem tailTrace_3677244 : CollatzResearch.WordTrace tailWord_3677244 prefixEnd_3677244 139866196730512296269531 := by
  unfold tailWord_3677244
  simp only [CollatzResearch.WordTrace]
  refine ⟨67060053544990243060411393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89413404726653657413881857 67060053544990243060411393)
  ·
    refine ⟨50295040158742682295308545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67060053544990243060411393 50295040158742682295308545)
    ·
      refine ⟨37721280119057011721481409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50295040158742682295308545 37721280119057011721481409)
      ·
        refine ⟨28290960089292758791111057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37721280119057011721481409 28290960089292758791111057)
        ·
          refine ⟨21218220066969569093333293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28290960089292758791111057 21218220066969569093333293)
          ·
            refine ⟨7956832525113588409999985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21218220066969569093333293 7956832525113588409999985)
            ·
              refine ⟨5967624393835191307499989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956832525113588409999985 5967624393835191307499989)
              ·
                refine ⟨139866196730512296269531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5967624393835191307499989 139866196730512296269531)
                ·
                  rfl

theorem cell22_3677244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_3677244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677244 prefixEnd_3677244 := by exact prefixLift 3677244
  have htrace : WordTrace (prefixWord ++ tailWord_3677244) baseStart_3677244 baseEnd_3677244 := by
    simpa [prefixWord, tailWord_3677244, baseEnd_3677244] using wordTrace_append hprefix tailTrace_3677244
  have hstable : (prefixWord ++ tailWord_3677244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677244).length < 2 ^ (prefixWord ++ tailWord_3677244).sum := by decide
  have hdescent : baseEnd_3677244 < baseStart_3677244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677257 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3677257 : Nat := 118140960795 + 3677257 * 2 ^ 59
def prefixEnd_3677257 : Nat := 4983230072969 + 3 ^ 40 * 3677257 * 2
def baseEnd_3677257 : Nat := 1258800220740282965850739

theorem tailTrace_3677257 : CollatzResearch.WordTrace tailWord_3677257 prefixEnd_3677257 1258800220740282965850739 := by
  unfold tailWord_3677257
  simp only [CollatzResearch.WordTrace]
  refine ⟨134120581238933389341046025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89413720825955592894030683 134120581238933389341046025)
  ·
    refine ⟨100590435929200042005784519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134120581238933389341046025 100590435929200042005784519)
    ·
      refine ⟨150885653893800063008676779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100590435929200042005784519 150885653893800063008676779)
      ·
        refine ⟨226328480840700094513015169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150885653893800063008676779 226328480840700094513015169)
        ·
          refine ⟨169746360630525070884761377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226328480840700094513015169 169746360630525070884761377)
          ·
            refine ⟨127309770472893803163571033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169746360630525070884761377 127309770472893803163571033)
            ·
              refine ⟨95482327854670352372678275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127309770472893803163571033 95482327854670352372678275)
              ·
                refine ⟨143223491782005528559017413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95482327854670352372678275 143223491782005528559017413)
                ·
                  refine ⟨26854404709126036604815765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143223491782005528559017413 26854404709126036604815765)
                  ·
                    refine ⟨1258800220740282965850739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26854404709126036604815765 1258800220740282965850739)
                    ·
                      rfl

theorem cell22_3677257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3677257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677257 prefixEnd_3677257 := by exact prefixLift 3677257
  have htrace : WordTrace (prefixWord ++ tailWord_3677257) baseStart_3677257 baseEnd_3677257 := by
    simpa [prefixWord, tailWord_3677257, baseEnd_3677257] using wordTrace_append hprefix tailTrace_3677257
  have hstable : (prefixWord ++ tailWord_3677257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677257).length < 2 ^ (prefixWord ++ tailWord_3677257).sum := by decide
  have hdescent : baseEnd_3677257 < baseStart_3677257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677289 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 5]
def baseStart_3677289 : Nat := 118140960795 + 3677289 * 2 ^ 59
def prefixEnd_3677289 : Nat := 4983230072969 + 3 ^ 40 * 3677289 * 2
def baseEnd_3677289 : Nat := 419603724998081849683547

theorem tailTrace_3677289 : CollatzResearch.WordTrace tailWord_3677289 prefixEnd_3677289 419603724998081849683547 := by
  unfold tailWord_3677289
  simp only [CollatzResearch.WordTrace]
  refine ⟨134121748374817458806210921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89414498916544972537473947 134121748374817458806210921)
  ·
    refine ⟨100591311281113094104658191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134121748374817458806210921 100591311281113094104658191)
    ·
      refine ⟨150886966921669641156987287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100591311281113094104658191 150886966921669641156987287)
      ·
        refine ⟨226330450382504461735480931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150886966921669641156987287 226330450382504461735480931)
        ·
          refine ⟨339495675573756692603221397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226330450382504461735480931 339495675573756692603221397)
          ·
            refine ⟨15913859792519844965776003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339495675573756692603221397 15913859792519844965776003)
            ·
              refine ⟨23870789688779767448664005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15913859792519844965776003 23870789688779767448664005)
              ·
                refine ⟨4475773066646206396624501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23870789688779767448664005 4475773066646206396624501)
                ·
                  refine ⟨419603724998081849683547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4475773066646206396624501 419603724998081849683547)
                  ·
                    rfl

theorem cell22_3677289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_3677289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677289 prefixEnd_3677289 := by exact prefixLift 3677289
  have htrace : WordTrace (prefixWord ++ tailWord_3677289) baseStart_3677289 baseEnd_3677289 := by
    simpa [prefixWord, tailWord_3677289, baseEnd_3677289] using wordTrace_append hprefix tailTrace_3677289
  have hstable : (prefixWord ++ tailWord_3677289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677289).length < 2 ^ (prefixWord ++ tailWord_3677289).sum := by decide
  have hdescent : baseEnd_3677289 < baseStart_3677289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677351 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 6]
def baseStart_3677351 : Nat := 118140960795 + 3677351 * 2 ^ 59
def prefixEnd_3677351 : Nat := 4983230072969 + 3 ^ 40 * 3677351 * 2
def baseEnd_3677351 : Nat := 419610799620432684666817

theorem tailTrace_3677351 : CollatzResearch.WordTrace tailWord_3677351 prefixEnd_3677351 419610799620432684666817 := by
  unfold tailWord_3677351
  simp only [CollatzResearch.WordTrace]
  refine ⟨134124009700592843394967907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89416006467061895596645271 134124009700592843394967907)
  ·
    refine ⟨201186014550889265092451861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134124009700592843394967907 201186014550889265092451861)
    ·
      refine ⟨9430594432072934301208681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201186014550889265092451861 9430594432072934301208681)
      ·
        refine ⟨7072945824054700725906511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9430594432072934301208681 7072945824054700725906511)
        ·
          refine ⟨10609418736082051088859767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072945824054700725906511 10609418736082051088859767)
          ·
            refine ⟨15914128104123076633289651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609418736082051088859767 15914128104123076633289651)
            ·
              refine ⟨23871192156184614949934477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914128104123076633289651 23871192156184614949934477)
              ·
                refine ⟨8951697058569230606225429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23871192156184614949934477 8951697058569230606225429)
                ·
                  refine ⟨419610799620432684666817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8951697058569230606225429 419610799620432684666817)
                  ·
                    rfl

theorem cell22_3677351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_3677351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677351 prefixEnd_3677351 := by exact prefixLift 3677351
  have htrace : WordTrace (prefixWord ++ tailWord_3677351) baseStart_3677351 baseEnd_3677351 := by
    simpa [prefixWord, tailWord_3677351, baseEnd_3677351] using wordTrace_append hprefix tailTrace_3677351
  have hstable : (prefixWord ++ tailWord_3677351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677351).length < 2 ^ (prefixWord ++ tailWord_3677351).sum := by decide
  have hdescent : baseEnd_3677351 < baseStart_3677351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677503 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 4]
def baseStart_3677503 : Nat := 118140960795 + 3677503 * 2 ^ 59
def prefixEnd_3677503 : Nat := 4983230072969 + 3 ^ 40 * 3677503 * 2
def baseEnd_3677503 : Nat := 419628143855873441399995

theorem tailTrace_3677503 : CollatzResearch.WordTrace tailWord_3677503 prefixEnd_3677503 419628143855873441399995 := by
  unfold tailWord_3677503
  simp only [CollatzResearch.WordTrace]
  refine ⟨134129553596042173354501163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89419702397361448903000775 134129553596042173354501163)
  ·
    refine ⟨201194330394063260031751745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134129553596042173354501163 201194330394063260031751745)
    ·
      refine ⟨150895747795547445023813809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201194330394063260031751745 150895747795547445023813809)
      ·
        refine ⟨113171810846660583767860357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150895747795547445023813809 113171810846660583767860357)
        ·
          refine ⟨21219714533748859456473817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113171810846660583767860357 21219714533748859456473817)
          ·
            refine ⟨15914785900311644592355363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21219714533748859456473817 15914785900311644592355363)
            ·
              refine ⟨23872178850467466888533045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914785900311644592355363 23872178850467466888533045)
              ·
                refine ⟨2238016767231325020799973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23872178850467466888533045 2238016767231325020799973)
                ·
                  refine ⟨419628143855873441399995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238016767231325020799973 419628143855873441399995)
                  ·
                    rfl

theorem cell22_3677503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 4].length) (baseStart_3677503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677503 prefixEnd_3677503 := by exact prefixLift 3677503
  have htrace : WordTrace (prefixWord ++ tailWord_3677503) baseStart_3677503 baseEnd_3677503 := by
    simpa [prefixWord, tailWord_3677503, baseEnd_3677503] using wordTrace_append hprefix tailTrace_3677503
  have hstable : (prefixWord ++ tailWord_3677503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677503).length < 2 ^ (prefixWord ++ tailWord_3677503).sum := by decide
  have hdescent : baseEnd_3677503 < baseStart_3677503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677505 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3677505 : Nat := 118140960795 + 3677505 * 2 ^ 59
def prefixEnd_3677505 : Nat := 4983230072969 + 3 ^ 40 * 3677505 * 2
def baseEnd_3677505 : Nat := 1258885116208492985649979

theorem tailTrace_3677505 : CollatzResearch.WordTrace tailWord_3677505 prefixEnd_3677505 1258885116208492985649979 := by
  unfold tailWord_3677505
  simp only [CollatzResearch.WordTrace]
  refine ⟨134129626542034927696073969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89419751028023285130715979 134129626542034927696073969)
  ·
    refine ⟨100597219906526195772055477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134129626542034927696073969 100597219906526195772055477)
    ·
      refine ⟨9430989366236830853630201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100597219906526195772055477 9430989366236830853630201)
      ·
        refine ⟨7073242024677623140222651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9430989366236830853630201 7073242024677623140222651)
        ·
          refine ⟨10609863037016434710333977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073242024677623140222651 10609863037016434710333977)
          ·
            refine ⟨7957397277762326032750483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10609863037016434710333977 7957397277762326032750483)
            ·
              refine ⟨11936095916643489049125725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957397277762326032750483 11936095916643489049125725)
              ·
                refine ⟨4476035968741308393422147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11936095916643489049125725 4476035968741308393422147)
                ·
                  refine ⟨6714053953111962590133221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476035968741308393422147 6714053953111962590133221)
                  ·
                    refine ⟨1258885116208492985649979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714053953111962590133221 1258885116208492985649979)
                    ·
                      rfl

theorem cell22_3677505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3677505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677505 prefixEnd_3677505 := by exact prefixLift 3677505
  have htrace : WordTrace (prefixWord ++ tailWord_3677505) baseStart_3677505 baseEnd_3677505 := by
    simpa [prefixWord, tailWord_3677505, baseEnd_3677505] using wordTrace_append hprefix tailTrace_3677505
  have hstable : (prefixWord ++ tailWord_3677505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677505).length < 2 ^ (prefixWord ++ tailWord_3677505).sum := by decide
  have hdescent : baseEnd_3677505 < baseStart_3677505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677518 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3677518 : Nat := 118140960795 + 3677518 * 2 ^ 59
def prefixEnd_3677518 : Nat := 4983230072969 + 3 ^ 40 * 3677518 * 2
def baseEnd_3677518 : Nat := 1258889566374165285074939

theorem tailTrace_3677518 : CollatzResearch.WordTrace tailWord_3677518 prefixEnd_3677518 1258889566374165285074939 := by
  unfold tailWord_3677518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16766262586373478864537151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89420067127325220610864805 16766262586373478864537151)
  ·
    refine ⟨25149393879560218296805727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16766262586373478864537151 25149393879560218296805727)
    ·
      refine ⟨37724090819340327445208591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25149393879560218296805727 37724090819340327445208591)
      ·
        refine ⟨56586136229010491167812887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37724090819340327445208591 56586136229010491167812887)
        ·
          refine ⟨84879204343515736751719331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56586136229010491167812887 84879204343515736751719331)
          ·
            refine ⟨127318806515273605127578997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84879204343515736751719331 127318806515273605127578997)
            ·
              refine ⟨11936138110806900480710531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127318806515273605127578997 11936138110806900480710531)
              ·
                refine ⟨17904207166210350721065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11936138110806900480710531 17904207166210350721065797)
                ·
                  refine ⟨3357038843664440760199837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17904207166210350721065797 3357038843664440760199837)
                  ·
                    refine ⟨1258889566374165285074939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357038843664440760199837 1258889566374165285074939)
                    ·
                      rfl

theorem cell22_3677518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3677518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677518 prefixEnd_3677518 := by exact prefixLift 3677518
  have htrace : WordTrace (prefixWord ++ tailWord_3677518) baseStart_3677518 baseEnd_3677518 := by
    simpa [prefixWord, tailWord_3677518, baseEnd_3677518] using wordTrace_append hprefix tailTrace_3677518
  have hstable : (prefixWord ++ tailWord_3677518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677518).length < 2 ^ (prefixWord ++ tailWord_3677518).sum := by decide
  have hdescent : baseEnd_3677518 < baseStart_3677518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677526 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3677526 : Nat := 118140960795 + 3677526 * 2 ^ 59
def prefixEnd_3677526 : Nat := 4983230072969 + 3 ^ 40 * 3677526 * 2
def baseEnd_3677526 : Nat := 419630768312551976958305

theorem tailTrace_3677526 : CollatzResearch.WordTrace tailWord_3677526 prefixEnd_3677526 419630768312551976958305 := by
  unfold tailWord_3677526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8383149529684928017661777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89420261649972565521725621 8383149529684928017661777)
  ·
    refine ⟨6287362147263696013246333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8383149529684928017661777 6287362147263696013246333)
    ·
      refine ⟨2357760805223886004967375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6287362147263696013246333 2357760805223886004967375)
      ·
        refine ⟨3536641207835829007451063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357760805223886004967375 3536641207835829007451063)
        ·
          refine ⟨5304961811753743511176595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536641207835829007451063 5304961811753743511176595)
          ·
            refine ⟨7957442717630615266764893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304961811753743511176595 7957442717630615266764893)
            ·
              refine ⟨2984041019111480725036835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7957442717630615266764893 2984041019111480725036835)
              ·
                refine ⟨4476061528667221087555253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984041019111480725036835 4476061528667221087555253)
                ·
                  refine ⟨419630768312551976958305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476061528667221087555253 419630768312551976958305)
                  ·
                    rfl

theorem cell22_3677526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3677526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677526 prefixEnd_3677526 := by exact prefixLift 3677526
  have htrace : WordTrace (prefixWord ++ tailWord_3677526) baseStart_3677526 baseEnd_3677526 := by
    simpa [prefixWord, tailWord_3677526, baseEnd_3677526] using wordTrace_append hprefix tailTrace_3677526
  have hstable : (prefixWord ++ tailWord_3677526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677526).length < 2 ^ (prefixWord ++ tailWord_3677526).sum := by decide
  have hdescent : baseEnd_3677526 < baseStart_3677526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677548 : List Nat := [2, 2, 1, 1, 5, 1, 4, 6]
def baseStart_3677548 : Nat := 118140960795 + 3677548 * 2 ^ 59
def prefixEnd_3677548 : Nat := 4983230072969 + 3 ^ 40 * 3677548 * 2
def baseEnd_3677548 : Nat := 139877759554139467424983

theorem tailTrace_3677548 : CollatzResearch.WordTrace tailWord_3677548 prefixEnd_3677548 139877759554139467424983 := by
  unfold tailWord_3677548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065597440439573019944649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89420796587252764026592865 67065597440439573019944649)
  ·
    refine ⟨50299198080329679764958487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67065597440439573019944649 50299198080329679764958487)
    ·
      refine ⟨75448797120494519647437731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50299198080329679764958487 75448797120494519647437731)
      ·
        refine ⟨113173195680741779471156597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75448797120494519647437731 113173195680741779471156597)
        ·
          refine ⟨10609987095069541825420931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113173195680741779471156597 10609987095069541825420931)
          ·
            refine ⟨15914980642604312738131397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609987095069541825420931 15914980642604312738131397)
            ·
              refine ⟨2984058870488308638399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15914980642604312738131397 2984058870488308638399637)
              ·
                refine ⟨139877759554139467424983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2984058870488308638399637 139877759554139467424983)
                ·
                  rfl

theorem cell22_3677548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_3677548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677548 prefixEnd_3677548 := by exact prefixLift 3677548
  have htrace : WordTrace (prefixWord ++ tailWord_3677548) baseStart_3677548 baseEnd_3677548 := by
    simpa [prefixWord, tailWord_3677548, baseEnd_3677548] using wordTrace_append hprefix tailTrace_3677548
  have hstable : (prefixWord ++ tailWord_3677548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677548).length < 2 ^ (prefixWord ++ tailWord_3677548).sum := by decide
  have hdescent : baseEnd_3677548 < baseStart_3677548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677586 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3677586 : Nat := 118140960795 + 3677586 * 2 ^ 59
def prefixEnd_3677586 : Nat := 4983230072969 + 3 ^ 40 * 3677586 * 2
def baseEnd_3677586 : Nat := 1258912844163835774374731

theorem tailTrace_3677586 : CollatzResearch.WordTrace tailWord_3677586 prefixEnd_3677586 1258912844163835774374731 := by
  unfold tailWord_3677586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33533145213685369632443153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89421720569827652353181741 33533145213685369632443153)
  ·
    refine ⟨25149858910264027224332365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33533145213685369632443153 25149858910264027224332365)
    ·
      refine ⟨9431197091349010209124637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25149858910264027224332365 9431197091349010209124637)
      ·
        refine ⟨3536698909255878828421739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9431197091349010209124637 3536698909255878828421739)
        ·
          refine ⟨5305048363883818242632609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536698909255878828421739 5305048363883818242632609)
          ·
            refine ⟨3978786272912863681974457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5305048363883818242632609 3978786272912863681974457)
            ·
              refine ⟨2984089704684647761480843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978786272912863681974457 2984089704684647761480843)
              ·
                refine ⟨4476134557026971642221265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984089704684647761480843 4476134557026971642221265)
                ·
                  refine ⟨3357100917770228731665949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4476134557026971642221265 3357100917770228731665949)
                  ·
                    refine ⟨1258912844163835774374731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357100917770228731665949 1258912844163835774374731)
                    ·
                      rfl

theorem cell22_3677586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3677586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677586 prefixEnd_3677586 := by exact prefixLift 3677586
  have htrace : WordTrace (prefixWord ++ tailWord_3677586) baseStart_3677586 baseEnd_3677586 := by
    simpa [prefixWord, tailWord_3677586, baseEnd_3677586] using wordTrace_append hprefix tailTrace_3677586
  have hstable : (prefixWord ++ tailWord_3677586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677586).length < 2 ^ (prefixWord ++ tailWord_3677586).sum := by decide
  have hdescent : baseEnd_3677586 < baseStart_3677586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677591 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3677591 : Nat := 118140960795 + 3677591 * 2 ^ 59
def prefixEnd_3677591 : Nat := 4983230072969 + 3 ^ 40 * 3677591 * 2
def baseEnd_3677591 : Nat := 1258914555766017427999715

theorem tailTrace_3677591 : CollatzResearch.WordTrace tailWord_3677591 prefixEnd_3677591 1258914555766017427999715 := by
  unfold tailWord_3677591
  simp only [CollatzResearch.WordTrace]
  refine ⟨134132763219723364383704627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89421842146482242922469751 134132763219723364383704627)
  ·
    refine ⟨201199144829585046575556941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134132763219723364383704627 201199144829585046575556941)
    ·
      refine ⟨75449679311094392465833853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201199144829585046575556941 75449679311094392465833853)
      ·
        refine ⟨28293629741660397174687695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75449679311094392465833853 28293629741660397174687695)
        ·
          refine ⟨42440444612490595762031543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28293629741660397174687695 42440444612490595762031543)
          ·
            refine ⟨63660666918735893643047315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42440444612490595762031543 63660666918735893643047315)
            ·
              refine ⟨95491000378103840464570973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63660666918735893643047315 95491000378103840464570973)
              ·
                refine ⟨35809125141788940174214115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95491000378103840464570973 35809125141788940174214115)
                ·
                  refine ⟨53713687712683410261321173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35809125141788940174214115 53713687712683410261321173)
                  ·
                    refine ⟨1258914555766017427999715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53713687712683410261321173 1258914555766017427999715)
                    ·
                      rfl

theorem cell22_3677591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3677591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677591 prefixEnd_3677591 := by exact prefixLift 3677591
  have htrace : WordTrace (prefixWord ++ tailWord_3677591) baseStart_3677591 baseEnd_3677591 := by
    simpa [prefixWord, tailWord_3677591, baseEnd_3677591] using wordTrace_append hprefix tailTrace_3677591
  have hstable : (prefixWord ++ tailWord_3677591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677591).length < 2 ^ (prefixWord ++ tailWord_3677591).sum := by decide
  have hdescent : baseEnd_3677591 < baseStart_3677591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677593 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 5]
def baseStart_3677593 : Nat := 118140960795 + 3677593 * 2 ^ 59
def prefixEnd_3677593 : Nat := 4983230072969 + 3 ^ 40 * 3677593 * 2
def baseEnd_3677593 : Nat := 419638413468963363149903

theorem tailTrace_3677593 : CollatzResearch.WordTrace tailWord_3677593 prefixEnd_3677593 419638413468963363149903 := by
  unfold tailWord_3677593
  simp only [CollatzResearch.WordTrace]
  refine ⟨134132836165716118725277433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89421890777144079150184955 134132836165716118725277433)
  ·
    refine ⟨100599627124287089043958075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134132836165716118725277433 100599627124287089043958075)
    ·
      refine ⟨150899440686430633565937113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100599627124287089043958075 150899440686430633565937113)
      ·
        refine ⟨113174580514822975174452835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150899440686430633565937113 113174580514822975174452835)
        ·
          refine ⟨169761870772234462761679253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113174580514822975174452835 169761870772234462761679253)
          ·
            refine ⟨7957587692448490441953715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169761870772234462761679253 7957587692448490441953715)
            ·
              refine ⟨11936381538672735662930573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957587692448490441953715 11936381538672735662930573)
              ·
                refine ⟨4476143077002275873598965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11936381538672735662930573 4476143077002275873598965)
                ·
                  refine ⟨419638413468963363149903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476143077002275873598965 419638413468963363149903)
                  ·
                    rfl

theorem cell22_3677593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_3677593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677593 prefixEnd_3677593 := by exact prefixLift 3677593
  have htrace : WordTrace (prefixWord ++ tailWord_3677593) baseStart_3677593 baseEnd_3677593 := by
    simpa [prefixWord, tailWord_3677593, baseEnd_3677593] using wordTrace_append hprefix tailTrace_3677593
  have hstable : (prefixWord ++ tailWord_3677593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677593).length < 2 ^ (prefixWord ++ tailWord_3677593).sum := by decide
  have hdescent : baseEnd_3677593 < baseStart_3677593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677674 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3677674 : Nat := 118140960795 + 3677674 * 2 ^ 59
def prefixEnd_3677674 : Nat := 4983230072969 + 3 ^ 40 * 3677674 * 2
def baseEnd_3677674 : Nat := 1258942968362232878174461

theorem tailTrace_3677674 : CollatzResearch.WordTrace tailWord_3677674 prefixEnd_3677674 1258942968362232878174461 := by
  unfold tailWord_3677674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33533947619605667389744019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89423860318948446372650717 33533947619605667389744019)
  ·
    refine ⟨50300921429408501084616029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33533947619605667389744019 50300921429408501084616029)
    ·
      refine ⟨18862845536028187906731011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50300921429408501084616029 18862845536028187906731011)
      ·
        refine ⟨28294268304042281860096517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18862845536028187906731011 28294268304042281860096517)
        ·
          refine ⟨5305175307007927848768097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28294268304042281860096517 5305175307007927848768097)
          ·
            refine ⟨3978881480255945886576073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5305175307007927848768097 3978881480255945886576073)
            ·
              refine ⟨2984161110191959414932055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978881480255945886576073 2984161110191959414932055)
              ·
                refine ⟨4476241665287939122398083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984161110191959414932055 4476241665287939122398083)
                ·
                  refine ⟨6714362497931908683597125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476241665287939122398083 6714362497931908683597125)
                  ·
                    refine ⟨1258942968362232878174461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714362497931908683597125 1258942968362232878174461)
                    ·
                      rfl

theorem cell22_3677674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3677674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677674 prefixEnd_3677674 := by exact prefixLift 3677674
  have htrace : WordTrace (prefixWord ++ tailWord_3677674) baseStart_3677674 baseEnd_3677674 := by
    simpa [prefixWord, tailWord_3677674, baseEnd_3677674] using wordTrace_append hprefix tailTrace_3677674
  have hstable : (prefixWord ++ tailWord_3677674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677674).length < 2 ^ (prefixWord ++ tailWord_3677674).sum := by decide
  have hdescent : baseEnd_3677674 < baseStart_3677674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677715 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 3, 3]
def baseStart_3677715 : Nat := 118140960795 + 3677715 * 2 ^ 59
def prefixEnd_3677715 : Nat := 4983230072969 + 3 ^ 40 * 3677715 * 2
def baseEnd_3677715 : Nat := 1258957003500122437899335

theorem tailTrace_3677715 : CollatzResearch.WordTrace tailWord_3677715 prefixEnd_3677715 1258957003500122437899335 := by
  unfold tailWord_3677715
  simp only [CollatzResearch.WordTrace]
  refine ⟨134137285871274133561218599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89424857247516089040812399 134137285871274133561218599)
  ·
    refine ⟨201205928806911200341827899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134137285871274133561218599 201205928806911200341827899)
    ·
      refine ⟨301808893210366800512741849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201205928806911200341827899 301808893210366800512741849)
      ·
        refine ⟨226356669907775100384556387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301808893210366800512741849 226356669907775100384556387)
        ·
          refine ⟨339535004861662650576834581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226356669907775100384556387 339535004861662650576834581)
          ·
            refine ⟨15915703352890436745789121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339535004861662650576834581 15915703352890436745789121)
            ·
              refine ⟨11936777514667827559341841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15915703352890436745789121 11936777514667827559341841)
              ·
                refine ⟨8952583136000870669506381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11936777514667827559341841 8952583136000870669506381)
                ·
                  refine ⟨3357218676000326501064893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8952583136000870669506381 3357218676000326501064893)
                  ·
                    refine ⟨1258957003500122437899335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357218676000326501064893 1258957003500122437899335)
                    ·
                      rfl

theorem cell22_3677715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].length) (baseStart_3677715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677715 prefixEnd_3677715 := by exact prefixLift 3677715
  have htrace : WordTrace (prefixWord ++ tailWord_3677715) baseStart_3677715 baseEnd_3677715 := by
    simpa [prefixWord, tailWord_3677715, baseEnd_3677715] using wordTrace_append hprefix tailTrace_3677715
  have hstable : (prefixWord ++ tailWord_3677715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677715).length < 2 ^ (prefixWord ++ tailWord_3677715).sum := by decide
  have hdescent : baseEnd_3677715 < baseStart_3677715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677818 : List Nat := [3, 1, 1, 1, 1, 1, 1, 13]
def baseStart_3677818 : Nat := 118140960795 + 3677818 * 2 ^ 59
def prefixEnd_3677818 : Nat := 4983230072969 + 3 ^ 40 * 3677818 * 2
def baseEnd_3677818 : Nat := 139888029167229389174891

theorem tailTrace_3677818 : CollatzResearch.WordTrace tailWord_3677818 prefixEnd_3677818 139888029167229389174891 := by
  unfold tailWord_3677818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535260647475245538054527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89427361726600654768145405 33535260647475245538054527)
  ·
    refine ⟨50302890971212868307081791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33535260647475245538054527 50302890971212868307081791)
    ·
      refine ⟨75454336456819302460622687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50302890971212868307081791 75454336456819302460622687)
      ·
        refine ⟨113181504685228953690934031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75454336456819302460622687 113181504685228953690934031)
        ·
          refine ⟨169772257027843430536401047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113181504685228953690934031 169772257027843430536401047)
          ·
            refine ⟨254658385541765145804601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169772257027843430536401047 254658385541765145804601571)
            ·
              refine ⟨381987578312647718706902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254658385541765145804601571 381987578312647718706902357)
              ·
                refine ⟨139888029167229389174891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 381987578312647718706902357 139888029167229389174891)
                ·
                  rfl

theorem cell22_3677818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_3677818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677818 prefixEnd_3677818 := by exact prefixLift 3677818
  have htrace : WordTrace (prefixWord ++ tailWord_3677818) baseStart_3677818 baseEnd_3677818 := by
    simpa [prefixWord, tailWord_3677818, baseEnd_3677818] using wordTrace_append hprefix tailTrace_3677818
  have hstable : (prefixWord ++ tailWord_3677818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677818).length < 2 ^ (prefixWord ++ tailWord_3677818).sum := by decide
  have hdescent : baseEnd_3677818 < baseStart_3677818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677835 : List Nat := [1, 1, 1, 1, 4, 1, 7, 6]
def baseStart_3677835 : Nat := 118140960795 + 3677835 * 2 ^ 59
def prefixEnd_3677835 : Nat := 4983230072969 + 3 ^ 40 * 3677835 * 2
def baseEnd_3677835 : Nat := 139888675772498013877663

theorem tailTrace_3677835 : CollatzResearch.WordTrace tailWord_3677835 prefixEnd_3677835 139888675772498013877663 := by
  unfold tailWord_3677835
  simp only [CollatzResearch.WordTrace]
  refine ⟨134141662630839394055586959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89427775087226262703724639 134141662630839394055586959)
  ·
    refine ⟨201212493946259091083380439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134141662630839394055586959 201212493946259091083380439)
    ·
      refine ⟨301818740919388636625070659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201212493946259091083380439 301818740919388636625070659)
      ·
        refine ⟨452728111379082954937605989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301818740919388636625070659 452728111379082954937605989)
        ·
          refine ⟨84886520883578054050801123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452728111379082954937605989 84886520883578054050801123)
          ·
            refine ⟨127329781325367081076201685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84886520883578054050801123 127329781325367081076201685)
            ·
              refine ⟨2984291749813290962723477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127329781325367081076201685 2984291749813290962723477)
              ·
                refine ⟨139888675772498013877663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2984291749813290962723477 139888675772498013877663)
                ·
                  rfl

theorem cell22_3677835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 6].length) (baseStart_3677835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677835 prefixEnd_3677835 := by exact prefixLift 3677835
  have htrace : WordTrace (prefixWord ++ tailWord_3677835) baseStart_3677835 baseEnd_3677835 := by
    simpa [prefixWord, tailWord_3677835, baseEnd_3677835] using wordTrace_append hprefix tailTrace_3677835
  have hstable : (prefixWord ++ tailWord_3677835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677835).length < 2 ^ (prefixWord ++ tailWord_3677835).sum := by decide
  have hdescent : baseEnd_3677835 < baseStart_3677835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677880 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_3677880 : Nat := 118140960795 + 3677880 * 2 ^ 59
def prefixEnd_3677880 : Nat := 4983230072969 + 3 ^ 40 * 3677880 * 2
def baseEnd_3677880 : Nat := 419671162124039002507943

theorem tailTrace_3677880 : CollatzResearch.WordTrace tailWord_3677880 prefixEnd_3677880 419671162124039002507943 := by
  unfold tailWord_3677880
  simp only [CollatzResearch.WordTrace]
  refine ⟨67071651957838183370487547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89428869277117577827316729 67071651957838183370487547)
  ·
    refine ⟨100607477936757275055731321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67071651957838183370487547 100607477936757275055731321)
    ·
      refine ⟨75455608452567956291798491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100607477936757275055731321 75455608452567956291798491)
      ·
        refine ⟨113183412678851934437697737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75455608452567956291798491 113183412678851934437697737)
        ·
          refine ⟨84887559509138950828273303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113183412678851934437697737 84887559509138950828273303)
          ·
            refine ⟨127331339263708426242409955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84887559509138950828273303 127331339263708426242409955)
            ·
              refine ⟨190997008895562639363614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127331339263708426242409955 190997008895562639363614933)
              ·
                refine ⟨4476492395989749360084725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190997008895562639363614933 4476492395989749360084725)
                ·
                  refine ⟨419671162124039002507943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476492395989749360084725 419671162124039002507943)
                  ·
                    rfl

theorem cell22_3677880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_3677880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677880 prefixEnd_3677880 := by exact prefixLift 3677880
  have htrace : WordTrace (prefixWord ++ tailWord_3677880) baseStart_3677880 baseEnd_3677880 := by
    simpa [prefixWord, tailWord_3677880, baseEnd_3677880] using wordTrace_append hprefix tailTrace_3677880
  have hstable : (prefixWord ++ tailWord_3677880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677880).length < 2 ^ (prefixWord ++ tailWord_3677880).sum := by decide
  have hdescent : baseEnd_3677880 < baseStart_3677880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677955 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_3677955 : Nat := 118140960795 + 3677955 * 2 ^ 59
def prefixEnd_3677955 : Nat := 4983230072969 + 3 ^ 40 * 3677955 * 2
def baseEnd_3677955 : Nat := 1259039160404841811898599

theorem tailTrace_3677955 : CollatzResearch.WordTrace tailWord_3677955 prefixEnd_3677955 1259039160404841811898599 := by
  unfold tailWord_3677955
  simp only [CollatzResearch.WordTrace]
  refine ⟨134146039390404654549955319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89430692926936436366636879 134146039390404654549955319)
  ·
    refine ⟨201219059085606981824932979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134146039390404654549955319 201219059085606981824932979)
    ·
      refine ⟨301828588628410472737399469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201219059085606981824932979 301828588628410472737399469)
      ·
        refine ⟨113185720735653927276524801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301828588628410472737399469 113185720735653927276524801)
        ·
          refine ⟨84889290551740445457393601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113185720735653927276524801 84889290551740445457393601)
          ·
            refine ⟨63666967913805334093045201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84889290551740445457393601 63666967913805334093045201)
            ·
              refine ⟨47750225935354000569783901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63666967913805334093045201 47750225935354000569783901)
              ·
                refine ⟨17906334725757750213668963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47750225935354000569783901 17906334725757750213668963)
                ·
                  refine ⟨26859502088636625320503445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17906334725757750213668963 26859502088636625320503445)
                  ·
                    refine ⟨1259039160404841811898599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26859502088636625320503445 1259039160404841811898599)
                    ·
                      rfl

theorem cell22_3677955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_3677955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677955 prefixEnd_3677955 := by exact prefixLift 3677955
  have htrace : WordTrace (prefixWord ++ tailWord_3677955) baseStart_3677955 baseEnd_3677955 := by
    simpa [prefixWord, tailWord_3677955, baseEnd_3677955] using wordTrace_append hprefix tailTrace_3677955
  have hstable : (prefixWord ++ tailWord_3677955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677955).length < 2 ^ (prefixWord ++ tailWord_3677955).sum := by decide
  have hdescent : baseEnd_3677955 < baseStart_3677955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677965 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3677965 : Nat := 118140960795 + 3677965 * 2 ^ 59
def prefixEnd_3677965 : Nat := 4983230072969 + 3 ^ 40 * 3677965 * 2
def baseEnd_3677965 : Nat := 419680861203068373049523

theorem tailTrace_3677965 : CollatzResearch.WordTrace tailWord_3677965 prefixEnd_3677965 419680861203068373049523 := by
  unfold tailWord_3677965
  simp only [CollatzResearch.WordTrace]
  refine ⟨134146404120368426257819349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89430936080245617505212899 134146404120368426257819349)
  ·
    refine ⟨3144056346571134990417641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 134146404120368426257819349 3144056346571134990417641)
    ·
      refine ⟨2358042259928351242813231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3144056346571134990417641 2358042259928351242813231)
      ·
        refine ⟨3537063389892526864219847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358042259928351242813231 3537063389892526864219847)
        ·
          refine ⟨5305595084838790296329771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537063389892526864219847 5305595084838790296329771)
          ·
            refine ⟨7958392627258185444494657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305595084838790296329771 7958392627258185444494657)
            ·
              refine ⟨5968794470443639083370993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958392627258185444494657 5968794470443639083370993)
              ·
                refine ⟨4476595852832729312528245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968794470443639083370993 4476595852832729312528245)
                ·
                  refine ⟨419680861203068373049523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476595852832729312528245 419680861203068373049523)
                  ·
                    rfl

theorem cell22_3677965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3677965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3677965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3677965 prefixEnd_3677965 := by exact prefixLift 3677965
  have htrace : WordTrace (prefixWord ++ tailWord_3677965) baseStart_3677965 baseEnd_3677965 := by
    simpa [prefixWord, tailWord_3677965, baseEnd_3677965] using wordTrace_append hprefix tailTrace_3677965
  have hstable : (prefixWord ++ tailWord_3677965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677965).length < 2 ^ (prefixWord ++ tailWord_3677965).sum := by decide
  have hdescent : baseEnd_3677965 < baseStart_3677965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678006 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3678006 : Nat := 118140960795 + 3678006 * 2 ^ 59
def prefixEnd_3678006 : Nat := 4983230072969 + 3 ^ 40 * 3678006 * 2
def baseEnd_3678006 : Nat := 1259056618747094678873443

theorem tailTrace_3678006 : CollatzResearch.WordTrace tailWord_3678006 prefixEnd_3678006 1259056618747094678873443 := by
  unfold tailWord_3678006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384243719576243141253867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89431933008813260173374581 8384243719576243141253867)
  ·
    refine ⟨12576365579364364711880801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384243719576243141253867 12576365579364364711880801)
    ·
      refine ⟨9432274184523273533910601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12576365579364364711880801 9432274184523273533910601)
      ·
        refine ⟨7074205638392455150432951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9432274184523273533910601 7074205638392455150432951)
        ·
          refine ⟨10611308457588682725649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074205638392455150432951 10611308457588682725649427)
          ·
            refine ⟨15916962686383024088474141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10611308457588682725649427 15916962686383024088474141)
            ·
              refine ⟨5968861007393634033177803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15916962686383024088474141 5968861007393634033177803)
              ·
                refine ⟨8953291511090451049766705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968861007393634033177803 8953291511090451049766705)
                ·
                  refine ⟨6714968633317838287325029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8953291511090451049766705 6714968633317838287325029)
                  ·
                    refine ⟨1259056618747094678873443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6714968633317838287325029 1259056618747094678873443)
                    ·
                      rfl

theorem cell22_3678006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3678006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678006 prefixEnd_3678006 := by exact prefixLift 3678006
  have htrace : WordTrace (prefixWord ++ tailWord_3678006) baseStart_3678006 baseEnd_3678006 := by
    simpa [prefixWord, tailWord_3678006, baseEnd_3678006] using wordTrace_append hprefix tailTrace_3678006
  have hstable : (prefixWord ++ tailWord_3678006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678006).length < 2 ^ (prefixWord ++ tailWord_3678006).sum := by decide
  have hdescent : baseEnd_3678006 < baseStart_3678006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678036 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3678036 : Nat := 118140960795 + 3678036 * 2 ^ 59
def prefixEnd_3678036 : Nat := 4983230072969 + 3 ^ 40 * 3678036 * 2
def baseEnd_3678036 : Nat := 1259066888360184600623351

theorem tailTrace_3678036 : CollatzResearch.WordTrace tailWord_3678036 prefixEnd_3678036 1259066888360184600623351 := by
  unfold tailWord_3678036
  simp only [CollatzResearch.WordTrace]
  refine ⟨67074496851555602691826981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89432662468740803589102641 67074496851555602691826981)
  ·
    refine ⟨12576468159666675504717559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67074496851555602691826981 12576468159666675504717559)
    ·
      refine ⟨18864702239500013257076339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12576468159666675504717559 18864702239500013257076339)
      ·
        refine ⟨28297053359250019885614509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18864702239500013257076339 28297053359250019885614509)
        ·
          refine ⟨10611395009718757457105441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28297053359250019885614509 10611395009718757457105441)
          ·
            refine ⟨7958546257289068092829081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10611395009718757457105441 7958546257289068092829081)
            ·
              refine ⟨5968909692966801069621811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958546257289068092829081 5968909692966801069621811)
              ·
                refine ⟨8953364539450201604432717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968909692966801069621811 8953364539450201604432717)
                ·
                  refine ⟨3357511702293825601662269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8953364539450201604432717 3357511702293825601662269)
                  ·
                    refine ⟨1259066888360184600623351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357511702293825601662269 1259066888360184600623351)
                    ·
                      rfl

theorem cell22_3678036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3678036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678036 prefixEnd_3678036 := by exact prefixLift 3678036
  have htrace : WordTrace (prefixWord ++ tailWord_3678036) baseStart_3678036 baseEnd_3678036 := by
    simpa [prefixWord, tailWord_3678036, baseEnd_3678036] using wordTrace_append hprefix tailTrace_3678036
  have hstable : (prefixWord ++ tailWord_3678036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678036).length < 2 ^ (prefixWord ++ tailWord_3678036).sum := by decide
  have hdescent : baseEnd_3678036 < baseStart_3678036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678047 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3678047 : Nat := 118140960795 + 3678047 * 2 ^ 59
def prefixEnd_3678047 : Nat := 4983230072969 + 3 ^ 40 * 3678047 * 2
def baseEnd_3678047 : Nat := 1259070653884984238598317

theorem tailTrace_3678047 : CollatzResearch.WordTrace tailWord_3678047 prefixEnd_3678047 1259070653884984238598317 := by
  unfold tailWord_3678047
  simp only [CollatzResearch.WordTrace]
  refine ⟨134149394906071354262304395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89432929937380902841536263 134149394906071354262304395)
  ·
    refine ⟨201224092359107031393456593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134149394906071354262304395 201224092359107031393456593)
    ·
      refine ⟨150918069269330273545092445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201224092359107031393456593 150918069269330273545092445)
      ·
        refine ⟨56594275975998852579409667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150918069269330273545092445 56594275975998852579409667)
        ·
          refine ⟨84891413963998278869114501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56594275975998852579409667 84891413963998278869114501)
          ·
            refine ⟨15917140118249677287958969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84891413963998278869114501 15917140118249677287958969)
            ·
              refine ⟨11937855088687257965969227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917140118249677287958969 11937855088687257965969227)
              ·
                refine ⟨17906782633030886948953841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937855088687257965969227 17906782633030886948953841)
                ·
                  refine ⟨13430086974773165211715381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17906782633030886948953841 13430086974773165211715381)
                  ·
                    refine ⟨1259070653884984238598317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13430086974773165211715381 1259070653884984238598317)
                    ·
                      rfl

theorem cell22_3678047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3678047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678047 prefixEnd_3678047 := by exact prefixLift 3678047
  have htrace : WordTrace (prefixWord ++ tailWord_3678047) baseStart_3678047 baseEnd_3678047 := by
    simpa [prefixWord, tailWord_3678047, baseEnd_3678047] using wordTrace_append hprefix tailTrace_3678047
  have hstable : (prefixWord ++ tailWord_3678047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678047).length < 2 ^ (prefixWord ++ tailWord_3678047).sum := by decide
  have hdescent : baseEnd_3678047 < baseStart_3678047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678049 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 5]
def baseStart_3678049 : Nat := 118140960795 + 3678049 * 2 ^ 59
def prefixEnd_3678049 : Nat := 4983230072969 + 3 ^ 40 * 3678049 * 2
def baseEnd_3678049 : Nat := 419690446175285633349437

theorem tailTrace_3678049 : CollatzResearch.WordTrace tailWord_3678049 prefixEnd_3678049 419690446175285633349437 := by
  unfold tailWord_3678049
  simp only [CollatzResearch.WordTrace]
  refine ⟨134149467852064108603877201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89432978568042739069251467 134149467852064108603877201)
  ·
    refine ⟨100612100889048081452907901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134149467852064108603877201 100612100889048081452907901)
    ·
      refine ⟨37729537833393030544840463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100612100889048081452907901 37729537833393030544840463)
      ·
        refine ⟨56594306750089545817260695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37729537833393030544840463 56594306750089545817260695)
        ·
          refine ⟨84891460125134318725891043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56594306750089545817260695 84891460125134318725891043)
          ·
            refine ⟨127337190187701478088836565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84891460125134318725891043 127337190187701478088836565)
            ·
              refine ⟨2984465395024253392707107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127337190187701478088836565 2984465395024253392707107)
              ·
                refine ⟨4476698092536380089060661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984465395024253392707107 4476698092536380089060661)
                ·
                  refine ⟨419690446175285633349437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476698092536380089060661 419690446175285633349437)
                  ·
                    rfl

theorem cell22_3678049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_3678049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678049 prefixEnd_3678049 := by exact prefixLift 3678049
  have htrace : WordTrace (prefixWord ++ tailWord_3678049) baseStart_3678049 baseEnd_3678049 := by
    simpa [prefixWord, tailWord_3678049, baseEnd_3678049] using wordTrace_append hprefix tailTrace_3678049
  have hstable : (prefixWord ++ tailWord_3678049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678049).length < 2 ^ (prefixWord ++ tailWord_3678049).sum := by decide
  have hdescent : baseEnd_3678049 < baseStart_3678049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678113 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3678113 : Nat := 118140960795 + 3678113 * 2 ^ 59
def prefixEnd_3678113 : Nat := 4983230072969 + 3 ^ 40 * 3678113 * 2
def baseEnd_3678113 : Nat := 1259093247033782066448115

theorem tailTrace_3678113 : CollatzResearch.WordTrace tailWord_3678113 prefixEnd_3678113 1259093247033782066448115 := by
  unfold tailWord_3678113
  simp only [CollatzResearch.WordTrace]
  refine ⟨134151802123832247534206993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89434534749221498356137995 134151802123832247534206993)
  ·
    refine ⟨100613851592874185650655245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134151802123832247534206993 100613851592874185650655245)
    ·
      refine ⟨37730194347327819618995717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100613851592874185650655245 37730194347327819618995717)
      ·
        refine ⟨7074411440123966178561697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37730194347327819618995717 7074411440123966178561697)
        ·
          refine ⟨5305808580092974633921273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074411440123966178561697 5305808580092974633921273)
          ·
            refine ⟨3979356435069730975440955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5305808580092974633921273 3979356435069730975440955)
            ·
              refine ⟨5969034652604596463161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979356435069730975440955 5969034652604596463161433)
              ·
                refine ⟨4476775989453447347371075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969034652604596463161433 4476775989453447347371075)
                ·
                  refine ⟨6715163984180171021056613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476775989453447347371075 6715163984180171021056613)
                  ·
                    refine ⟨1259093247033782066448115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715163984180171021056613 1259093247033782066448115)
                    ·
                      rfl

theorem cell22_3678113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3678113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678113 prefixEnd_3678113 := by exact prefixLift 3678113
  have htrace : WordTrace (prefixWord ++ tailWord_3678113) baseStart_3678113 baseEnd_3678113 := by
    simpa [prefixWord, tailWord_3678113, baseEnd_3678113] using wordTrace_append hprefix tailTrace_3678113
  have hstable : (prefixWord ++ tailWord_3678113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678113).length < 2 ^ (prefixWord ++ tailWord_3678113).sum := by decide
  have hdescent : baseEnd_3678113 < baseStart_3678113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678201 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 5]
def baseStart_3678201 : Nat := 118140960795 + 3678201 * 2 ^ 59
def prefixEnd_3678201 : Nat := 4983230072969 + 3 ^ 40 * 3678201 * 2
def baseEnd_3678201 : Nat := 419707790410726390082615

theorem tailTrace_3678201 : CollatzResearch.WordTrace tailWord_3678201 prefixEnd_3678201 419707790410726390082615 := by
  unfold tailWord_3678201
  simp only [CollatzResearch.WordTrace]
  refine ⟨134155011747513438563410457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89436674498342292375606971 134155011747513438563410457)
  ·
    refine ⟨100616258810635078922557843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134155011747513438563410457 100616258810635078922557843)
    ·
      refine ⟨150924388215952618383836765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100616258810635078922557843 150924388215952618383836765)
      ·
        refine ⟨56596645580982231893938787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150924388215952618383836765 56596645580982231893938787)
        ·
          refine ⟨84894968371473347840908181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56596645580982231893938787 84894968371473347840908181)
          ·
            refine ⟨3979451642412813180042571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84894968371473347840908181 3979451642412813180042571)
            ·
              refine ⟨5969177463619219770063857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979451642412813180042571 5969177463619219770063857)
              ·
                refine ⟨4476883097714414827547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969177463619219770063857 4476883097714414827547893)
                ·
                  refine ⟨419707790410726390082615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476883097714414827547893 419707790410726390082615)
                  ·
                    rfl

theorem cell22_3678201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_3678201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678201 prefixEnd_3678201 := by exact prefixLift 3678201
  have htrace : WordTrace (prefixWord ++ tailWord_3678201) baseStart_3678201 baseEnd_3678201 := by
    simpa [prefixWord, tailWord_3678201, baseEnd_3678201] using wordTrace_append hprefix tailTrace_3678201
  have hstable : (prefixWord ++ tailWord_3678201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678201).length < 2 ^ (prefixWord ++ tailWord_3678201).sum := by decide
  have hdescent : baseEnd_3678201 < baseStart_3678201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678218 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_3678218 : Nat := 118140960795 + 3678218 * 2 ^ 59
def prefixEnd_3678218 : Nat := 4983230072969 + 3 ^ 40 * 3678218 * 2
def baseEnd_3678218 : Nat := 419709730226532264190931

theorem tailTrace_3678218 : CollatzResearch.WordTrace tailWord_3678218 prefixEnd_3678218 419709730226532264190931 := by
  unfold tailWord_3678218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33538907947112962616694827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89437087858967900311186205 33538907947112962616694827)
  ·
    refine ⟨50308361920669443925042241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33538907947112962616694827 50308361920669443925042241)
    ·
      refine ⟨37731271440502082943781681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50308361920669443925042241 37731271440502082943781681)
      ·
        refine ⟨28298453580376562207836261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37731271440502082943781681 28298453580376562207836261)
        ·
          refine ⟨5305960046320605413969299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28298453580376562207836261 5305960046320605413969299)
          ·
            refine ⟨7958940069480908120953949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305960046320605413969299 7958940069480908120953949)
            ·
              refine ⟨2984602526055340545357731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7958940069480908120953949 2984602526055340545357731)
              ·
                refine ⟨4476903789083010818036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984602526055340545357731 4476903789083010818036597)
                ·
                  refine ⟨419709730226532264190931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4476903789083010818036597 419709730226532264190931)
                  ·
                    rfl

theorem cell22_3678218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_3678218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678218 prefixEnd_3678218 := by exact prefixLift 3678218
  have htrace : WordTrace (prefixWord ++ tailWord_3678218) baseStart_3678218 baseEnd_3678218 := by
    simpa [prefixWord, tailWord_3678218, baseEnd_3678218] using wordTrace_append hprefix tailTrace_3678218
  have hstable : (prefixWord ++ tailWord_3678218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678218).length < 2 ^ (prefixWord ++ tailWord_3678218).sum := by decide
  have hdescent : baseEnd_3678218 < baseStart_3678218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678259 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_3678259 : Nat := 118140960795 + 3678259 * 2 ^ 59
def prefixEnd_3678259 : Nat := 4983230072969 + 3 ^ 40 * 3678259 * 2
def baseEnd_3678259 : Nat := 1259143225817486352297667

theorem tailTrace_3678259 : CollatzResearch.WordTrace tailWord_3678259 prefixEnd_3678259 1259143225817486352297667 := by
  unfold tailWord_3678259
  simp only [CollatzResearch.WordTrace]
  refine ⟨134157127181303314469021831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89438084787535542979347887 134157127181303314469021831)
  ·
    refine ⟨201235690771954971703532747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134157127181303314469021831 201235690771954971703532747)
    ·
      refine ⟨301853536157932457555299121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201235690771954971703532747 301853536157932457555299121)
      ·
        refine ⟨226390152118449343166474341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301853536157932457555299121 226390152118449343166474341)
        ·
          refine ⟨42448153522209251843713939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226390152118449343166474341 42448153522209251843713939)
          ·
            refine ⟨63672230283313877765570909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42448153522209251843713939 63672230283313877765570909)
            ·
              refine ⟨23877086356242704162089091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63672230283313877765570909 23877086356242704162089091)
              ·
                refine ⟨35815629534364056243133637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23877086356242704162089091 35815629534364056243133637)
                ·
                  refine ⟨6715430537693260545587557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35815629534364056243133637 6715430537693260545587557)
                  ·
                    refine ⟨1259143225817486352297667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715430537693260545587557 1259143225817486352297667)
                    ·
                      rfl

theorem cell22_3678259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_3678259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678259 prefixEnd_3678259 := by exact prefixLift 3678259
  have htrace : WordTrace (prefixWord ++ tailWord_3678259) baseStart_3678259 baseEnd_3678259 := by
    simpa [prefixWord, tailWord_3678259, baseEnd_3678259] using wordTrace_append hprefix tailTrace_3678259
  have hstable : (prefixWord ++ tailWord_3678259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678259).length < 2 ^ (prefixWord ++ tailWord_3678259).sum := by decide
  have hdescent : baseEnd_3678259 < baseStart_3678259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678261 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3678261 : Nat := 118140960795 + 3678261 * 2 ^ 59
def prefixEnd_3678261 : Nat := 4983230072969 + 3 ^ 40 * 3678261 * 2
def baseEnd_3678261 : Nat := 1259143910458359013747661

theorem tailTrace_3678261 : CollatzResearch.WordTrace tailWord_3678261 prefixEnd_3678261 1259143910458359013747661 := by
  unfold tailWord_3678261
  simp only [CollatzResearch.WordTrace]
  refine ⟨134157200127296068810594637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89438133418197379207063091 134157200127296068810594637)
  ·
    refine ⟨50308950047736025803972989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134157200127296068810594637 50308950047736025803972989)
    ·
      refine ⟨18865856267901009676489871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50308950047736025803972989 18865856267901009676489871)
      ·
        refine ⟨28298784401851514514734807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865856267901009676489871 28298784401851514514734807)
        ·
          refine ⟨42448176602777271772102211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298784401851514514734807 42448176602777271772102211)
          ·
            refine ⟨63672264904165907658153317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42448176602777271772102211 63672264904165907658153317)
            ·
              refine ⟨11938549669531107685903747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63672264904165907658153317 11938549669531107685903747)
              ·
                refine ⟨17907824504296661528855621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938549669531107685903747 17907824504296661528855621)
                ·
                  refine ⟨3357717094555624036660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17907824504296661528855621 3357717094555624036660429)
                  ·
                    refine ⟨1259143910458359013747661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357717094555624036660429 1259143910458359013747661)
                    ·
                      rfl

theorem cell22_3678261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3678261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678261 prefixEnd_3678261 := by exact prefixLift 3678261
  have htrace : WordTrace (prefixWord ++ tailWord_3678261) baseStart_3678261 baseEnd_3678261 := by
    simpa [prefixWord, tailWord_3678261, baseEnd_3678261] using wordTrace_append hprefix tailTrace_3678261
  have hstable : (prefixWord ++ tailWord_3678261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678261).length < 2 ^ (prefixWord ++ tailWord_3678261).sum := by decide
  have hdescent : baseEnd_3678261 < baseStart_3678261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678278 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3678278 : Nat := 118140960795 + 3678278 * 2 ^ 59
def prefixEnd_3678278 : Nat := 4983230072969 + 3 ^ 40 * 3678278 * 2
def baseEnd_3678278 : Nat := 1259149729905776636072609

theorem tailTrace_3678278 : CollatzResearch.WordTrace tailWord_3678278 prefixEnd_3678278 1259149729905776636072609 := by
  unfold tailWord_3678278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192431880257327522311359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89438546778822987142642325 4192431880257327522311359)
  ·
    refine ⟨6288647820385991283467039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192431880257327522311359 6288647820385991283467039)
    ·
      refine ⟨9432971730578986925200559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288647820385991283467039 9432971730578986925200559)
      ·
        refine ⟨14149457595868480387800839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432971730578986925200559 14149457595868480387800839)
        ·
          refine ⟨21224186393802720581701259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14149457595868480387800839 21224186393802720581701259)
          ·
            refine ⟨31836279590704080872551889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21224186393802720581701259 31836279590704080872551889)
            ·
              refine ⟨23877209693028060654413917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31836279590704080872551889 23877209693028060654413917)
              ·
                refine ⟨8953953634885522745405219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23877209693028060654413917 8953953634885522745405219)
                ·
                  refine ⟨13430930452328284118107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953953634885522745405219 13430930452328284118107829)
                  ·
                    refine ⟨1259149729905776636072609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13430930452328284118107829 1259149729905776636072609)
                    ·
                      rfl

theorem cell22_3678278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3678278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678278 prefixEnd_3678278 := by exact prefixLift 3678278
  have htrace : WordTrace (prefixWord ++ tailWord_3678278) baseStart_3678278 baseEnd_3678278 := by
    simpa [prefixWord, tailWord_3678278, baseEnd_3678278] using wordTrace_append hprefix tailTrace_3678278
  have hstable : (prefixWord ++ tailWord_3678278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678278).length < 2 ^ (prefixWord ++ tailWord_3678278).sum := by decide
  have hdescent : baseEnd_3678278 < baseStart_3678278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678370 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3678370 : Nat := 118140960795 + 3678370 * 2 ^ 59
def prefixEnd_3678370 : Nat := 4983230072969 + 3 ^ 40 * 3678370 * 2
def baseEnd_3678370 : Nat := 419727074461973020924109

theorem tailTrace_3678370 : CollatzResearch.WordTrace tailWord_3678370 prefixEnd_3678370 419727074461973020924109 := by
  unfold tailWord_3678370
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540293920975295106578141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89440783789267453617541709 33540293920975295106578141)
  ·
    refine ⟨12577610220365735664966803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33540293920975295106578141 12577610220365735664966803)
    ·
      refine ⟨18866415330548603497450205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577610220365735664966803 18866415330548603497450205)
      ·
        refine ⟨7074905748955726311543827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18866415330548603497450205 7074905748955726311543827)
        ·
          refine ⟨10612358623433589467315741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074905748955726311543827 10612358623433589467315741)
          ·
            refine ⟨3979634483787596050243403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10612358623433589467315741 3979634483787596050243403)
            ·
              refine ⟨5969451725681394075365105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979634483787596050243403 5969451725681394075365105)
              ·
                refine ⟨4477088794261045556523829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969451725681394075365105 4477088794261045556523829)
                ·
                  refine ⟨419727074461973020924109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477088794261045556523829 419727074461973020924109)
                  ·
                    rfl

theorem cell22_3678370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3678370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678370 prefixEnd_3678370 := by exact prefixLift 3678370
  have htrace : WordTrace (prefixWord ++ tailWord_3678370) baseStart_3678370 baseEnd_3678370 := by
    simpa [prefixWord, tailWord_3678370, baseEnd_3678370] using wordTrace_append hprefix tailTrace_3678370
  have hstable : (prefixWord ++ tailWord_3678370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678370).length < 2 ^ (prefixWord ++ tailWord_3678370).sum := by decide
  have hdescent : baseEnd_3678370 < baseStart_3678370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678411 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_3678411 : Nat := 118140960795 + 3678411 * 2 ^ 59
def prefixEnd_3678411 : Nat := 4983230072969 + 3 ^ 40 * 3678411 * 2
def baseEnd_3678411 : Nat := 1259195258523808622497201

theorem tailTrace_3678411 : CollatzResearch.WordTrace tailWord_3678411 prefixEnd_3678411 1259195258523808622497201 := by
  unfold tailWord_3678411
  simp only [CollatzResearch.WordTrace]
  refine ⟨134162671076752644428555087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89441780717835096285703391 134162671076752644428555087)
  ·
    refine ⟨201244006615128966642832631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134162671076752644428555087 201244006615128966642832631)
    ·
      refine ⟨301866009922693449964248947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201244006615128966642832631 301866009922693449964248947)
      ·
        refine ⟨452799014884040174946373421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301866009922693449964248947 452799014884040174946373421)
        ·
          refine ⟨169799630581515065604890033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452799014884040174946373421 169799630581515065604890033)
          ·
            refine ⟨127349722936136299203667525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169799630581515065604890033 127349722936136299203667525)
            ·
              refine ⟨23878073050525556100687661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127349722936136299203667525 23878073050525556100687661)
              ·
                refine ⟨8954277393947083537757873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23878073050525556100687661 8954277393947083537757873)
                ·
                  refine ⟨6715708045460312653318405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8954277393947083537757873 6715708045460312653318405)
                  ·
                    refine ⟨1259195258523808622497201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715708045460312653318405 1259195258523808622497201)
                    ·
                      rfl

theorem cell22_3678411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_3678411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678411 prefixEnd_3678411 := by exact prefixLift 3678411
  have htrace : WordTrace (prefixWord ++ tailWord_3678411) baseStart_3678411 baseEnd_3678411 := by
    simpa [prefixWord, tailWord_3678411, baseEnd_3678411] using wordTrace_append hprefix tailTrace_3678411
  have hstable : (prefixWord ++ tailWord_3678411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678411).length < 2 ^ (prefixWord ++ tailWord_3678411).sum := by decide
  have hdescent : baseEnd_3678411 < baseStart_3678411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678447 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 2, 3]
def baseStart_3678447 : Nat := 118140960795 + 3678447 * 2 ^ 59
def prefixEnd_3678447 : Nat := 4983230072969 + 3 ^ 40 * 3678447 * 2
def baseEnd_3678447 : Nat := 1259207582059516528597091

theorem tailTrace_3678447 : CollatzResearch.WordTrace tailWord_3678447 prefixEnd_3678447 1259207582059516528597091 := by
  unfold tailWord_3678447
  simp only [CollatzResearch.WordTrace]
  refine ⟨134163984104622222576865595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89442656069748148384577063 134163984104622222576865595)
  ·
    refine ⟨201245976156933333865298393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134163984104622222576865595 201245976156933333865298393)
    ·
      refine ⟨150934482117700000398973795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201245976156933333865298393 150934482117700000398973795)
      ·
        refine ⟨226401723176550000598460693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150934482117700000398973795 226401723176550000598460693)
        ·
          refine ⟨10612580773900781278052845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226401723176550000598460693 10612580773900781278052845)
          ·
            refine ⟨3979717790212792979269817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10612580773900781278052845 3979717790212792979269817)
            ·
              refine ⟨2984788342659594734452363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3979717790212792979269817 2984788342659594734452363)
              ·
                refine ⟨4477182513989392101678545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984788342659594734452363 4477182513989392101678545)
                ·
                  refine ⟨3357886885492044076258909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477182513989392101678545 3357886885492044076258909)
                  ·
                    refine ⟨1259207582059516528597091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357886885492044076258909 1259207582059516528597091)
                    ·
                      rfl

theorem cell22_3678447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_3678447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678447 prefixEnd_3678447 := by exact prefixLift 3678447
  have htrace : WordTrace (prefixWord ++ tailWord_3678447) baseStart_3678447 baseEnd_3678447 := by
    simpa [prefixWord, tailWord_3678447, baseEnd_3678447] using wordTrace_append hprefix tailTrace_3678447
  have hstable : (prefixWord ++ tailWord_3678447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678447).length < 2 ^ (prefixWord ++ tailWord_3678447).sum := by decide
  have hdescent : baseEnd_3678447 < baseStart_3678447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678475 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 1, 3]
def baseStart_3678475 : Nat := 118140960795 + 3678475 * 2 ^ 59
def prefixEnd_3678475 : Nat := 4983230072969 + 3 ^ 40 * 3678475 * 2
def baseEnd_3678475 : Nat := 1259217167031733788897005

theorem tailTrace_3678475 : CollatzResearch.WordTrace tailWord_3678475 prefixEnd_3678475 1259217167031733788897005 := by
  unfold tailWord_3678475
  simp only [CollatzResearch.WordTrace]
  refine ⟨134165005348520783358884879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89443336899013855572589919 134165005348520783358884879)
  ·
    refine ⟨201247508022781175038327319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134165005348520783358884879 201247508022781175038327319)
    ·
      refine ⟨301871262034171762557490979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201247508022781175038327319 301871262034171762557490979)
      ·
        refine ⟨452806893051257643836236469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301871262034171762557490979 452806893051257643836236469)
        ·
          refine ⟨42450646223555404109647169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452806893051257643836236469 42450646223555404109647169)
          ·
            refine ⟨31837984667666553082235377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42450646223555404109647169 31837984667666553082235377)
            ·
              refine ⟨23878488500749914811676533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31837984667666553082235377 23878488500749914811676533)
              ·
                refine ⟨2238608296945304513594675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23878488500749914811676533 2238608296945304513594675)
                ·
                  refine ⟨3357912445417956770392013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238608296945304513594675 3357912445417956770392013)
                  ·
                    refine ⟨1259217167031733788897005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357912445417956770392013 1259217167031733788897005)
                    ·
                      rfl

theorem cell22_3678475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 3].length) (baseStart_3678475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678475 prefixEnd_3678475 := by exact prefixLift 3678475
  have htrace : WordTrace (prefixWord ++ tailWord_3678475) baseStart_3678475 baseEnd_3678475 := by
    simpa [prefixWord, tailWord_3678475, baseEnd_3678475] using wordTrace_append hprefix tailTrace_3678475
  have hstable : (prefixWord ++ tailWord_3678475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678475).length < 2 ^ (prefixWord ++ tailWord_3678475).sum := by decide
  have hdescent : baseEnd_3678475 < baseStart_3678475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678488 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_3678488 : Nat := 118140960795 + 3678488 * 2 ^ 59
def prefixEnd_3678488 : Nat := 4983230072969 + 3 ^ 40 * 3678488 * 2
def baseEnd_3678488 : Nat := 419740539065802029440655

theorem tailTrace_3678488 : CollatzResearch.WordTrace tailWord_3678488 prefixEnd_3678488 419740539065802029440655 := by
  unfold tailWord_3678488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67082739748736843289554059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89443652998315791052738745 67082739748736843289554059)
  ·
    refine ⟨100624109623105264934331089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67082739748736843289554059 100624109623105264934331089)
    ·
      refine ⟨75468082217328948700748317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100624109623105264934331089 75468082217328948700748317)
      ·
        refine ⟨28300530831498355762780619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75468082217328948700748317 28300530831498355762780619)
        ·
          refine ⟨42450796247247533644170929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28300530831498355762780619 42450796247247533644170929)
          ·
            refine ⟨31838097185435650233128197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42450796247247533644170929 31838097185435650233128197)
            ·
              refine ⟨5969643222269184418711537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31838097185435650233128197 5969643222269184418711537)
              ·
                refine ⟨4477232416701888314033653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969643222269184418711537 4477232416701888314033653)
                ·
                  refine ⟨419740539065802029440655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477232416701888314033653 419740539065802029440655)
                  ·
                    rfl

theorem cell22_3678488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_3678488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678488 prefixEnd_3678488 := by exact prefixLift 3678488
  have htrace : WordTrace (prefixWord ++ tailWord_3678488) baseStart_3678488 baseEnd_3678488 := by
    simpa [prefixWord, tailWord_3678488, baseEnd_3678488] using wordTrace_append hprefix tailTrace_3678488
  have hstable : (prefixWord ++ tailWord_3678488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678488).length < 2 ^ (prefixWord ++ tailWord_3678488).sum := by decide
  have hdescent : baseEnd_3678488 < baseStart_3678488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678565 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3678565 : Nat := 118140960795 + 3678565 * 2 ^ 59
def prefixEnd_3678565 : Nat := 4983230072969 + 3 ^ 40 * 3678565 * 2
def baseEnd_3678565 : Nat := 1259247975871003554146729

theorem tailTrace_3678565 : CollatzResearch.WordTrace tailWord_3678565 prefixEnd_3678565 1259247975871003554146729 := by
  unfold tailWord_3678565
  simp only [CollatzResearch.WordTrace]
  refine ⟨134168287918194728729661149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89445525278796485819774099 134168287918194728729661149)
  ·
    refine ⟨50313107969323023273622931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134168287918194728729661149 50313107969323023273622931)
    ·
      refine ⟨75469661953984534910434397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50313107969323023273622931 75469661953984534910434397)
      ·
        refine ⟨28301123232744200591412899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75469661953984534910434397 28301123232744200591412899)
        ·
          refine ⟨42451684849116300887119349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28301123232744200591412899 42451684849116300887119349)
          ·
            refine ⟨3979845454604653208167439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42451684849116300887119349 3979845454604653208167439)
            ·
              refine ⟨5969768181906979812251159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979845454604653208167439 5969768181906979812251159)
              ·
                refine ⟨8954652272860469718376739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969768181906979812251159 8954652272860469718376739)
                ·
                  refine ⟨13431978409290704577565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8954652272860469718376739 13431978409290704577565109)
                  ·
                    refine ⟨1259247975871003554146729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13431978409290704577565109 1259247975871003554146729)
                    ·
                      rfl

theorem cell22_3678565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3678565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678565 prefixEnd_3678565 := by exact prefixLift 3678565
  have htrace : WordTrace (prefixWord ++ tailWord_3678565) baseStart_3678565 baseEnd_3678565 := by
    simpa [prefixWord, tailWord_3678565, baseEnd_3678565] using wordTrace_append hprefix tailTrace_3678565
  have hstable : (prefixWord ++ tailWord_3678565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678565).length < 2 ^ (prefixWord ++ tailWord_3678565).sum := by decide
  have hdescent : baseEnd_3678565 < baseStart_3678565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678578 : List Nat := [3, 2, 1, 2, 1, 4, 1, 8]
def baseStart_3678578 : Nat := 118140960795 + 3678578 * 2 ^ 59
def prefixEnd_3678578 : Nat := 4983230072969 + 3 ^ 40 * 3678578 * 2
def baseEnd_3678578 : Nat := 139916936226297317063521

theorem tailTrace_3678578 : CollatzResearch.WordTrace tailWord_3678578 prefixEnd_3678578 139916936226297317063521 := by
  unfold tailWord_3678578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542190516786907987471097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89445841378098421299922925 33542190516786907987471097)
  ·
    refine ⟨25156642887590180990603323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33542190516786907987471097 25156642887590180990603323)
    ·
      refine ⟨37734964331385271485904985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25156642887590180990603323 37734964331385271485904985)
      ·
        refine ⟨28301223248538953614428739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37734964331385271485904985 28301223248538953614428739)
        ·
          refine ⟨42451834872808430421643109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28301223248538953614428739 42451834872808430421643109)
          ·
            refine ⟨7959719038651580704058083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42451834872808430421643109 7959719038651580704058083)
            ·
              refine ⟨11939578557977371056087125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959719038651580704058083 11939578557977371056087125)
              ·
                refine ⟨139916936226297317063521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11939578557977371056087125 139916936226297317063521)
                ·
                  rfl

theorem cell22_3678578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_3678578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678578 prefixEnd_3678578 := by exact prefixLift 3678578
  have htrace : WordTrace (prefixWord ++ tailWord_3678578) baseStart_3678578 baseEnd_3678578 := by
    simpa [prefixWord, tailWord_3678578, baseEnd_3678578] using wordTrace_append hprefix tailTrace_3678578
  have hstable : (prefixWord ++ tailWord_3678578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678578).length < 2 ^ (prefixWord ++ tailWord_3678578).sum := by decide
  have hdescent : baseEnd_3678578 < baseStart_3678578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678595 : List Nat := [1, 1, 1, 3, 7, 1, 8]
def baseStart_3678595 : Nat := 118140960795 + 3678595 * 2 ^ 59
def prefixEnd_3678595 : Nat := 4983230072969 + 3 ^ 40 * 3678595 * 2
def baseEnd_3678595 : Nat := 46639194277188647255431

theorem tailTrace_3678595 : CollatzResearch.WordTrace tailWord_3678595 prefixEnd_3678595 46639194277188647255431 := by
  unfold tailWord_3678595
  simp only [CollatzResearch.WordTrace]
  refine ⟨134169382108086043853253239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89446254738724029235502159 134169382108086043853253239)
  ·
    refine ⟨201254073162129065779879859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134169382108086043853253239 201254073162129065779879859)
    ·
      refine ⟨301881109743193598669819789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201254073162129065779879859 301881109743193598669819789)
      ·
        refine ⟨113205416153697599501182421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301881109743193598669819789 113205416153697599501182421)
        ·
          refine ⟨2653251941102287488308963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113205416153697599501182421 2653251941102287488308963)
          ·
            refine ⟨3979877911653431232463445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653251941102287488308963 3979877911653431232463445)
            ·
              refine ⟨46639194277188647255431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3979877911653431232463445 46639194277188647255431)
              ·
                rfl

theorem cell22_3678595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 8].length) (baseStart_3678595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678595 prefixEnd_3678595 := by exact prefixLift 3678595
  have htrace : WordTrace (prefixWord ++ tailWord_3678595) baseStart_3678595 baseEnd_3678595 := by
    simpa [prefixWord, tailWord_3678595, baseEnd_3678595] using wordTrace_append hprefix tailTrace_3678595
  have hstable : (prefixWord ++ tailWord_3678595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678595).length < 2 ^ (prefixWord ++ tailWord_3678595).sum := by decide
  have hdescent : baseEnd_3678595 < baseStart_3678595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678685 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3678685 : Nat := 118140960795 + 3678685 * 2 ^ 59
def prefixEnd_3678685 : Nat := 4983230072969 + 3 ^ 40 * 3678685 * 2
def baseEnd_3678685 : Nat := 419763018107787747048787

theorem tailTrace_3678685 : CollatzResearch.WordTrace tailWord_3678685 prefixEnd_3678685 419763018107787747048787 := by
  unfold tailWord_3678685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134172664677759989224029509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89448443118506659482686339 134172664677759989224029509)
  ·
    refine ⟨25157374627079997979505533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134172664677759989224029509 25157374627079997979505533)
    ·
      refine ⟨9434015485154999242314575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25157374627079997979505533 9434015485154999242314575)
      ·
        refine ⟨14151023227732498863471863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434015485154999242314575 14151023227732498863471863)
        ·
          refine ⟨21226534841598748295207795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151023227732498863471863 21226534841598748295207795)
          ·
            refine ⟨31839802262398122442811693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21226534841598748295207795 31839802262398122442811693)
            ·
              refine ⟨11939925848399295916054385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31839802262398122442811693 11939925848399295916054385)
              ·
                refine ⟨8954944386299471937040789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11939925848399295916054385 8954944386299471937040789)
                ·
                  refine ⟨419763018107787747048787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8954944386299471937040789 419763018107787747048787)
                  ·
                    rfl

theorem cell22_3678685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3678685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678685 prefixEnd_3678685 := by exact prefixLift 3678685
  have htrace : WordTrace (prefixWord ++ tailWord_3678685) baseStart_3678685 baseEnd_3678685 := by
    simpa [prefixWord, tailWord_3678685, baseEnd_3678685] using wordTrace_append hprefix tailTrace_3678685
  have hstable : (prefixWord ++ tailWord_3678685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678685).length < 2 ^ (prefixWord ++ tailWord_3678685).sum := by decide
  have hdescent : baseEnd_3678685 < baseStart_3678685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678700 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_3678700 : Nat := 118140960795 + 3678700 * 2 ^ 59
def prefixEnd_3678700 : Nat := 4983230072969 + 3 ^ 40 * 3678700 * 2
def baseEnd_3678700 : Nat := 1259294189129908202021315

theorem tailTrace_3678700 : CollatzResearch.WordTrace tailWord_3678700 prefixEnd_3678700 1259294189129908202021315 := by
  unfold tailWord_3678700
  simp only [CollatzResearch.WordTrace]
  refine ⟨67086605886352823392912777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89448807848470431190550369 67086605886352823392912777)
  ·
    refine ⟨50314954414764617544684583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67086605886352823392912777 50314954414764617544684583)
    ·
      refine ⟨75472431622146926317026875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50314954414764617544684583 75472431622146926317026875)
      ·
        refine ⟨113208647433220389475540313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75472431622146926317026875 113208647433220389475540313)
        ·
          refine ⟨84906485574915292106655235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113208647433220389475540313 84906485574915292106655235)
          ·
            refine ⟨127359728362372938159982853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84906485574915292106655235 127359728362372938159982853)
            ·
              refine ⟨23879949067944925904996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127359728362372938159982853 23879949067944925904996785)
              ·
                refine ⟨17909961800958694428747589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23879949067944925904996785 17909961800958694428747589)
                ·
                  refine ⟨3358117837679755205390173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17909961800958694428747589 3358117837679755205390173)
                  ·
                    refine ⟨1259294189129908202021315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358117837679755205390173 1259294189129908202021315)
                    ·
                      rfl

theorem cell22_3678700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_3678700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678700 prefixEnd_3678700 := by exact prefixLift 3678700
  have htrace : WordTrace (prefixWord ++ tailWord_3678700) baseStart_3678700 baseEnd_3678700 := by
    simpa [prefixWord, tailWord_3678700, baseEnd_3678700] using wordTrace_append hprefix tailTrace_3678700
  have hstable : (prefixWord ++ tailWord_3678700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678700).length < 2 ^ (prefixWord ++ tailWord_3678700).sum := by decide
  have hdescent : baseEnd_3678700 < baseStart_3678700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678702 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_3678702 : Nat := 118140960795 + 3678702 * 2 ^ 59
def prefixEnd_3678702 : Nat := 4983230072969 + 3 ^ 40 * 3678702 * 2
def baseEnd_3678702 : Nat := 419764957923593621157103

theorem tailTrace_3678702 : CollatzResearch.WordTrace tailWord_3678702 prefixEnd_3678702 419764957923593621157103 := by
  unfold tailWord_3678702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771660589837300140924795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89448856479132267418265573 16771660589837300140924795)
  ·
    refine ⟨25157490884755950211387193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16771660589837300140924795 25157490884755950211387193)
    ·
      refine ⟨18868118163566962658540395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25157490884755950211387193 18868118163566962658540395)
      ·
        refine ⟨28302177245350443987810593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18868118163566962658540395 28302177245350443987810593)
        ·
          refine ⟨21226632934012832990857945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28302177245350443987810593 21226632934012832990857945)
          ·
            refine ⟨15919974700509624743143459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21226632934012832990857945 15919974700509624743143459)
            ·
              refine ⟨23879962050764437114715189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919974700509624743143459 23879962050764437114715189)
              ·
                refine ⟨2238746442259165979504549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23879962050764437114715189 2238746442259165979504549)
                ·
                  refine ⟨419764957923593621157103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2238746442259165979504549 419764957923593621157103)
                  ·
                    rfl

theorem cell22_3678702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_3678702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678702 prefixEnd_3678702 := by exact prefixLift 3678702
  have htrace : WordTrace (prefixWord ++ tailWord_3678702) baseStart_3678702 baseEnd_3678702 := by
    simpa [prefixWord, tailWord_3678702, baseEnd_3678702] using wordTrace_append hprefix tailTrace_3678702
  have hstable : (prefixWord ++ tailWord_3678702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678702).length < 2 ^ (prefixWord ++ tailWord_3678702).sum := by decide
  have hdescent : baseEnd_3678702 < baseStart_3678702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678775 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 5]
def baseStart_3678775 : Nat := 118140960795 + 3678775 * 2 ^ 59
def prefixEnd_3678775 : Nat := 4983230072969 + 3 ^ 40 * 3678775 * 2
def baseEnd_3678775 : Nat := 419773287720877668798695

theorem tailTrace_3678775 : CollatzResearch.WordTrace tailWord_3678775 prefixEnd_3678775 419773287720877668798695 := by
  unfold tailWord_3678775
  simp only [CollatzResearch.WordTrace]
  refine ⟨134175947247433934594805779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89450631498289289729870519 134175947247433934594805779)
  ·
    refine ⟨201263920871150901892208669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134175947247433934594805779 201263920871150901892208669)
    ·
      refine ⟨75473970326681588209578251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201263920871150901892208669 75473970326681588209578251)
      ·
        refine ⟨113210955490022382314367377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75473970326681588209578251 113210955490022382314367377)
        ·
          refine ⟨84908216617516786735775533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113210955490022382314367377 84908216617516786735775533)
          ·
            refine ⟨31840581231568795025915825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84908216617516786735775533 31840581231568795025915825)
            ·
              refine ⟨23880435923676596269436869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31840581231568795025915825 23880435923676596269436869)
              ·
                refine ⟨4477581735689361800519413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23880435923676596269436869 4477581735689361800519413)
                ·
                  refine ⟨419773287720877668798695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4477581735689361800519413 419773287720877668798695)
                  ·
                    rfl

theorem cell22_3678775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].length) (baseStart_3678775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678775 prefixEnd_3678775 := by exact prefixLift 3678775
  have htrace : WordTrace (prefixWord ++ tailWord_3678775) baseStart_3678775 baseEnd_3678775 := by
    simpa [prefixWord, tailWord_3678775, baseEnd_3678775] using wordTrace_append hprefix tailTrace_3678775
  have hstable : (prefixWord ++ tailWord_3678775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678775).length < 2 ^ (prefixWord ++ tailWord_3678775).sum := by decide
  have hdescent : baseEnd_3678775 < baseStart_3678775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678852 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3678852 : Nat := 118140960795 + 3678852 * 2 ^ 59
def prefixEnd_3678852 : Nat := 4983230072969 + 3 ^ 40 * 3678852 * 2
def baseEnd_3678852 : Nat := 1259346221836230472220849

theorem tailTrace_3678852 : CollatzResearch.WordTrace tailWord_3678852 prefixEnd_3678852 1259346221836230472220849 := by
  unfold tailWord_3678852
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089377834077488372679405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89452503778769984496905873 67089377834077488372679405)
  ·
    refine ⟨25158516687779058139754777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67089377834077488372679405 25158516687779058139754777)
    ·
      refine ⟨18868887515834293604816083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25158516687779058139754777 18868887515834293604816083)
      ·
        refine ⟨28303331273751440407224125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18868887515834293604816083 28303331273751440407224125)
        ·
          refine ⟨10613749227656790152709047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28303331273751440407224125 10613749227656790152709047)
          ·
            refine ⟨15920623841485185229063571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10613749227656790152709047 15920623841485185229063571)
            ·
              refine ⟨23880935762227777843595357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15920623841485185229063571 23880935762227777843595357)
              ·
                refine ⟨8955350910835416691348259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23880935762227777843595357 8955350910835416691348259)
                ·
                  refine ⟨13433026366253125037022389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955350910835416691348259 13433026366253125037022389)
                  ·
                    refine ⟨1259346221836230472220849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13433026366253125037022389 1259346221836230472220849)
                    ·
                      rfl

theorem cell22_3678852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3678852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678852 prefixEnd_3678852 := by exact prefixLift 3678852
  have htrace : WordTrace (prefixWord ++ tailWord_3678852) baseStart_3678852 baseEnd_3678852 := by
    simpa [prefixWord, tailWord_3678852, baseEnd_3678852] using wordTrace_append hprefix tailTrace_3678852
  have hstable : (prefixWord ++ tailWord_3678852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678852).length < 2 ^ (prefixWord ++ tailWord_3678852).sum := by decide
  have hdescent : baseEnd_3678852 < baseStart_3678852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678948 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3678948 : Nat := 118140960795 + 3678948 * 2 ^ 59
def prefixEnd_3678948 : Nat := 4983230072969 + 3 ^ 40 * 3678948 * 2
def baseEnd_3678948 : Nat := 1259379084598118221820555

theorem tailTrace_3678948 : CollatzResearch.WordTrace tailWord_3678948 prefixEnd_3678948 1259379084598118221820555 := by
  unfold tailWord_3678948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67091128537903592570426749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89454838050538123427235665 67091128537903592570426749)
  ·
    refine ⟨25159173201713847213910031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67091128537903592570426749 25159173201713847213910031)
    ·
      refine ⟨37738759802570770820865047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25159173201713847213910031 37738759802570770820865047)
      ·
        refine ⟨56608139703856156231297571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37738759802570770820865047 56608139703856156231297571)
        ·
          refine ⟨84912209555784234346946357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56608139703856156231297571 84912209555784234346946357)
          ·
            refine ⟨7960519645854771970026221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84912209555784234346946357 7960519645854771970026221)
            ·
              refine ⟨2985194867195539488759833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7960519645854771970026221 2985194867195539488759833)
              ·
                refine ⟨2238896150396654616569875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985194867195539488759833 2238896150396654616569875)
                ·
                  refine ⟨3358344225594981924854813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238896150396654616569875 3358344225594981924854813)
                  ·
                    refine ⟨1259379084598118221820555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358344225594981924854813 1259379084598118221820555)
                    ·
                      rfl

theorem cell22_3678948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3678948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3678948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3678948 prefixEnd_3678948 := by exact prefixLift 3678948
  have htrace : WordTrace (prefixWord ++ tailWord_3678948) baseStart_3678948 baseEnd_3678948 := by
    simpa [prefixWord, tailWord_3678948, baseEnd_3678948] using wordTrace_append hprefix tailTrace_3678948
  have hstable : (prefixWord ++ tailWord_3678948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678948).length < 2 ^ (prefixWord ++ tailWord_3678948).sum := by decide
  have hdescent : baseEnd_3678948 < baseStart_3678948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679066 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_3679066 : Nat := 118140960795 + 3679066 * 2 ^ 59
def prefixEnd_3679066 : Nat := 4983230072969 + 3 ^ 40 * 3679066 * 2
def baseEnd_3679066 : Nat := 1259419478409605247370193

theorem tailTrace_3679066 : CollatzResearch.WordTrace tailWord_3679066 prefixEnd_3679066 1259419478409605247370193 := by
  unfold tailWord_3679066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546640222344922823412263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89457707259586460862432701 33546640222344922823412263)
  ·
    refine ⟨50319960333517384235118395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33546640222344922823412263 50319960333517384235118395)
    ·
      refine ⟨75479940500276076352677593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50319960333517384235118395 75479940500276076352677593)
      ·
        refine ⟨56609955375207057264508195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75479940500276076352677593 56609955375207057264508195)
        ·
          refine ⟨84914933062810585896762293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56609955375207057264508195 84914933062810585896762293)
          ·
            refine ⟨7960774974638492427821465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84914933062810585896762293 7960774974638492427821465)
            ·
              refine ⟨5970581230978869320866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960774974638492427821465 5970581230978869320866099)
              ·
                refine ⟨8955871846468303981299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970581230978869320866099 8955871846468303981299149)
                ·
                  refine ⟨3358451942425613992987181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8955871846468303981299149 3358451942425613992987181)
                  ·
                    refine ⟨1259419478409605247370193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358451942425613992987181 1259419478409605247370193)
                    ·
                      rfl

theorem cell22_3679066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_3679066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679066 prefixEnd_3679066 := by exact prefixLift 3679066
  have htrace : WordTrace (prefixWord ++ tailWord_3679066) baseStart_3679066 baseEnd_3679066 := by
    simpa [prefixWord, tailWord_3679066, baseEnd_3679066] using wordTrace_append hprefix tailTrace_3679066
  have hstable : (prefixWord ++ tailWord_3679066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679066).length < 2 ^ (prefixWord ++ tailWord_3679066).sum := by decide
  have hdescent : baseEnd_3679066 < baseStart_3679066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679130 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_3679130 : Nat := 118140960795 + 3679130 * 2 ^ 59
def prefixEnd_3679130 : Nat := 4983230072969 + 3 ^ 40 * 3679130 * 2
def baseEnd_3679130 : Nat := 419813795639176804589999

theorem tailTrace_3679130 : CollatzResearch.WordTrace tailWord_3679130 prefixEnd_3679130 419813795639176804589999 := by
  unfold tailWord_3679130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547223790286957555994711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89459263440765220149319229 33547223790286957555994711)
  ·
    refine ⟨50320835685430436333992067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33547223790286957555994711 50320835685430436333992067)
    ·
      refine ⟨75481253528145654500988101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50320835685430436333992067 75481253528145654500988101)
      ·
        refine ⟨14152735036527310218935269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75481253528145654500988101 14152735036527310218935269)
        ·
          refine ⟨2653637819348870666050363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14152735036527310218935269 2653637819348870666050363)
          ·
            refine ⟨3980456729023305999075545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653637819348870666050363 3980456729023305999075545)
            ·
              refine ⟨2985342546767479499306659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980456729023305999075545 2985342546767479499306659)
              ·
                refine ⟨4478013820151219248959989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985342546767479499306659 4478013820151219248959989)
                ·
                  refine ⟨419813795639176804589999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4478013820151219248959989 419813795639176804589999)
                  ·
                    rfl

theorem cell22_3679130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_3679130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679130 prefixEnd_3679130 := by exact prefixLift 3679130
  have htrace : WordTrace (prefixWord ++ tailWord_3679130) baseStart_3679130 baseEnd_3679130 := by
    simpa [prefixWord, tailWord_3679130, baseEnd_3679130] using wordTrace_append hprefix tailTrace_3679130
  have hstable : (prefixWord ++ tailWord_3679130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679130).length < 2 ^ (prefixWord ++ tailWord_3679130).sum := by decide
  have hdescent : baseEnd_3679130 < baseStart_3679130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679186 : List Nat := [3, 2, 2, 3, 1, 1, 3, 7]
def baseStart_3679186 : Nat := 118140960795 + 3679186 * 2 ^ 59
def prefixEnd_3679186 : Nat := 4983230072969 + 3 ^ 40 * 3679186 * 2
def baseEnd_3679186 : Nat := 139940061873551659374425

theorem tailTrace_3679186 : CollatzResearch.WordTrace tailWord_3679186 prefixEnd_3679186 139940061873551659374425 := by
  unfold tailWord_3679186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547734412236237947004353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89460625099296634525344941 33547734412236237947004353)
  ·
    refine ⟨25160800809177178460253265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33547734412236237947004353 25160800809177178460253265)
    ·
      refine ⟨18870600606882883845189949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25160800809177178460253265 18870600606882883845189949)
      ·
        refine ⟨7076475227581081441946231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18870600606882883845189949 7076475227581081441946231)
        ·
          refine ⟨10614712841371622162919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076475227581081441946231 10614712841371622162919347)
          ·
            refine ⟨15922069262057433244379021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614712841371622162919347 15922069262057433244379021)
            ·
              refine ⟨5970775973271537466642133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15922069262057433244379021 5970775973271537466642133)
              ·
                refine ⟨139940061873551659374425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5970775973271537466642133 139940061873551659374425)
                ·
                  rfl

theorem cell22_3679186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_3679186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679186 prefixEnd_3679186 := by exact prefixLift 3679186
  have htrace : WordTrace (prefixWord ++ tailWord_3679186) baseStart_3679186 baseEnd_3679186 := by
    simpa [prefixWord, tailWord_3679186, baseEnd_3679186] using wordTrace_append hprefix tailTrace_3679186
  have hstable : (prefixWord ++ tailWord_3679186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679186).length < 2 ^ (prefixWord ++ tailWord_3679186).sum := by decide
  have hdescent : baseEnd_3679186 < baseStart_3679186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679190 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_3679190 : Nat := 118140960795 + 3679190 * 2 ^ 59
def prefixEnd_3679190 : Nat := 4983230072969 + 3 ^ 40 * 3679190 * 2
def baseEnd_3679190 : Nat := 1259461926143710257269813

theorem tailTrace_3679190 : CollatzResearch.WordTrace tailWord_3679190 prefixEnd_3679190 1259461926143710257269813 := by
  unfold tailWord_3679190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386942721308153779447689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89460722360620306980775349 8386942721308153779447689)
  ·
    refine ⟨6290207040981115334585767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8386942721308153779447689 6290207040981115334585767)
    ·
      refine ⟨9435310561471673001878651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290207040981115334585767 9435310561471673001878651)
      ·
        refine ⟨14152965842207509502817977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435310561471673001878651 14152965842207509502817977)
        ·
          refine ⟨10614724381655632127113483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14152965842207509502817977 10614724381655632127113483)
          ·
            refine ⟨15922086572483448190670225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614724381655632127113483 15922086572483448190670225)
            ·
              refine ⟨11941564929362586143002669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15922086572483448190670225 11941564929362586143002669)
              ·
                refine ⟨4478086848510969803626001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11941564929362586143002669 4478086848510969803626001)
                ·
                  refine ⟨3358565136383227352719501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4478086848510969803626001 3358565136383227352719501)
                  ·
                    refine ⟨1259461926143710257269813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358565136383227352719501 1259461926143710257269813)
                    ·
                      rfl

theorem cell22_3679190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_3679190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679190 prefixEnd_3679190 := by exact prefixLift 3679190
  have htrace : WordTrace (prefixWord ++ tailWord_3679190) baseStart_3679190 baseEnd_3679190 := by
    simpa [prefixWord, tailWord_3679190, baseEnd_3679190] using wordTrace_append hprefix tailTrace_3679190
  have hstable : (prefixWord ++ tailWord_3679190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679190).length < 2 ^ (prefixWord ++ tailWord_3679190).sum := by decide
  have hdescent : baseEnd_3679190 < baseStart_3679190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679205 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_3679205 : Nat := 118140960795 + 3679205 * 2 ^ 59
def prefixEnd_3679205 : Nat := 4983230072969 + 3 ^ 40 * 3679205 * 2
def baseEnd_3679205 : Nat := 1259467060950255218144767

theorem tailTrace_3679205 : CollatzResearch.WordTrace tailWord_3679205 prefixEnd_3679205 1259467060950255218144767 := by
  unfold tailWord_3679205
  simp only [CollatzResearch.WordTrace]
  refine ⟨134191630635876118032959069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89461087090584078688639379 134191630635876118032959069)
  ·
    refine ⟨50321861488453544262359651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134191630635876118032959069 50321861488453544262359651)
    ·
      refine ⟨75482792232680316393539477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50321861488453544262359651 75482792232680316393539477)
      ·
        refine ⟨3538255885906889830947163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75482792232680316393539477 3538255885906889830947163)
        ·
          refine ⟨5307383828860334746420745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538255885906889830947163 5307383828860334746420745)
          ·
            refine ⟨3980537871645251059815559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307383828860334746420745 3980537871645251059815559)
            ·
              refine ⟨5970806807467876589723339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980537871645251059815559 5970806807467876589723339)
              ·
                refine ⟨8956210211201814884585009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970806807467876589723339 8956210211201814884585009)
                ·
                  refine ⟨6717157658401361163438757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956210211201814884585009 6717157658401361163438757)
                  ·
                    refine ⟨1259467060950255218144767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717157658401361163438757 1259467060950255218144767)
                    ·
                      rfl

theorem cell22_3679205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_3679205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679205 prefixEnd_3679205 := by exact prefixLift 3679205
  have htrace : WordTrace (prefixWord ++ tailWord_3679205) baseStart_3679205 baseEnd_3679205 := by
    simpa [prefixWord, tailWord_3679205, baseEnd_3679205] using wordTrace_append hprefix tailTrace_3679205
  have hstable : (prefixWord ++ tailWord_3679205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679205).length < 2 ^ (prefixWord ++ tailWord_3679205).sum := by decide
  have hdescent : baseEnd_3679205 < baseStart_3679205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679246 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3679246 : Nat := 118140960795 + 3679246 * 2 ^ 59
def prefixEnd_3679246 : Nat := 4983230072969 + 3 ^ 40 * 3679246 * 2
def baseEnd_3679246 : Nat := 1259481096088144777869641

theorem tailTrace_3679246 : CollatzResearch.WordTrace tailWord_3679246 prefixEnd_3679246 1259481096088144777869641 := by
  unfold tailWord_3679246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774140753590947754400199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89462084019151721356801061 16774140753590947754400199)
  ·
    refine ⟨25161211130386421631600299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16774140753590947754400199 25161211130386421631600299)
    ·
      refine ⟨37741816695579632447400449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161211130386421631600299 37741816695579632447400449)
      ·
        refine ⟨28306362521684724335550337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37741816695579632447400449 28306362521684724335550337)
        ·
          refine ⟨21229771891263543251662753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28306362521684724335550337 21229771891263543251662753)
          ·
            refine ⟨15922328918447657438747065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21229771891263543251662753 15922328918447657438747065)
            ·
              refine ⟨11941746688835743079060299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15922328918447657438747065 11941746688835743079060299)
              ·
                refine ⟨17912620033253614618590449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941746688835743079060299 17912620033253614618590449)
                ·
                  refine ⟨13434465024940210963942837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17912620033253614618590449 13434465024940210963942837)
                  ·
                    refine ⟨1259481096088144777869641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13434465024940210963942837 1259481096088144777869641)
                    ·
                      rfl

theorem cell22_3679246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3679246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679246 prefixEnd_3679246 := by exact prefixLift 3679246
  have htrace : WordTrace (prefixWord ++ tailWord_3679246) baseStart_3679246 baseEnd_3679246 := by
    simpa [prefixWord, tailWord_3679246, baseEnd_3679246] using wordTrace_append hprefix tailTrace_3679246
  have hstable : (prefixWord ++ tailWord_3679246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679246).length < 2 ^ (prefixWord ++ tailWord_3679246).sum := by decide
  have hdescent : baseEnd_3679246 < baseStart_3679246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679278 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3679278 : Nat := 118140960795 + 3679278 * 2 ^ 59
def prefixEnd_3679278 : Nat := 4983230072969 + 3 ^ 40 * 3679278 * 2
def baseEnd_3679278 : Nat := 1259492050342107361069543

theorem tailTrace_3679278 : CollatzResearch.WordTrace tailWord_3679278 prefixEnd_3679278 1259492050342107361069543 := by
  unfold tailWord_3679278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774286645576456437545811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89462862109741101000244325 16774286645576456437545811)
  ·
    refine ⟨25161429968364684656318717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16774286645576456437545811 25161429968364684656318717)
    ·
      refine ⟨9435536238136756746119519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25161429968364684656318717 9435536238136756746119519)
      ·
        refine ⟨14153304357205135119179279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435536238136756746119519 14153304357205135119179279)
        ·
          refine ⟨21229956535807702678768919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153304357205135119179279 21229956535807702678768919)
          ·
            refine ⟨31844934803711554018153379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229956535807702678768919 31844934803711554018153379)
            ·
              refine ⟨47767402205567331027230069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31844934803711554018153379 47767402205567331027230069)
              ·
                refine ⟨4478193956771937283802819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47767402205567331027230069 4478193956771937283802819)
                ·
                  refine ⟨6717290935157905925704229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478193956771937283802819 6717290935157905925704229)
                  ·
                    refine ⟨1259492050342107361069543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717290935157905925704229 1259492050342107361069543)
                    ·
                      rfl

theorem cell22_3679278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3679278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679278 prefixEnd_3679278 := by exact prefixLift 3679278
  have htrace : WordTrace (prefixWord ++ tailWord_3679278) baseStart_3679278 baseEnd_3679278 := by
    simpa [prefixWord, tailWord_3679278, baseEnd_3679278] using wordTrace_append hprefix tailTrace_3679278
  have hstable : (prefixWord ++ tailWord_3679278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679278).length < 2 ^ (prefixWord ++ tailWord_3679278).sum := by decide
  have hdescent : baseEnd_3679278 < baseStart_3679278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679293 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3679293 : Nat := 118140960795 + 3679293 * 2 ^ 59
def prefixEnd_3679293 : Nat := 4983230072969 + 3 ^ 40 * 3679293 * 2
def baseEnd_3679293 : Nat := 419832395049550773981499

theorem tailTrace_3679293 : CollatzResearch.WordTrace tailWord_3679293 prefixEnd_3679293 419832395049550773981499 := by
  unfold tailWord_3679293
  simp only [CollatzResearch.WordTrace]
  refine ⟨134194840259557309062162533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89463226839704872708108355 134194840259557309062162533)
  ·
    refine ⟨25161532548666995449155475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134194840259557309062162533 25161532548666995449155475)
    ·
      refine ⟨37742298823000493173733213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161532548666995449155475 37742298823000493173733213)
      ·
        refine ⟨14153362058625184940149955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37742298823000493173733213 14153362058625184940149955)
        ·
          refine ⟨21230043087937777410224933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153362058625184940149955 21230043087937777410224933)
          ·
            refine ⟨3980633078988333264417175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21230043087937777410224933 3980633078988333264417175)
            ·
              refine ⟨5970949618482499896625763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980633078988333264417175 5970949618482499896625763)
              ·
                refine ⟨8956424427723749844938645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970949618482499896625763 8956424427723749844938645)
                ·
                  refine ⟨419832395049550773981499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956424427723749844938645 419832395049550773981499)
                  ·
                    rfl

theorem cell22_3679293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3679293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679293 prefixEnd_3679293 := by exact prefixLift 3679293
  have htrace : WordTrace (prefixWord ++ tailWord_3679293) baseStart_3679293 baseEnd_3679293 := by
    simpa [prefixWord, tailWord_3679293, baseEnd_3679293] using wordTrace_append hprefix tailTrace_3679293
  have hstable : (prefixWord ++ tailWord_3679293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679293).length < 2 ^ (prefixWord ++ tailWord_3679293).sum := by decide
  have hdescent : baseEnd_3679293 < baseStart_3679293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679325 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3679325 : Nat := 118140960795 + 3679325 * 2 ^ 59
def prefixEnd_3679325 : Nat := 4983230072969 + 3 ^ 40 * 3679325 * 2
def baseEnd_3679325 : Nat := 1259508139402614905144399

theorem tailTrace_3679325 : CollatzResearch.WordTrace tailWord_3679325 prefixEnd_3679325 1259508139402614905144399 := by
  unfold tailWord_3679325
  simp only [CollatzResearch.WordTrace]
  refine ⟨134196007395441378527327429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89464004930294252351551619 134196007395441378527327429)
  ·
    refine ⟨25161751386645258473873893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134196007395441378527327429 25161751386645258473873893)
    ·
      refine ⟨4717828384995985963851355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25161751386645258473873893 4717828384995985963851355)
      ·
        refine ⟨7076742577493978945777033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717828384995985963851355 7076742577493978945777033)
        ·
          refine ⟨5307556933120484209332775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7076742577493978945777033 5307556933120484209332775)
          ·
            refine ⟨7961335399680726313999163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307556933120484209332775 7961335399680726313999163)
            ·
              refine ⟨11942003099521089470998745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7961335399680726313999163 11942003099521089470998745)
              ·
                refine ⟨8956502324640817103249059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11942003099521089470998745 8956502324640817103249059)
                ·
                  refine ⟨13434753486961225654873589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956502324640817103249059 13434753486961225654873589)
                  ·
                    refine ⟨1259508139402614905144399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13434753486961225654873589 1259508139402614905144399)
                    ·
                      rfl

theorem cell22_3679325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3679325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679325 prefixEnd_3679325 := by exact prefixLift 3679325
  have htrace : WordTrace (prefixWord ++ tailWord_3679325) baseStart_3679325 baseEnd_3679325 := by
    simpa [prefixWord, tailWord_3679325, baseEnd_3679325] using wordTrace_append hprefix tailTrace_3679325
  have hstable : (prefixWord ++ tailWord_3679325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679325).length < 2 ^ (prefixWord ++ tailWord_3679325).sum := by decide
  have hdescent : baseEnd_3679325 < baseStart_3679325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679411 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 6]
def baseStart_3679411 : Nat := 118140960795 + 3679411 * 2 ^ 59
def prefixEnd_3679411 : Nat := 4983230072969 + 3 ^ 40 * 3679411 * 2
def baseEnd_3679411 : Nat := 419845859653379782498045

theorem tailTrace_3679411 : CollatzResearch.WordTrace tailWord_3679411 prefixEnd_3679411 419845859653379782498045 := by
  unfold tailWord_3679411
  simp only [CollatzResearch.WordTrace]
  refine ⟨134199144073129815214958087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89466096048753210143305391 134199144073129815214958087)
  ·
    refine ⟨201298716109694722822437131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134199144073129815214958087 201298716109694722822437131)
    ·
      refine ⟨301948074164542084233655697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201298716109694722822437131 301948074164542084233655697)
      ·
        refine ⟨226461055623406563175241773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301948074164542084233655697 226461055623406563175241773)
        ·
          refine ⟨84922895858777461190715665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226461055623406563175241773 84922895858777461190715665)
          ·
            refine ⟨63692171894083095893036749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84922895858777461190715665 63692171894083095893036749)
            ·
              refine ⟨23884564460281160959888781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63692171894083095893036749 23884564460281160959888781)
              ·
                refine ⟨8956711672605435359958293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23884564460281160959888781 8956711672605435359958293)
                ·
                  refine ⟨419845859653379782498045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8956711672605435359958293 419845859653379782498045)
                  ·
                    rfl

theorem cell22_3679411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_3679411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679411 prefixEnd_3679411 := by exact prefixLift 3679411
  have htrace : WordTrace (prefixWord ++ tailWord_3679411) baseStart_3679411 baseEnd_3679411 := by
    simpa [prefixWord, tailWord_3679411, baseEnd_3679411] using wordTrace_append hprefix tailTrace_3679411
  have hstable : (prefixWord ++ tailWord_3679411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679411).length < 2 ^ (prefixWord ++ tailWord_3679411).sum := by decide
  have hdescent : baseEnd_3679411 < baseStart_3679411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679456 : List Nat := [2, 1, 1, 3, 1, 4, 10]
def baseStart_3679456 : Nat := 118140960795 + 3679456 * 2 ^ 59
def prefixEnd_3679456 : Nat := 4983230072969 + 3 ^ 40 * 3679456 * 2
def baseEnd_3679456 : Nat := 46650110495547193708111

theorem tailTrace_3679456 : CollatzResearch.WordTrace tailWord_3679456 prefixEnd_3679456 46650110495547193708111 := by
  unfold tailWord_3679456
  simp only [CollatzResearch.WordTrace]
  refine ⟨67100392678983393950173111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89467190238644525266897481 67100392678983393950173111)
  ·
    refine ⟨100650589018475090925259667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67100392678983393950173111 100650589018475090925259667)
    ·
      refine ⟨150975883527712636387889501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100650589018475090925259667 150975883527712636387889501)
      ·
        refine ⟨56615956322892238645458563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150975883527712636387889501 56615956322892238645458563)
        ·
          refine ⟨84923934484338357968187845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56615956322892238645458563 84923934484338357968187845)
          ·
            refine ⟨15923237715813442119035221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84923934484338357968187845 15923237715813442119035221)
            ·
              refine ⟨46650110495547193708111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15923237715813442119035221 46650110495547193708111)
              ·
                rfl

theorem cell22_3679456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 10].length) (baseStart_3679456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679456 prefixEnd_3679456 := by exact prefixLift 3679456
  have htrace : WordTrace (prefixWord ++ tailWord_3679456) baseStart_3679456 baseEnd_3679456 := by
    simpa [prefixWord, tailWord_3679456, baseEnd_3679456] using wordTrace_append hprefix tailTrace_3679456
  have hstable : (prefixWord ++ tailWord_3679456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679456).length < 2 ^ (prefixWord ++ tailWord_3679456).sum := by decide
  have hdescent : baseEnd_3679456 < baseStart_3679456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679488 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 5, 3]
def baseStart_3679488 : Nat := 118140960795 + 3679488 * 2 ^ 59
def prefixEnd_3679488 : Nat := 4983230072969 + 3 ^ 40 * 3679488 * 2
def baseEnd_3679488 : Nat := 1259563937633736813318899

theorem tailTrace_3679488 : CollatzResearch.WordTrace tailWord_3679488 prefixEnd_3679488 1259563937633736813318899 := by
  unfold tailWord_3679488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67100976246925428682755559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89467968329233904910340745 67100976246925428682755559)
  ·
    refine ⟨100651464370388143024133339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67100976246925428682755559 100651464370388143024133339)
    ·
      refine ⟨150977196555582214536200009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100651464370388143024133339 150977196555582214536200009)
      ·
        refine ⟨113232897416686660902150007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150977196555582214536200009 113232897416686660902150007)
        ·
          refine ⟨169849346125029991353225011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113232897416686660902150007 169849346125029991353225011)
          ·
            refine ⟨254774019187544987029837517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169849346125029991353225011 254774019187544987029837517)
            ·
              refine ⟨95540257195329370136189069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254774019187544987029837517 95540257195329370136189069)
              ·
                refine ⟨35827596448248513801070901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95540257195329370136189069 35827596448248513801070901)
                ·
                  refine ⟨3358837167023298168850397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35827596448248513801070901 3358837167023298168850397)
                  ·
                    refine ⟨1259563937633736813318899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358837167023298168850397 1259563937633736813318899)
                    ·
                      rfl

theorem cell22_3679488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_3679488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679488 prefixEnd_3679488 := by exact prefixLift 3679488
  have htrace : WordTrace (prefixWord ++ tailWord_3679488) baseStart_3679488 baseEnd_3679488 := by
    simpa [prefixWord, tailWord_3679488, baseEnd_3679488] using wordTrace_append hprefix tailTrace_3679488
  have hstable : (prefixWord ++ tailWord_3679488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679488).length < 2 ^ (prefixWord ++ tailWord_3679488).sum := by decide
  have hdescent : baseEnd_3679488 < baseStart_3679488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679556 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3679556 : Nat := 118140960795 + 3679556 * 2 ^ 59
def prefixEnd_3679556 : Nat := 4983230072969 + 3 ^ 40 * 3679556 * 2
def baseEnd_3679556 : Nat := 1259587215423407302618691

theorem tailTrace_3679556 : CollatzResearch.WordTrace tailWord_3679556 prefixEnd_3679556 1259587215423407302618691 := by
  unfold tailWord_3679556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67102216328802252489493261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89469621771736336652657681 67102216328802252489493261)
  ·
    refine ⟨25163331123300844683559973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67102216328802252489493261 25163331123300844683559973)
    ·
      refine ⟨4718124585618908378167495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25163331123300844683559973 4718124585618908378167495)
      ·
        refine ⟨7077186878428362567251243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718124585618908378167495 7077186878428362567251243)
        ·
          refine ⟨10615780317642543850876865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077186878428362567251243 10615780317642543850876865)
          ·
            refine ⟨7961835238231907888157649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10615780317642543850876865 7961835238231907888157649)
            ·
              refine ⟨5971376428673930916118237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961835238231907888157649 5971376428673930916118237)
              ·
                refine ⟨2239266160752724093544339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5971376428673930916118237 2239266160752724093544339)
                ·
                  refine ⟨3358899241129086140316509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239266160752724093544339 3358899241129086140316509)
                  ·
                    refine ⟨1259587215423407302618691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358899241129086140316509 1259587215423407302618691)
                    ·
                      rfl

theorem cell22_3679556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3679556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679556 prefixEnd_3679556 := by exact prefixLift 3679556
  have htrace : WordTrace (prefixWord ++ tailWord_3679556) baseStart_3679556 baseEnd_3679556 := by
    simpa [prefixWord, tailWord_3679556, baseEnd_3679556] using wordTrace_append hprefix tailTrace_3679556
  have hstable : (prefixWord ++ tailWord_3679556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679556).length < 2 ^ (prefixWord ++ tailWord_3679556).sum := by decide
  have hdescent : baseEnd_3679556 < baseStart_3679556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679578 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3679578 : Nat := 118140960795 + 3679578 * 2 ^ 59
def prefixEnd_3679578 : Nat := 4983230072969 + 3 ^ 40 * 3679578 * 2
def baseEnd_3679578 : Nat := 1259594746473006578568623

theorem tailTrace_3679578 : CollatzResearch.WordTrace tailWord_3679578 prefixEnd_3679578 1259594746473006578568623 := by
  unfold tailWord_3679578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33551308765881200684071847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89470156709016535157524925 33551308765881200684071847)
  ·
    refine ⟨50326963148821801026107771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33551308765881200684071847 50326963148821801026107771)
    ·
      refine ⟨75490444723232701539161657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50326963148821801026107771 75490444723232701539161657)
      ·
        refine ⟨56617833542424526154371243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75490444723232701539161657 56617833542424526154371243)
        ·
          refine ⟨84926750313636789231556865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56617833542424526154371243 84926750313636789231556865)
          ·
            refine ⟨63695062735227591923667649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84926750313636789231556865 63695062735227591923667649)
            ·
              refine ⟨47771297051420693942750737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63695062735227591923667649 47771297051420693942750737)
              ·
                refine ⟨35828472788565520457063053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47771297051420693942750737 35828472788565520457063053)
                ·
                  refine ⟨13435677295712070171398645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35828472788565520457063053 13435677295712070171398645)
                  ·
                    refine ⟨1259594746473006578568623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13435677295712070171398645 1259594746473006578568623)
                    ·
                      rfl

theorem cell22_3679578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3679578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679578 prefixEnd_3679578 := by exact prefixLift 3679578
  have htrace : WordTrace (prefixWord ++ tailWord_3679578) baseStart_3679578 baseEnd_3679578 := by
    simpa [prefixWord, tailWord_3679578, baseEnd_3679578] using wordTrace_append hprefix tailTrace_3679578
  have hstable : (prefixWord ++ tailWord_3679578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679578).length < 2 ^ (prefixWord ++ tailWord_3679578).sum := by decide
  have hdescent : baseEnd_3679578 < baseStart_3679578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679593 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3679593 : Nat := 118140960795 + 3679593 * 2 ^ 59
def prefixEnd_3679593 : Nat := 4983230072969 + 3 ^ 40 * 3679593 * 2
def baseEnd_3679593 : Nat := 1259599881279551539443577

theorem tailTrace_3679593 : CollatzResearch.WordTrace tailWord_3679593 prefixEnd_3679593 1259599881279551539443577 := by
  unfold tailWord_3679593
  simp only [CollatzResearch.WordTrace]
  refine ⟨134205782158470460298083433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89470521438980306865388955 134205782158470460298083433)
  ·
    refine ⟨100654336618852845223562575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134205782158470460298083433 100654336618852845223562575)
    ·
      refine ⟨150981504928279267835343863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100654336618852845223562575 150981504928279267835343863)
      ·
        refine ⟨226472257392418901753015795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150981504928279267835343863 226472257392418901753015795)
        ·
          refine ⟨339708386088628352629523693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226472257392418901753015795 339708386088628352629523693)
          ·
            refine ⟨127390644783235632236071385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339708386088628352629523693 127390644783235632236071385)
            ·
              refine ⟨95542983587426724177053539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127390644783235632236071385 95542983587426724177053539)
              ·
                refine ⟨143314475381140086265580309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95542983587426724177053539 143314475381140086265580309)
                ·
                  refine ⟨6717866033490941543699077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143314475381140086265580309 6717866033490941543699077)
                  ·
                    refine ⟨1259599881279551539443577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717866033490941543699077 1259599881279551539443577)
                    ·
                      rfl

theorem cell22_3679593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3679593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679593 prefixEnd_3679593 := by exact prefixLift 3679593
  have htrace : WordTrace (prefixWord ++ tailWord_3679593) baseStart_3679593 baseEnd_3679593 := by
    simpa [prefixWord, tailWord_3679593, baseEnd_3679593] using wordTrace_append hprefix tailTrace_3679593
  have hstable : (prefixWord ++ tailWord_3679593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679593).length < 2 ^ (prefixWord ++ tailWord_3679593).sum := by decide
  have hdescent : baseEnd_3679593 < baseStart_3679593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679625 : List Nat := [1, 2, 1, 1, 7, 2, 8]
def baseStart_3679625 : Nat := 118140960795 + 3679625 * 2 ^ 59
def prefixEnd_3679625 : Nat := 4983230072969 + 3 ^ 40 * 3679625 * 2
def baseEnd_3679625 : Nat := 46652253167907930468277

theorem tailTrace_3679625 : CollatzResearch.WordTrace tailWord_3679625 prefixEnd_3679625 46652253167907930468277 := by
  unfold tailWord_3679625
  simp only [CollatzResearch.WordTrace]
  refine ⟨134206949294354529763248329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89471299529569686508832219 134206949294354529763248329)
  ·
    refine ⟨100655211970765897322436247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134206949294354529763248329 100655211970765897322436247)
    ·
      refine ⟨150982817956148845983654371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100655211970765897322436247 150982817956148845983654371)
      ·
        refine ⟨226474226934223268975481557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150982817956148845983654371 226474226934223268975481557)
        ·
          refine ⟨5307989693770857866612849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226474226934223268975481557 5307989693770857866612849)
          ·
            refine ⟨3980992270328143399959637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307989693770857866612849 3980992270328143399959637)
            ·
              refine ⟨46652253167907930468277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3980992270328143399959637 46652253167907930468277)
              ·
                rfl

theorem cell22_3679625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 8].length) (baseStart_3679625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679625 prefixEnd_3679625 := by exact prefixLift 3679625
  have htrace : WordTrace (prefixWord ++ tailWord_3679625) baseStart_3679625 baseEnd_3679625 := by
    simpa [prefixWord, tailWord_3679625, baseEnd_3679625] using wordTrace_append hprefix tailTrace_3679625
  have hstable : (prefixWord ++ tailWord_3679625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679625).length < 2 ^ (prefixWord ++ tailWord_3679625).sum := by decide
  have hdescent : baseEnd_3679625 < baseStart_3679625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679646 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3679646 : Nat := 118140960795 + 3679646 * 2 ^ 59
def prefixEnd_3679646 : Nat := 4983230072969 + 3 ^ 40 * 3679646 * 2
def baseEnd_3679646 : Nat := 1259618024262677067868415

theorem tailTrace_3679646 : CollatzResearch.WordTrace tailWord_3679646 prefixEnd_3679646 1259618024262677067868415 := by
  unfold tailWord_3679646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775964403409806293720349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89471810151518966899841861 16775964403409806293720349)
  ·
    refine ⟨6290986651278677360145131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16775964403409806293720349 6290986651278677360145131)
    ·
      refine ⟨9436479976918016040217697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290986651278677360145131 9436479976918016040217697)
      ·
        refine ⟨7077359982688512030163273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9436479976918016040217697 7077359982688512030163273)
        ·
          refine ⟨5308019987016384022622455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7077359982688512030163273 5308019987016384022622455)
          ·
            refine ⟨7962029980524576033933683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308019987016384022622455 7962029980524576033933683)
            ·
              refine ⟨11943044970786864050900525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962029980524576033933683 11943044970786864050900525)
              ·
                refine ⟨4478641864045074019087697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11943044970786864050900525 4478641864045074019087697)
                ·
                  refine ⟨3358981398033805514315773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4478641864045074019087697 3358981398033805514315773)
                  ·
                    refine ⟨1259618024262677067868415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3358981398033805514315773 1259618024262677067868415)
                    ·
                      rfl

theorem cell22_3679646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3679646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679646 prefixEnd_3679646 := by exact prefixLift 3679646
  have htrace : WordTrace (prefixWord ++ tailWord_3679646) baseStart_3679646 baseEnd_3679646 := by
    simpa [prefixWord, tailWord_3679646, baseEnd_3679646] using wordTrace_append hprefix tailTrace_3679646
  have hstable : (prefixWord ++ tailWord_3679646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679646).length < 2 ^ (prefixWord ++ tailWord_3679646).sum := by decide
  have hdescent : baseEnd_3679646 < baseStart_3679646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679653 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3679653 : Nat := 118140960795 + 3679653 * 2 ^ 59
def prefixEnd_3679653 : Nat := 4983230072969 + 3 ^ 40 * 3679653 * 2
def baseEnd_3679653 : Nat := 419873473501910460981131

theorem tailTrace_3679653 : CollatzResearch.WordTrace tailWord_3679653 prefixEnd_3679653 419873473501910460981131 := by
  unfold tailWord_3679653
  simp only [CollatzResearch.WordTrace]
  refine ⟨134207970538253090545267613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89471980358835393696845075 134207970538253090545267613)
  ·
    refine ⟨50327988951844908954475355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134207970538253090545267613 50327988951844908954475355)
    ·
      refine ⟨75491983427767363431713033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50327988951844908954475355 75491983427767363431713033)
      ·
        refine ⟨56618987570825522573784775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75491983427767363431713033 56618987570825522573784775)
        ·
          refine ⟨84928481356238283860677163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56618987570825522573784775 84928481356238283860677163)
          ·
            refine ⟨127392722034357425791015745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84928481356238283860677163 127392722034357425791015745)
            ·
              refine ⟨95544541525768069343261809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127392722034357425791015745 95544541525768069343261809)
              ·
                refine ⟨71658406144326052007446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95544541525768069343261809 71658406144326052007446357)
                ·
                  refine ⟨419873473501910460981131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71658406144326052007446357 419873473501910460981131)
                  ·
                    rfl

theorem cell22_3679653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3679653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679653 prefixEnd_3679653 := by exact prefixLift 3679653
  have htrace : WordTrace (prefixWord ++ tailWord_3679653) baseStart_3679653 baseEnd_3679653 := by
    simpa [prefixWord, tailWord_3679653, baseEnd_3679653] using wordTrace_append hprefix tailTrace_3679653
  have hstable : (prefixWord ++ tailWord_3679653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679653).length < 2 ^ (prefixWord ++ tailWord_3679653).sum := by decide
  have hdescent : baseEnd_3679653 < baseStart_3679653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679682 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3679682 : Nat := 118140960795 + 3679682 * 2 ^ 59
def prefixEnd_3679682 : Nat := 4983230072969 + 3 ^ 40 * 3679682 * 2
def baseEnd_3679682 : Nat := 419876782599461657989435

theorem tailTrace_3679682 : CollatzResearch.WordTrace tailWord_3679682 prefixEnd_3679682 419876782599461657989435 := by
  unfold tailWord_3679682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33552257063787007124518325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89472685503432018998715533 33552257063787007124518325)
  ·
    refine ⟨3145524099730031917923593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33552257063787007124518325 3145524099730031917923593)
    ·
      refine ⟨2359143074797523938442695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145524099730031917923593 2359143074797523938442695)
      ·
        refine ⟨3538714612196285907664043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359143074797523938442695 3538714612196285907664043)
        ·
          refine ⟨5308071918294428861496065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538714612196285907664043 5308071918294428861496065)
          ·
            refine ⟨3981053938720821646122049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5308071918294428861496065 3981053938720821646122049)
            ·
              refine ⟨2985790454040616234591537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981053938720821646122049 2985790454040616234591537)
              ·
                refine ⟨2239342840530462175943653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985790454040616234591537 2239342840530462175943653)
                ·
                  refine ⟨419876782599461657989435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239342840530462175943653 419876782599461657989435)
                  ·
                    rfl

theorem cell22_3679682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3679682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679682 prefixEnd_3679682 := by exact prefixLift 3679682
  have htrace : WordTrace (prefixWord ++ tailWord_3679682) baseStart_3679682 baseEnd_3679682 := by
    simpa [prefixWord, tailWord_3679682, baseEnd_3679682] using wordTrace_append hprefix tailTrace_3679682
  have hstable : (prefixWord ++ tailWord_3679682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679682).length < 2 ^ (prefixWord ++ tailWord_3679682).sum := by decide
  have hdescent : baseEnd_3679682 < baseStart_3679682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679702 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3679702 : Nat := 118140960795 + 3679702 * 2 ^ 59
def prefixEnd_3679702 : Nat := 4983230072969 + 3 ^ 40 * 3679702 * 2
def baseEnd_3679702 : Nat := 1259637194207111588468243

theorem tailTrace_3679702 : CollatzResearch.WordTrace tailWord_3679702 prefixEnd_3679702 1259637194207111588468243 := by
  unfold tailWord_3679702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388109857192223244612585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89473171810050381275867573 8388109857192223244612585)
  ·
    refine ⟨6291082392894167433459439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8388109857192223244612585 6291082392894167433459439)
    ·
      refine ⟨9436623589341251150189159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291082392894167433459439 9436623589341251150189159)
      ·
        refine ⟨14154935384011876725283739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436623589341251150189159 14154935384011876725283739)
        ·
          refine ⟨21232403076017815087925609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154935384011876725283739 21232403076017815087925609)
          ·
            refine ⟨15924302307013361315944207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21232403076017815087925609 15924302307013361315944207)
            ·
              refine ⟨23886453460520041973916311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15924302307013361315944207 23886453460520041973916311)
              ·
                refine ⟨35829680190780062960874467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23886453460520041973916311 35829680190780062960874467)
                ·
                  refine ⟨53744520286170094441311701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35829680190780062960874467 53744520286170094441311701)
                  ·
                    refine ⟨1259637194207111588468243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53744520286170094441311701 1259637194207111588468243)
                    ·
                      rfl

theorem cell22_3679702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3679702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679702 prefixEnd_3679702 := by exact prefixLift 3679702
  have htrace : WordTrace (prefixWord ++ tailWord_3679702) baseStart_3679702 baseEnd_3679702 := by
    simpa [prefixWord, tailWord_3679702, baseEnd_3679702] using wordTrace_append hprefix tailTrace_3679702
  have hstable : (prefixWord ++ tailWord_3679702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679702).length < 2 ^ (prefixWord ++ tailWord_3679702).sum := by decide
  have hdescent : baseEnd_3679702 < baseStart_3679702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679715 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 8]
def baseStart_3679715 : Nat := 118140960795 + 3679715 * 2 ^ 59
def prefixEnd_3679715 : Nat := 4983230072969 + 3 ^ 40 * 3679715 * 2
def baseEnd_3679715 : Nat := 419880548124261295964401

theorem tailTrace_3679715 : CollatzResearch.WordTrace tailWord_3679715 prefixEnd_3679715 419880548124261295964401 := by
  unfold tailWord_3679715
  simp only [CollatzResearch.WordTrace]
  refine ⟨134210231864028475134024599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89473487909352316756016399 134210231864028475134024599)
  ·
    refine ⟨201315347796042712701036899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134210231864028475134024599 201315347796042712701036899)
    ·
      refine ⟨301973021694064069051555349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201315347796042712701036899 301973021694064069051555349)
      ·
        refine ⟨14154985391909253236791657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301973021694064069051555349 14154985391909253236791657)
        ·
          refine ⟨10616239043931939927593743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14154985391909253236791657 10616239043931939927593743)
          ·
            refine ⟨15924358565897909891390615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616239043931939927593743 15924358565897909891390615)
            ·
              refine ⟨23886537848846864837085923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15924358565897909891390615 23886537848846864837085923)
              ·
                refine ⟨35829806773270297255628885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23886537848846864837085923 35829806773270297255628885)
                ·
                  refine ⟨419880548124261295964401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35829806773270297255628885 419880548124261295964401)
                  ·
                    rfl

theorem cell22_3679715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_3679715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679715 prefixEnd_3679715 := by exact prefixLift 3679715
  have htrace : WordTrace (prefixWord ++ tailWord_3679715) baseStart_3679715 baseEnd_3679715 := by
    simpa [prefixWord, tailWord_3679715, baseEnd_3679715] using wordTrace_append hprefix tailTrace_3679715
  have hstable : (prefixWord ++ tailWord_3679715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679715).length < 2 ^ (prefixWord ++ tailWord_3679715).sum := by decide
  have hdescent : baseEnd_3679715 < baseStart_3679715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679717 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3679717 : Nat := 118140960795 + 3679717 * 2 ^ 59
def prefixEnd_3679717 : Nat := 4983230072969 + 3 ^ 40 * 3679717 * 2
def baseEnd_3679717 : Nat := 1259642329013656549343197

theorem tailTrace_3679717 : CollatzResearch.WordTrace tailWord_3679717 prefixEnd_3679717 1259642329013656549343197 := by
  unfold tailWord_3679717
  simp only [CollatzResearch.WordTrace]
  refine ⟨134210304810021229475597405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89473536540014152983731603 134210304810021229475597405)
  ·
    refine ⟨50328864303757961053349027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134210304810021229475597405 50328864303757961053349027)
    ·
      refine ⟨75493296455636941580023541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50328864303757961053349027 75493296455636941580023541)
      ·
        refine ⟨7077496542715963273127207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75493296455636941580023541 7077496542715963273127207)
        ·
          refine ⟨10616244814073944909690811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077496542715963273127207 10616244814073944909690811)
          ·
            refine ⟨15924367221110917364536217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616244814073944909690811 15924367221110917364536217)
            ·
              refine ⟨11943275415833188023402163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15924367221110917364536217 11943275415833188023402163)
              ·
                refine ⟨17914913123749782035103245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943275415833188023402163 17914913123749782035103245)
                ·
                  refine ⟨6718092421406168263163717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17914913123749782035103245 6718092421406168263163717)
                  ·
                    refine ⟨1259642329013656549343197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718092421406168263163717 1259642329013656549343197)
                    ·
                      rfl

theorem cell22_3679717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3679717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679717 prefixEnd_3679717 := by exact prefixLift 3679717
  have htrace : WordTrace (prefixWord ++ tailWord_3679717) baseStart_3679717 baseEnd_3679717 := by
    simpa [prefixWord, tailWord_3679717, baseEnd_3679717] using wordTrace_append hprefix tailTrace_3679717
  have hstable : (prefixWord ++ tailWord_3679717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679717).length < 2 ^ (prefixWord ++ tailWord_3679717).sum := by decide
  have hdescent : baseEnd_3679717 < baseStart_3679717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679734 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3679734 : Nat := 118140960795 + 3679734 * 2 ^ 59
def prefixEnd_3679734 : Nat := 4983230072969 + 3 ^ 40 * 3679734 * 2
def baseEnd_3679734 : Nat := 1259648148461074171668145

theorem tailTrace_3679734 : CollatzResearch.WordTrace tailWord_3679734 prefixEnd_3679734 1259648148461074171668145 := by
  unfold tailWord_3679734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388182803184977586185391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89473949900639760919310837 8388182803184977586185391)
  ·
    refine ⟨12582274204777466379278087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388182803184977586185391 12582274204777466379278087)
    ·
      refine ⟨18873411307166199568917131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12582274204777466379278087 18873411307166199568917131)
      ·
        refine ⟨28310116960749299353375697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18873411307166199568917131 28310116960749299353375697)
        ·
          refine ⟨21232587720561974515031773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28310116960749299353375697 21232587720561974515031773)
          ·
            refine ⟨7962220395210740443136915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21232587720561974515031773 7962220395210740443136915)
            ·
              refine ⟨11943330592816110664705373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962220395210740443136915 11943330592816110664705373)
              ·
                refine ⟨4478748972306041499264515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11943330592816110664705373 4478748972306041499264515)
                ·
                  refine ⟨6718123458459062248896773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478748972306041499264515 6718123458459062248896773)
                  ·
                    refine ⟨1259648148461074171668145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718123458459062248896773 1259648148461074171668145)
                    ·
                      rfl

theorem cell22_3679734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3679734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679734 prefixEnd_3679734 := by exact prefixLift 3679734
  have htrace : WordTrace (prefixWord ++ tailWord_3679734) baseStart_3679734 baseEnd_3679734 := by
    simpa [prefixWord, tailWord_3679734, baseEnd_3679734] using wordTrace_append hprefix tailTrace_3679734
  have hstable : (prefixWord ++ tailWord_3679734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679734).length < 2 ^ (prefixWord ++ tailWord_3679734).sum := by decide
  have hdescent : baseEnd_3679734 < baseStart_3679734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679747 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 2, 3]
def baseStart_3679747 : Nat := 118140960795 + 3679747 * 2 ^ 59
def prefixEnd_3679747 : Nat := 4983230072969 + 3 ^ 40 * 3679747 * 2
def baseEnd_3679747 : Nat := 1259652598626746471093105

theorem tailTrace_3679747 : CollatzResearch.WordTrace tailWord_3679747 prefixEnd_3679747 1259652598626746471093105 := by
  unfold tailWord_3679747
  simp only [CollatzResearch.WordTrace]
  refine ⟨134211398999912544599189495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89474265999941696399459663 134211398999912544599189495)
  ·
    refine ⟨201317098499868816898784243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134211398999912544599189495 201317098499868816898784243)
    ·
      refine ⟨301975647749803225348176365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201317098499868816898784243 301975647749803225348176365)
      ·
        refine ⟨113240867906176209505566137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301975647749803225348176365 113240867906176209505566137)
        ·
          refine ⟨84930650929632157129174603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113240867906176209505566137 84930650929632157129174603)
          ·
            refine ⟨127395976394448235693761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84930650929632157129174603 127395976394448235693761905)
            ·
              refine ⟨95546982295836176770321429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127395976394448235693761905 95546982295836176770321429)
              ·
                refine ⟨4478764795117320786108817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95546982295836176770321429 4478764795117320786108817)
                ·
                  refine ⟨3359073596337990589581613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4478764795117320786108817 3359073596337990589581613)
                  ·
                    refine ⟨1259652598626746471093105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359073596337990589581613 1259652598626746471093105)
                    ·
                      rfl

theorem cell22_3679747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].length) (baseStart_3679747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679747 prefixEnd_3679747 := by exact prefixLift 3679747
  have htrace : WordTrace (prefixWord ++ tailWord_3679747) baseStart_3679747 baseEnd_3679747 := by
    simpa [prefixWord, tailWord_3679747, baseEnd_3679747] using wordTrace_append hprefix tailTrace_3679747
  have hstable : (prefixWord ++ tailWord_3679747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679747).length < 2 ^ (prefixWord ++ tailWord_3679747).sum := by decide
  have hdescent : baseEnd_3679747 < baseStart_3679747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679777 : List Nat := [1, 2, 3, 2, 2, 2, 4, 6]
def baseStart_3679777 : Nat := 118140960795 + 3679777 * 2 ^ 59
def prefixEnd_3679777 : Nat := 4983230072969 + 3 ^ 40 * 3679777 * 2
def baseEnd_3679777 : Nat := 139962540915537376982557

theorem tailTrace_3679777 : CollatzResearch.WordTrace tailWord_3679777 prefixEnd_3679777 139962540915537376982557 := by
  unfold tailWord_3679777
  simp only [CollatzResearch.WordTrace]
  refine ⟨134212493189803859722781585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89474995459869239815187723 134212493189803859722781585)
  ·
    refine ⟨100659369892352894792086189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134212493189803859722781585 100659369892352894792086189)
    ·
      refine ⟨37747263709632335547032321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100659369892352894792086189 37747263709632335547032321)
      ·
        refine ⟨28310447782224251660274241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37747263709632335547032321 28310447782224251660274241)
        ·
          refine ⟨21232835836668188745205681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28310447782224251660274241 21232835836668188745205681)
          ·
            refine ⟨15924626877501141558904261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21232835836668188745205681 15924626877501141558904261)
            ·
              refine ⟨2985867539531464042294549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15924626877501141558904261 2985867539531464042294549)
              ·
                refine ⟨139962540915537376982557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2985867539531464042294549 139962540915537376982557)
                ·
                  rfl

theorem cell22_3679777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 6].length) (baseStart_3679777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679777 prefixEnd_3679777 := by exact prefixLift 3679777
  have htrace : WordTrace (prefixWord ++ tailWord_3679777) baseStart_3679777 baseEnd_3679777 := by
    simpa [prefixWord, tailWord_3679777, baseEnd_3679777] using wordTrace_append hprefix tailTrace_3679777
  have hstable : (prefixWord ++ tailWord_3679777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679777).length < 2 ^ (prefixWord ++ tailWord_3679777).sum := by decide
  have hdescent : baseEnd_3679777 < baseStart_3679777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679897 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_3679897 : Nat := 118140960795 + 3679897 * 2 ^ 59
def prefixEnd_3679897 : Nat := 4983230072969 + 3 ^ 40 * 3679897 * 2
def baseEnd_3679897 : Nat := 1259703946692196079842645

theorem tailTrace_3679897 : CollatzResearch.WordTrace tailWord_3679897 prefixEnd_3679897 1259703946692196079842645 := by
  unfold tailWord_3679897
  simp only [CollatzResearch.WordTrace]
  refine ⟨134216869949369120217149945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89477913299579413478099963 134216869949369120217149945)
  ·
    refine ⟨100662652462026840162862459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134216869949369120217149945 100662652462026840162862459)
    ·
      refine ⟨150993978693040260244293689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100662652462026840162862459 150993978693040260244293689)
      ·
        refine ⟨113245484019780195183220267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150993978693040260244293689 113245484019780195183220267)
        ·
          refine ⟨169868226029670292774830401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113245484019780195183220267 169868226029670292774830401)
          ·
            refine ⟨127401169522252719581122801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169868226029670292774830401 127401169522252719581122801)
            ·
              refine ⟨95550877141689539685842101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127401169522252719581122801 95550877141689539685842101)
              ·
                refine ⟨8957894732033394345547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95550877141689539685842101 8957894732033394345547697)
                ·
                  refine ⟨6718421049025045759160773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957894732033394345547697 6718421049025045759160773)
                  ·
                    refine ⟨1259703946692196079842645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718421049025045759160773 1259703946692196079842645)
                    ·
                      rfl

theorem cell22_3679897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_3679897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679897 prefixEnd_3679897 := by exact prefixLift 3679897
  have htrace : WordTrace (prefixWord ++ tailWord_3679897) baseStart_3679897 baseEnd_3679897 := by
    simpa [prefixWord, tailWord_3679897, baseEnd_3679897] using wordTrace_append hprefix tailTrace_3679897
  have hstable : (prefixWord ++ tailWord_3679897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679897).length < 2 ^ (prefixWord ++ tailWord_3679897).sum := by decide
  have hdescent : baseEnd_3679897 < baseStart_3679897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679944 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 3, 3]
def baseStart_3679944 : Nat := 118140960795 + 3679944 * 2 ^ 59
def prefixEnd_3679944 : Nat := 4983230072969 + 3 ^ 40 * 3679944 * 2
def baseEnd_3679944 : Nat := 1259720035752703623917501

theorem tailTrace_3679944 : CollatzResearch.WordTrace tailWord_3679944 prefixEnd_3679944 1259720035752703623917501 := by
  unfold tailWord_3679944
  simp only [CollatzResearch.WordTrace]
  refine ⟨67109292090099423622055443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89479056120132564829407257 67109292090099423622055443)
  ·
    refine ⟨100663938135149135433083165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67109292090099423622055443 100663938135149135433083165)
    ·
      refine ⟨37748976800680925787406187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100663938135149135433083165 37748976800680925787406187)
      ·
        refine ⟨56623465201021388681109281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748976800680925787406187 56623465201021388681109281)
        ·
          refine ⟨42467598900766041510831961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56623465201021388681109281 42467598900766041510831961)
          ·
            refine ⟨31850699175574531133123971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42467598900766041510831961 31850699175574531133123971)
            ·
              refine ⟨47776048763361796699685957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31850699175574531133123971 47776048763361796699685957)
              ·
                refine ⟨8958009143130336881191117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47776048763361796699685957 8958009143130336881191117)
                ·
                  refine ⟨3359253428673876330446669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8958009143130336881191117 3359253428673876330446669)
                  ·
                    refine ⟨1259720035752703623917501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359253428673876330446669 1259720035752703623917501)
                    ·
                      rfl

theorem cell22_3679944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_3679944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679944 prefixEnd_3679944 := by exact prefixLift 3679944
  have htrace : WordTrace (prefixWord ++ tailWord_3679944) baseStart_3679944 baseEnd_3679944 := by
    simpa [prefixWord, tailWord_3679944, baseEnd_3679944] using wordTrace_append hprefix tailTrace_3679944
  have hstable : (prefixWord ++ tailWord_3679944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679944).length < 2 ^ (prefixWord ++ tailWord_3679944).sum := by decide
  have hdescent : baseEnd_3679944 < baseStart_3679944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679946 : List Nat := [3, 1, 2, 1, 5, 2, 2, 6]
def baseStart_3679946 : Nat := 118140960795 + 3679946 * 2 ^ 59
def prefixEnd_3679946 : Nat := 4983230072969 + 3 ^ 40 * 3679946 * 2
def baseEnd_3679946 : Nat := 139968968932619587263055

theorem tailTrace_3679946 : CollatzResearch.WordTrace tailWord_3679946 prefixEnd_3679946 139968968932619587263055 := by
  unfold tailWord_3679946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33554664281547900396420923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89479104750794401057122461 33554664281547900396420923)
  ·
    refine ⟨50331996422321850594631385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33554664281547900396420923 50331996422321850594631385)
    ·
      refine ⟨37748997316741387945973539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50331996422321850594631385 37748997316741387945973539)
      ·
        refine ⟨56623495975112081918960309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748997316741387945973539 56623495975112081918960309)
        ·
          refine ⟨5308452747666757679902529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56623495975112081918960309 5308452747666757679902529)
          ·
            refine ⟨3981339560750068259926897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5308452747666757679902529 3981339560750068259926897)
            ·
              refine ⟨2986004670562551194945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981339560750068259926897 2986004670562551194945173)
              ·
                refine ⟨139968968932619587263055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2986004670562551194945173 139968968932619587263055)
                ·
                  rfl

theorem cell22_3679946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_3679946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3679946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3679946 prefixEnd_3679946 := by exact prefixLift 3679946
  have htrace : WordTrace (prefixWord ++ tailWord_3679946) baseStart_3679946 baseEnd_3679946 := by
    simpa [prefixWord, tailWord_3679946, baseEnd_3679946] using wordTrace_append hprefix tailTrace_3679946
  have hstable : (prefixWord ++ tailWord_3679946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679946).length < 2 ^ (prefixWord ++ tailWord_3679946).sum := by decide
  have hdescent : baseEnd_3679946 < baseStart_3679946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680034 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3680034 : Nat := 118140960795 + 3680034 * 2 ^ 59
def prefixEnd_3680034 : Nat := 4983230072969 + 3 ^ 40 * 3680034 * 2
def baseEnd_3680034 : Nat := 1259750844591973389167225

theorem tailTrace_3680034 : CollatzResearch.WordTrace tailWord_3680034 prefixEnd_3680034 1259750844591973389167225 := by
  unfold tailWord_3680034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555466687468198153721789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89481244499915195076591437 33555466687468198153721789)
  ·
    refine ⟨12583300007800574307645671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33555466687468198153721789 12583300007800574307645671)
    ·
      refine ⟨18874950011700861461468507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12583300007800574307645671 18874950011700861461468507)
      ·
        refine ⟨28312425017551292192202761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18874950011700861461468507 28312425017551292192202761)
        ·
          refine ⟨21234318763163469144152071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28312425017551292192202761 21234318763163469144152071)
          ·
            refine ⟨31851478144745203716228107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21234318763163469144152071 31851478144745203716228107)
            ·
              refine ⟨47777217217117805574342161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31851478144745203716228107 47777217217117805574342161)
              ·
                refine ⟨35832912912838354180756621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47777217217117805574342161 35832912912838354180756621)
                ·
                  refine ⟨13437342342314382817783733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35832912912838354180756621 13437342342314382817783733)
                  ·
                    refine ⟨1259750844591973389167225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437342342314382817783733 1259750844591973389167225)
                    ·
                      rfl

theorem cell22_3680034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3680034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680034 prefixEnd_3680034 := by exact prefixLift 3680034
  have htrace : WordTrace (prefixWord ++ tailWord_3680034) baseStart_3680034 baseEnd_3680034 := by
    simpa [prefixWord, tailWord_3680034, baseEnd_3680034] using wordTrace_append hprefix tailTrace_3680034
  have hstable : (prefixWord ++ tailWord_3680034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680034).length < 2 ^ (prefixWord ++ tailWord_3680034).sum := by decide
  have hdescent : baseEnd_3680034 < baseStart_3680034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680051 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_3680051 : Nat := 118140960795 + 3680051 * 2 ^ 59
def prefixEnd_3680051 : Nat := 4983230072969 + 3 ^ 40 * 3680051 * 2
def baseEnd_3680051 : Nat := 1259756664039391011492173

theorem tailTrace_3680051 : CollatzResearch.WordTrace tailWord_3680051 prefixEnd_3680051 1259756664039391011492173 := by
  unfold tailWord_3680051
  simp only [CollatzResearch.WordTrace]
  refine ⟨134222486790811204518256007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89481657860540803012170671 134222486790811204518256007)
  ·
    refine ⟨201333730186216806777384011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134222486790811204518256007 201333730186216806777384011)
    ·
      refine ⟨302000595279325210166076017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201333730186216806777384011 302000595279325210166076017)
      ·
        refine ⟨226500446459493907624557013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302000595279325210166076017 226500446459493907624557013)
        ·
          refine ⟨5308604213894388459950555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226500446459493907624557013 5308604213894388459950555)
          ·
            refine ⟨7962906320841582689925833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308604213894388459950555 7962906320841582689925833)
            ·
              refine ⟨5972179740631187017444375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962906320841582689925833 5972179740631187017444375)
              ·
                refine ⟨8958269610946780526166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972179740631187017444375 8958269610946780526166563)
                ·
                  refine ⟨13437404416420170789249845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958269610946780526166563 13437404416420170789249845)
                  ·
                    refine ⟨1259756664039391011492173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13437404416420170789249845 1259756664039391011492173)
                    ·
                      rfl

theorem cell22_3680051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_3680051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680051 prefixEnd_3680051 := by exact prefixLift 3680051
  have htrace : WordTrace (prefixWord ++ tailWord_3680051) baseStart_3680051 baseEnd_3680051 := by
    simpa [prefixWord, tailWord_3680051, baseEnd_3680051] using wordTrace_append hprefix tailTrace_3680051
  have hstable : (prefixWord ++ tailWord_3680051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680051).length < 2 ^ (prefixWord ++ tailWord_3680051).sum := by decide
  have hdescent : baseEnd_3680051 < baseStart_3680051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680070 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3680070 : Nat := 118140960795 + 3680070 * 2 ^ 59
def prefixEnd_3680070 : Nat := 4983230072969 + 3 ^ 40 * 3680070 * 2
def baseEnd_3680070 : Nat := 419921056042560431755705

theorem tailTrace_3680070 : CollatzResearch.WordTrace tailWord_3680070 prefixEnd_3680070 419921056042560431755705 := by
  unfold tailWord_3680070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194474368054449086349927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89482119851828247175465109 4194474368054449086349927)
  ·
    refine ⟨6291711552081673629524891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194474368054449086349927 6291711552081673629524891)
    ·
      refine ⟨9437567328122510444287337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291711552081673629524891 9437567328122510444287337)
      ·
        refine ⟨7078175496091882833215503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9437567328122510444287337 7078175496091882833215503)
        ·
          refine ⟨10617263244137824249823255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078175496091882833215503 10617263244137824249823255)
          ·
            refine ⟨15925894866206736374734883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10617263244137824249823255 15925894866206736374734883)
            ·
              refine ⟨23888842299310104562102325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15925894866206736374734883 23888842299310104562102325)
              ·
                refine ⟨2239578965560322302697093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23888842299310104562102325 2239578965560322302697093)
                ·
                  refine ⟨419921056042560431755705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239578965560322302697093 419921056042560431755705)
                  ·
                    rfl

theorem cell22_3680070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3680070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680070 prefixEnd_3680070 := by exact prefixLift 3680070
  have htrace : WordTrace (prefixWord ++ tailWord_3680070) baseStart_3680070 baseEnd_3680070 := by
    simpa [prefixWord, tailWord_3680070, baseEnd_3680070] using wordTrace_append hprefix tailTrace_3680070
  have hstable : (prefixWord ++ tailWord_3680070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680070).length < 2 ^ (prefixWord ++ tailWord_3680070).sum := by decide
  have hdescent : baseEnd_3680070 < baseStart_3680070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680096 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_3680096 : Nat := 118140960795 + 3680096 * 2 ^ 59
def prefixEnd_3680096 : Nat := 4983230072969 + 3 ^ 40 * 3680096 * 2
def baseEnd_3680096 : Nat := 1259772068459025894117035

theorem tailTrace_3680096 : CollatzResearch.WordTrace tailWord_3680096 prefixEnd_3680096 1259772068459025894117035 := by
  unfold tailWord_3680096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67112064037824088601822071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89482752050432118135762761 67112064037824088601822071)
  ·
    refine ⟨100668096056736132902733107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67112064037824088601822071 100668096056736132902733107)
    ·
      refine ⟨151002144085104199354099661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100668096056736132902733107 151002144085104199354099661)
      ·
        refine ⟨56625804031914074757787373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151002144085104199354099661 56625804031914074757787373)
        ·
          refine ⟨21234676511967778034170265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56625804031914074757787373 21234676511967778034170265)
          ·
            refine ⟨15926007383975833525627699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21234676511967778034170265 15926007383975833525627699)
            ·
              refine ⟨23889011075963750288441549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15926007383975833525627699 23889011075963750288441549)
              ·
                refine ⟨8958379153486406358165581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23889011075963750288441549 8958379153486406358165581)
                ·
                  refine ⟨3359392182557402384312093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8958379153486406358165581 3359392182557402384312093)
                  ·
                    refine ⟨1259772068459025894117035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359392182557402384312093 1259772068459025894117035)
                    ·
                      rfl

theorem cell22_3680096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_3680096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680096 prefixEnd_3680096 := by exact prefixLift 3680096
  have htrace : WordTrace (prefixWord ++ tailWord_3680096) baseStart_3680096 baseEnd_3680096 := by
    simpa [prefixWord, tailWord_3680096, baseEnd_3680096] using wordTrace_append hprefix tailTrace_3680096
  have hstable : (prefixWord ++ tailWord_3680096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680096).length < 2 ^ (prefixWord ++ tailWord_3680096).sum := by decide
  have hdescent : baseEnd_3680096 < baseStart_3680096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_3680139 : Nat := 118140960795 + 3680139 * 2 ^ 59
def prefixEnd_3680139 : Nat := 4983230072969 + 3 ^ 40 * 3680139 * 2
def baseEnd_3680139 : Nat := 1259786788237788115291903

theorem tailTrace_3680139 : CollatzResearch.WordTrace tailWord_3680139 prefixEnd_3680139 1259786788237788115291903 := by
  unfold tailWord_3680139
  simp only [CollatzResearch.WordTrace]
  refine ⟨134225696414492395547459471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89483797609661597031639647 134225696414492395547459471)
  ·
    refine ⟨201338544621738593321189207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134225696414492395547459471 201338544621738593321189207)
    ·
      refine ⟨302007816932607889981783811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201338544621738593321189207 302007816932607889981783811)
      ·
        refine ⟨453011725398911834972675717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302007816932607889981783811 453011725398911834972675717)
        ·
          refine ⟨84939698512295969057376697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453011725398911834972675717 84939698512295969057376697)
          ·
            refine ⟨63704773884221976793032523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84939698512295969057376697 63704773884221976793032523)
            ·
              refine ⟨95557160826332965189548785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63704773884221976793032523 95557160826332965189548785)
              ·
                refine ⟨71667870619749723892161589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95557160826332965189548785 71667870619749723892161589)
                ·
                  refine ⟨6718862870601536614890149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71667870619749723892161589 6718862870601536614890149)
                  ·
                    refine ⟨1259786788237788115291903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718862870601536614890149 1259786788237788115291903)
                    ·
                      rfl

theorem cell22_3680139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_3680139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680139 prefixEnd_3680139 := by exact prefixLift 3680139
  have htrace : WordTrace (prefixWord ++ tailWord_3680139) baseStart_3680139 baseEnd_3680139 := by
    simpa [prefixWord, tailWord_3680139, baseEnd_3680139] using wordTrace_append hprefix tailTrace_3680139
  have hstable : (prefixWord ++ tailWord_3680139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680139).length < 2 ^ (prefixWord ++ tailWord_3680139).sum := by decide
  have hdescent : baseEnd_3680139 < baseStart_3680139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680186 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_3680186 : Nat := 118140960795 + 3680186 * 2 ^ 59
def prefixEnd_3680186 : Nat := 4983230072969 + 3 ^ 40 * 3680186 * 2
def baseEnd_3680186 : Nat := 1259802877298295659366759

theorem tailTrace_3680186 : CollatzResearch.WordTrace tailWord_3680186 prefixEnd_3680186 1259802877298295659366759 := by
  unfold tailWord_3680186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33556852661330530643605103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89484940430214748382946941 33556852661330530643605103)
  ·
    refine ⟨50335278991995795965407655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33556852661330530643605103 50335278991995795965407655)
    ·
      refine ⟨75502918487993693948111483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50335278991995795965407655 75502918487993693948111483)
      ·
        refine ⟨113254377731990540922167225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75502918487993693948111483 113254377731990540922167225)
        ·
          refine ⟨84940783298992905691625419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113254377731990540922167225 84940783298992905691625419)
          ·
            refine ⟨127411174948489358537438129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84940783298992905691625419 127411174948489358537438129)
            ·
              refine ⟨95558381211367018903078597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127411174948489358537438129 95558381211367018903078597)
              ·
                refine ⟨17917196477131316044327237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95558381211367018903078597 17917196477131316044327237)
                ·
                  refine ⟨3359474339462121758311357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17917196477131316044327237 3359474339462121758311357)
                  ·
                    refine ⟨1259802877298295659366759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359474339462121758311357 1259802877298295659366759)
                    ·
                      rfl

theorem cell22_3680186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_3680186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680186 prefixEnd_3680186 := by exact prefixLift 3680186
  have htrace : WordTrace (prefixWord ++ tailWord_3680186) baseStart_3680186 baseEnd_3680186 := by
    simpa [prefixWord, tailWord_3680186, baseEnd_3680186] using wordTrace_append hprefix tailTrace_3680186
  have hstable : (prefixWord ++ tailWord_3680186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680186).length < 2 ^ (prefixWord ++ tailWord_3680186).sum := by decide
  have hdescent : baseEnd_3680186 < baseStart_3680186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680190 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3680190 : Nat := 118140960795 + 3680190 * 2 ^ 59
def prefixEnd_3680190 : Nat := 4983230072969 + 3 ^ 40 * 3680190 * 2
def baseEnd_3680190 : Nat := 1259804246580040982266747

theorem tailTrace_3680190 : CollatzResearch.WordTrace tailWord_3680190 prefixEnd_3680190 1259804246580040982266747 := by
  unfold tailWord_3680190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778444567163453907195753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89485037691538420838377349 16778444567163453907195753)
  ·
    refine ⟨12583833425372590430396815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16778444567163453907195753 12583833425372590430396815)
    ·
      refine ⟨18875750138058885645595223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12583833425372590430396815 18875750138058885645595223)
      ·
        refine ⟨28313625207088328468392835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18875750138058885645595223 28313625207088328468392835)
        ·
          refine ⟨42470437810632492702589253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28313625207088328468392835 42470437810632492702589253)
          ·
            refine ⟨7963207089493592381735485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42470437810632492702589253 7963207089493592381735485)
            ·
              refine ⟨2986202658560097143150807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7963207089493592381735485 2986202658560097143150807)
              ·
                refine ⟨4479303987840145714726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986202658560097143150807 4479303987840145714726211)
                ·
                  refine ⟨6718955981760218572089317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479303987840145714726211 6718955981760218572089317)
                  ·
                    refine ⟨1259804246580040982266747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6718955981760218572089317 1259804246580040982266747)
                    ·
                      rfl

theorem cell22_3680190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3680190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680190 prefixEnd_3680190 := by exact prefixLift 3680190
  have htrace : WordTrace (prefixWord ++ tailWord_3680190) baseStart_3680190 baseEnd_3680190 := by
    simpa [prefixWord, tailWord_3680190, baseEnd_3680190] using wordTrace_append hprefix tailTrace_3680190
  have hstable : (prefixWord ++ tailWord_3680190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680190).length < 2 ^ (prefixWord ++ tailWord_3680190).sum := by decide
  have hdescent : baseEnd_3680190 < baseStart_3680190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680203 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 2, 3]
def baseStart_3680203 : Nat := 118140960795 + 3680203 * 2 ^ 59
def prefixEnd_3680203 : Nat := 4983230072969 + 3 ^ 40 * 3680203 * 2
def baseEnd_3680203 : Nat := 1259808696745713281691707

theorem tailTrace_3680203 : CollatzResearch.WordTrace tailWord_3680203 prefixEnd_3680203 1259808696745713281691707 := by
  unfold tailWord_3680203
  simp only [CollatzResearch.WordTrace]
  refine ⟨134228030686260534477789263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89485353790840356318526175 134228030686260534477789263)
  ·
    refine ⟨201342046029390801716683895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134228030686260534477789263 201342046029390801716683895)
    ·
      refine ⟨302013069044086202575025843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201342046029390801716683895 302013069044086202575025843)
      ·
        refine ⟨453019603566129303862538765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302013069044086202575025843 453019603566129303862538765)
        ·
          refine ⟨169882351337298488948452037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453019603566129303862538765 169882351337298488948452037)
          ·
            refine ⟨31852940875743466677834757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169882351337298488948452037 31852940875743466677834757)
            ·
              refine ⟨5972426414201900002094017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31852940875743466677834757 5972426414201900002094017)
              ·
                refine ⟨4479319810651425001570513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5972426414201900002094017 4479319810651425001570513)
                ·
                  refine ⟨3359489857988568751177885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4479319810651425001570513 3359489857988568751177885)
                  ·
                    refine ⟨1259808696745713281691707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359489857988568751177885 1259808696745713281691707)
                    ·
                      rfl

theorem cell22_3680203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].length) (baseStart_3680203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680203 prefixEnd_3680203 := by exact prefixLift 3680203
  have htrace : WordTrace (prefixWord ++ tailWord_3680203) baseStart_3680203 baseEnd_3680203 := by
    simpa [prefixWord, tailWord_3680203, baseEnd_3680203] using wordTrace_append hprefix tailTrace_3680203
  have hstable : (prefixWord ++ tailWord_3680203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680203).length < 2 ^ (prefixWord ++ tailWord_3680203).sum := by decide
  have hdescent : baseEnd_3680203 < baseStart_3680203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680261 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 7]
def baseStart_3680261 : Nat := 118140960795 + 3680261 * 2 ^ 59
def prefixEnd_3680261 : Nat := 4983230072969 + 3 ^ 40 * 3680261 * 2
def baseEnd_3680261 : Nat := 419942850443673487913843

theorem tailTrace_3680261 : CollatzResearch.WordTrace tailWord_3680261 prefixEnd_3680261 419942850443673487913843 := by
  unfold tailWord_3680261
  simp only [CollatzResearch.WordTrace]
  refine ⟨134230146120050410383400637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89486764080033606922267091 134230146120050410383400637)
  ·
    refine ⟨50336304795018903893775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134230146120050410383400637 50336304795018903893775239)
    ·
      refine ⟨75504457192528355840662859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50336304795018903893775239 75504457192528355840662859)
      ·
        refine ⟨113256685788792533760994289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75504457192528355840662859 113256685788792533760994289)
        ·
          refine ⟨84942514341594400320745717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113256685788792533760994289 84942514341594400320745717)
          ·
            refine ⟨7963360719524475030069911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84942514341594400320745717 7963360719524475030069911)
            ·
              refine ⟨11945041079286712545104867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963360719524475030069911 11945041079286712545104867)
              ·
                refine ⟨17917561618930068817657301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945041079286712545104867 17917561618930068817657301)
                ·
                  refine ⟨419942850443673487913843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17917561618930068817657301 419942850443673487913843)
                  ·
                    rfl

theorem cell22_3680261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_3680261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680261 prefixEnd_3680261 := by exact prefixLift 3680261
  have htrace : WordTrace (prefixWord ++ tailWord_3680261) baseStart_3680261 baseEnd_3680261 := by
    simpa [prefixWord, tailWord_3680261, baseEnd_3680261] using wordTrace_append hprefix tailTrace_3680261
  have hstable : (prefixWord ++ tailWord_3680261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680261).length < 2 ^ (prefixWord ++ tailWord_3680261).sum := by decide
  have hdescent : baseEnd_3680261 < baseStart_3680261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680342 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3680342 : Nat := 118140960795 + 3680342 * 2 ^ 59
def prefixEnd_3680342 : Nat := 4983230072969 + 3 ^ 40 * 3680342 * 2
def baseEnd_3680342 : Nat := 1259856279286363252466281

theorem tailTrace_3680342 : CollatzResearch.WordTrace tailWord_3680342 prefixEnd_3680342 1259856279286363252466281 := by
  unfold tailWord_3680342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389568777047310076068705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89488733621837974144732853 8389568777047310076068705)
  ·
    refine ⟨6292176582785482557051529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8389568777047310076068705 6292176582785482557051529)
    ·
      refine ⟨4719132437089111917788647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6292176582785482557051529 4719132437089111917788647)
      ·
        refine ⟨7078698655633667876682971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719132437089111917788647 7078698655633667876682971)
        ·
          refine ⟨10618047983450501815024457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078698655633667876682971 10618047983450501815024457)
          ·
            refine ⟨7963535987587876361268343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618047983450501815024457 7963535987587876361268343)
            ·
              refine ⟨11945303981381814541902515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963535987587876361268343 11945303981381814541902515)
              ·
                refine ⟨17917955972072721812853773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945303981381814541902515 17917955972072721812853773)
                ·
                  refine ⟨6719233489527270679820165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17917955972072721812853773 6719233489527270679820165)
                  ·
                    refine ⟨1259856279286363252466281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719233489527270679820165 1259856279286363252466281)
                    ·
                      rfl

theorem cell22_3680342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3680342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680342 prefixEnd_3680342 := by exact prefixLift 3680342
  have htrace : WordTrace (prefixWord ++ tailWord_3680342) baseStart_3680342 baseEnd_3680342 := by
    simpa [prefixWord, tailWord_3680342, baseEnd_3680342] using wordTrace_append hprefix tailTrace_3680342
  have hstable : (prefixWord ++ tailWord_3680342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680342).length < 2 ^ (prefixWord ++ tailWord_3680342).sum := by decide
  have hdescent : baseEnd_3680342 < baseStart_3680342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680374 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3680374 : Nat := 118140960795 + 3680374 * 2 ^ 59
def prefixEnd_3680374 : Nat := 4983230072969 + 3 ^ 40 * 3680374 * 2
def baseEnd_3680374 : Nat := 419955744513441945222061

theorem tailTrace_3680374 : CollatzResearch.WordTrace tailWord_3680374 prefixEnd_3680374 419955744513441945222061 := by
  unfold tailWord_3680374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389641723040064417641511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89489511712427353788176117 8389641723040064417641511)
  ·
    refine ⟨12584462584560096626462267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8389641723040064417641511 12584462584560096626462267)
    ·
      refine ⟨18876693876840144939693401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12584462584560096626462267 18876693876840144939693401)
      ·
        refine ⟨14157520407630108704770051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18876693876840144939693401 14157520407630108704770051)
        ·
          refine ⟨21236280611445163057155077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157520407630108704770051 21236280611445163057155077)
          ·
            refine ⟨3981802614645968073216577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21236280611445163057155077 3981802614645968073216577)
            ·
              refine ⟨2986351960984476054912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981802614645968073216577 2986351960984476054912433)
              ·
                refine ⟨2239763970738357041184325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986351960984476054912433 2239763970738357041184325)
                ·
                  refine ⟨419955744513441945222061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239763970738357041184325 419955744513441945222061)
                  ·
                    rfl

theorem cell22_3680374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3680374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680374 prefixEnd_3680374 := by exact prefixLift 3680374
  have htrace : WordTrace (prefixWord ++ tailWord_3680374) baseStart_3680374 baseEnd_3680374 := by
    simpa [prefixWord, tailWord_3680374, baseEnd_3680374] using wordTrace_append hprefix tailTrace_3680374
  have hstable : (prefixWord ++ tailWord_3680374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680374).length < 2 ^ (prefixWord ++ tailWord_3680374).sum := by decide
  have hdescent : baseEnd_3680374 < baseStart_3680374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680385 : List Nat := [1, 2, 4, 2, 3, 2, 1, 7]
def baseStart_3680385 : Nat := 118140960795 + 3680385 * 2 ^ 59
def prefixEnd_3680385 : Nat := 4983230072969 + 3 ^ 40 * 3680385 * 2
def baseEnd_3680385 : Nat := 139985666562791719293461

theorem tailTrace_3680385 : CollatzResearch.WordTrace tailWord_3680385 prefixEnd_3680385 139985666562791719293461 := by
  unfold tailWord_3680385
  simp only [CollatzResearch.WordTrace]
  refine ⟨134234668771601179560914609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89489779181067453040609739 134234668771601179560914609)
  ·
    refine ⟨100676001578700884670685957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134234668771601179560914609 100676001578700884670685957)
    ·
      refine ⟨18876750296006415875753617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100676001578700884670685957 18876750296006415875753617)
      ·
        refine ⟨14157562722004811906815213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18876750296006415875753617 14157562722004811906815213)
        ·
          refine ⟨5309086020751804465055705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14157562722004811906815213 5309086020751804465055705)
          ·
            refine ⟨3981814515563853348791779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309086020751804465055705 3981814515563853348791779)
            ·
              refine ⟨5972721773345780023187669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981814515563853348791779 5972721773345780023187669)
              ·
                refine ⟨139985666562791719293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5972721773345780023187669 139985666562791719293461)
                ·
                  rfl

theorem cell22_3680385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 7].length) (baseStart_3680385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680385 prefixEnd_3680385 := by exact prefixLift 3680385
  have htrace : WordTrace (prefixWord ++ tailWord_3680385) baseStart_3680385 baseEnd_3680385 := by
    simpa [prefixWord, tailWord_3680385, baseEnd_3680385] using wordTrace_append hprefix tailTrace_3680385
  have hstable : (prefixWord ++ tailWord_3680385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680385).length < 2 ^ (prefixWord ++ tailWord_3680385).sum := by decide
  have hdescent : baseEnd_3680385 < baseStart_3680385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680396 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_3680396 : Nat := 118140960795 + 3680396 * 2 ^ 59
def prefixEnd_3680396 : Nat := 4983230072969 + 3 ^ 40 * 3680396 * 2
def baseEnd_3680396 : Nat := 419958254863308370538705

theorem tailTrace_3680396 : CollatzResearch.WordTrace tailWord_3680396 prefixEnd_3680396 419958254863308370538705 := by
  unfold tailWord_3680396
  simp only [CollatzResearch.WordTrace]
  refine ⟨67117534987280664219782521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89490046649707552293043361 67117534987280664219782521)
  ·
    refine ⟨50338151240460498164836891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67117534987280664219782521 50338151240460498164836891)
    ·
      refine ⟨75507226860690747247255337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50338151240460498164836891 75507226860690747247255337)
      ·
        refine ⟨56630420145518060435441503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75507226860690747247255337 56630420145518060435441503)
        ·
          refine ⟨84945630218277090653162255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56630420145518060435441503 84945630218277090653162255)
          ·
            refine ⟨127418445327415635979743383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84945630218277090653162255 127418445327415635979743383)
            ·
              refine ⟨191127667991123453969615075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127418445327415635979743383 191127667991123453969615075)
              ·
                refine ⟨286691501986685180954422613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191127667991123453969615075 286691501986685180954422613)
                ·
                  refine ⟨419958254863308370538705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 286691501986685180954422613 419958254863308370538705)
                  ·
                    rfl

theorem cell22_3680396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_3680396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680396 prefixEnd_3680396 := by exact prefixLift 3680396
  have htrace : WordTrace (prefixWord ++ tailWord_3680396) baseStart_3680396 baseEnd_3680396 := by
    simpa [prefixWord, tailWord_3680396, baseEnd_3680396] using wordTrace_append hprefix tailTrace_3680396
  have hstable : (prefixWord ++ tailWord_3680396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680396).length < 2 ^ (prefixWord ++ tailWord_3680396).sum := by decide
  have hdescent : baseEnd_3680396 < baseStart_3680396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680404 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3680404 : Nat := 118140960795 + 3680404 * 2 ^ 59
def prefixEnd_3680404 : Nat := 4983230072969 + 3 ^ 40 * 3680404 * 2
def baseEnd_3680404 : Nat := 1259877503153415757416091

theorem tailTrace_3680404 : CollatzResearch.WordTrace tailWord_3680404 prefixEnd_3680404 1259877503153415757416091 := by
  unfold tailWord_3680404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67117680879266172902928133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89490241172354897203904177 67117680879266172902928133)
  ·
    refine ⟨12584565164862407419299025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67117680879266172902928133 12584565164862407419299025)
    ·
      refine ⟨9438423873646805564474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12584565164862407419299025 9438423873646805564474269)
      ·
        refine ⟨3539408952617552086677851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9438423873646805564474269 3539408952617552086677851)
        ·
          refine ⟨5309113428926328130016777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539408952617552086677851 5309113428926328130016777)
          ·
            refine ⟨3981835071694746097512583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309113428926328130016777 3981835071694746097512583)
            ·
              refine ⟨5972752607542119146268875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981835071694746097512583 5972752607542119146268875)
              ·
                refine ⟨8959128911313178719403313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972752607542119146268875 8959128911313178719403313)
                ·
                  refine ⟨6719346683484884039552485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959128911313178719403313 6719346683484884039552485)
                  ·
                    refine ⟨1259877503153415757416091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719346683484884039552485 1259877503153415757416091)
                    ·
                      rfl

theorem cell22_3680404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3680404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680404 prefixEnd_3680404 := by exact prefixLift 3680404
  have htrace : WordTrace (prefixWord ++ tailWord_3680404) baseStart_3680404 baseEnd_3680404 := by
    simpa [prefixWord, tailWord_3680404, baseEnd_3680404] using wordTrace_append hprefix tailTrace_3680404
  have hstable : (prefixWord ++ tailWord_3680404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680404).length < 2 ^ (prefixWord ++ tailWord_3680404).sum := by decide
  have hdescent : baseEnd_3680404 < baseStart_3680404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680411 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_3680411 : Nat := 118140960795 + 3680411 * 2 ^ 59
def prefixEnd_3680411 : Nat := 4983230072969 + 3 ^ 40 * 3680411 * 2
def baseEnd_3680411 : Nat := 1259879899396470072491069

theorem tailTrace_3680411 : CollatzResearch.WordTrace tailWord_3680411 prefixEnd_3680411 1259879899396470072491069 := by
  unfold tailWord_3680411
  simp only [CollatzResearch.WordTrace]
  refine ⟨134235617069506986001361087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89490411379671324000907391 134235617069506986001361087)
  ·
    refine ⟨201353425604260479002041631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134235617069506986001361087 201353425604260479002041631)
    ·
      refine ⟨302030138406390718503062447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201353425604260479002041631 302030138406390718503062447)
      ·
        refine ⟨453045207609586077754593671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302030138406390718503062447 453045207609586077754593671)
        ·
          refine ⟨679567811414379116631890507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453045207609586077754593671 679567811414379116631890507)
          ·
            refine ⟨1019351717121568674947835761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679567811414379116631890507 1019351717121568674947835761)
            ·
              refine ⟨764513787841176506210876821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019351717121568674947835761 764513787841176506210876821)
              ·
                refine ⟨35836583805055148728634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 764513787841176506210876821 35836583805055148728634851)
                ·
                  refine ⟨53754875707582723092952277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35836583805055148728634851 53754875707582723092952277)
                  ·
                    refine ⟨1259879899396470072491069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53754875707582723092952277 1259879899396470072491069)
                    ·
                      rfl

theorem cell22_3680411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_3680411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680411 prefixEnd_3680411 := by exact prefixLift 3680411
  have htrace : WordTrace (prefixWord ++ tailWord_3680411) baseStart_3680411 baseEnd_3680411 := by
    simpa [prefixWord, tailWord_3680411, baseEnd_3680411] using wordTrace_append hprefix tailTrace_3680411
  have hstable : (prefixWord ++ tailWord_3680411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680411).length < 2 ^ (prefixWord ++ tailWord_3680411).sum := by decide
  have hdescent : baseEnd_3680411 < baseStart_3680411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680417 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3680417 : Nat := 118140960795 + 3680417 * 2 ^ 59
def prefixEnd_3680417 : Nat := 4983230072969 + 3 ^ 40 * 3680417 * 2
def baseEnd_3680417 : Nat := 1259881953319088056841051

theorem tailTrace_3680417 : CollatzResearch.WordTrace tailWord_3680417 prefixEnd_3680417 1259881953319088056841051 := by
  unfold tailWord_3680417
  simp only [CollatzResearch.WordTrace]
  refine ⟨134235835907485249026079505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89490557271656832684053003 134235835907485249026079505)
  ·
    refine ⟨100676876930613936769559629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134235835907485249026079505 100676876930613936769559629)
    ·
      refine ⟨37753828848980226288584861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100676876930613936769559629 37753828848980226288584861)
      ·
        refine ⟨14157685818367584858219323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37753828848980226288584861 14157685818367584858219323)
        ·
          refine ⟨21236528727551377287328985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157685818367584858219323 21236528727551377287328985)
          ·
            refine ⟨15927396545663532965496739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21236528727551377287328985 15927396545663532965496739)
            ·
              refine ⟨23891094818495299448245109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15927396545663532965496739 23891094818495299448245109)
              ·
                refine ⟨2239790139233934323272979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23891094818495299448245109 2239790139233934323272979)
                ·
                  refine ⟨3359685208850901484909469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239790139233934323272979 3359685208850901484909469)
                  ·
                    refine ⟨1259881953319088056841051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359685208850901484909469 1259881953319088056841051)
                    ·
                      rfl

theorem cell22_3680417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3680417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680417 prefixEnd_3680417 := by exact prefixLift 3680417
  have htrace : WordTrace (prefixWord ++ tailWord_3680417) baseStart_3680417 baseEnd_3680417 := by
    simpa [prefixWord, tailWord_3680417, baseEnd_3680417] using wordTrace_append hprefix tailTrace_3680417
  have hstable : (prefixWord ++ tailWord_3680417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680417).length < 2 ^ (prefixWord ++ tailWord_3680417).sum := by decide
  have hdescent : baseEnd_3680417 < baseStart_3680417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680458 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_3680458 : Nat := 118140960795 + 3680458 * 2 ^ 59
def prefixEnd_3680458 : Nat := 4983230072969 + 3 ^ 40 * 3680458 * 2
def baseEnd_3680458 : Nat := 419965329485659205521975

theorem tailTrace_3680458 : CollatzResearch.WordTrace tailWord_3680458 prefixEnd_3680458 419965329485659205521975 := by
  unfold tailWord_3680458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559332825084178257080507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89491554200224475352214685 33559332825084178257080507)
  ·
    refine ⟨50338999237626267385620761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33559332825084178257080507 50338999237626267385620761)
    ·
      refine ⟨37754249428219700539215571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50338999237626267385620761 37754249428219700539215571)
      ·
        refine ⟨56631374142329550808823357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37754249428219700539215571 56631374142329550808823357)
        ·
          refine ⟨21236765303373581553308759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56631374142329550808823357 21236765303373581553308759)
          ·
            refine ⟨31855147955060372329963139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21236765303373581553308759 31855147955060372329963139)
            ·
              refine ⟨47782721932590558494944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31855147955060372329963139 47782721932590558494944709)
              ·
                refine ⟨8959260362360729717802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47782721932590558494944709 8959260362360729717802133)
                ·
                  refine ⟨419965329485659205521975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8959260362360729717802133 419965329485659205521975)
                  ·
                    rfl

theorem cell22_3680458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_3680458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680458 prefixEnd_3680458 := by exact prefixLift 3680458
  have htrace : WordTrace (prefixWord ++ tailWord_3680458) baseStart_3680458 baseEnd_3680458 := by
    simpa [prefixWord, tailWord_3680458, baseEnd_3680458] using wordTrace_append hprefix tailTrace_3680458
  have hstable : (prefixWord ++ tailWord_3680458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680458).length < 2 ^ (prefixWord ++ tailWord_3680458).sum := by decide
  have hdescent : baseEnd_3680458 < baseStart_3680458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680473 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_3680473 : Nat := 118140960795 + 3680473 * 2 ^ 59
def prefixEnd_3680473 : Nat := 4983230072969 + 3 ^ 40 * 3680473 * 2
def baseEnd_3680473 : Nat := 1259901123263522577440879

theorem tailTrace_3680473 : CollatzResearch.WordTrace tailWord_3680473 prefixEnd_3680473 1259901123263522577440879 := by
  unfold tailWord_3680473
  simp only [CollatzResearch.WordTrace]
  refine ⟨134237878395282370590118073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89491918930188247060078715 134237878395282370590118073)
  ·
    refine ⟨100678408796461777942588555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134237878395282370590118073 100678408796461777942588555)
    ·
      refine ⟨151017613194692666913882833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100678408796461777942588555 151017613194692666913882833)
      ·
        refine ⟨113263209896019500185412125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151017613194692666913882833 113263209896019500185412125)
        ·
          refine ⟨42473703711007312569529547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113263209896019500185412125 42473703711007312569529547)
          ·
            refine ⟨63710555566510968854294321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42473703711007312569529547 63710555566510968854294321)
            ·
              refine ⟨47782916674883226640720741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63710555566510968854294321 47782916674883226640720741)
              ·
                refine ⟨8959296876540604995135139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47782916674883226640720741 8959296876540604995135139)
                ·
                  refine ⟨13438945314810907492702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959296876540604995135139 13438945314810907492702709)
                  ·
                    refine ⟨1259901123263522577440879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13438945314810907492702709 1259901123263522577440879)
                    ·
                      rfl

theorem cell22_3680473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_3680473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680473 prefixEnd_3680473 := by exact prefixLift 3680473
  have htrace : WordTrace (prefixWord ++ tailWord_3680473) baseStart_3680473 baseEnd_3680473 := by
    simpa [prefixWord, tailWord_3680473, baseEnd_3680473] using wordTrace_append hprefix tailTrace_3680473
  have hstable : (prefixWord ++ tailWord_3680473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680473).length < 2 ^ (prefixWord ++ tailWord_3680473).sum := by decide
  have hdescent : baseEnd_3680473 < baseStart_3680473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680477 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3680477 : Nat := 118140960795 + 3680477 * 2 ^ 59
def prefixEnd_3680477 : Nat := 4983230072969 + 3 ^ 40 * 3680477 * 2
def baseEnd_3680477 : Nat := 1259902492545267900340867

theorem tailTrace_3680477 : CollatzResearch.WordTrace tailWord_3680477 prefixEnd_3680477 1259902492545267900340867 := by
  unfold tailWord_3680477
  simp only [CollatzResearch.WordTrace]
  refine ⟨134238024287267879273263685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89492016191511919515509123 134238024287267879273263685)
  ·
    refine ⟨25169629553862727363736941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134238024287267879273263685 25169629553862727363736941)
    ·
      refine ⟨9438611082698522761401353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25169629553862727363736941 9438611082698522761401353)
      ·
        refine ⟨7078958312023892071051015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438611082698522761401353 7078958312023892071051015)
        ·
          refine ⟨10618437468035838106576523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078958312023892071051015 10618437468035838106576523)
          ·
            refine ⟨15927656202053757159864785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10618437468035838106576523 15927656202053757159864785)
            ·
              refine ⟨11945742151540317869898589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15927656202053757159864785 11945742151540317869898589)
              ·
                refine ⟨4479653306827619201211971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11945742151540317869898589 4479653306827619201211971)
                ·
                  refine ⟨6719479960241428801817957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479653306827619201211971 6719479960241428801817957)
                  ·
                    refine ⟨1259902492545267900340867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719479960241428801817957 1259902492545267900340867)
                    ·
                      rfl

theorem cell22_3680477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3680477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680477 prefixEnd_3680477 := by exact prefixLift 3680477
  have htrace : WordTrace (prefixWord ++ tailWord_3680477) baseStart_3680477 baseEnd_3680477 := by
    simpa [prefixWord, tailWord_3680477, baseEnd_3680477] using wordTrace_append hprefix tailTrace_3680477
  have hstable : (prefixWord ++ tailWord_3680477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680477).length < 2 ^ (prefixWord ++ tailWord_3680477).sum := by decide
  have hdescent : baseEnd_3680477 < baseStart_3680477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680490 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3680490 : Nat := 118140960795 + 3680490 * 2 ^ 59
def prefixEnd_3680490 : Nat := 4983230072969 + 3 ^ 40 * 3680490 * 2
def baseEnd_3680490 : Nat := 1259906942710940199765827

theorem tailTrace_3680490 : CollatzResearch.WordTrace tailWord_3680490 prefixEnd_3680490 1259906942710940199765827 := by
  unfold tailWord_3680490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559624609055195623371731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89492332290813854995657949 33559624609055195623371731)
  ·
    refine ⟨50339436913582793435057597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33559624609055195623371731 50339436913582793435057597)
    ·
      refine ⟨18877288842593547538146599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50339436913582793435057597 18877288842593547538146599)
      ·
        refine ⟨28315933263890321307219899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877288842593547538146599 28315933263890321307219899)
        ·
          refine ⟨42473899895835481960829849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315933263890321307219899 42473899895835481960829849)
          ·
            refine ⟨31855424921876611470622387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42473899895835481960829849 31855424921876611470622387)
            ·
              refine ⟨47783137382814917205933581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31855424921876611470622387 47783137382814917205933581)
              ·
                refine ⟨17918676518555593952225093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47783137382814917205933581 17918676518555593952225093)
                ·
                  refine ⟨3359751847229173866042205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17918676518555593952225093 3359751847229173866042205)
                  ·
                    refine ⟨1259906942710940199765827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359751847229173866042205 1259906942710940199765827)
                    ·
                      rfl

theorem cell22_3680490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3680490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680490 prefixEnd_3680490 := by exact prefixLift 3680490
  have htrace : WordTrace (prefixWord ++ tailWord_3680490) baseStart_3680490 baseEnd_3680490 := by
    simpa [prefixWord, tailWord_3680490, baseEnd_3680490] using wordTrace_append hprefix tailTrace_3680490
  have hstable : (prefixWord ++ tailWord_3680490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680490).length < 2 ^ (prefixWord ++ tailWord_3680490).sum := by decide
  have hdescent : baseEnd_3680490 < baseStart_3680490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680492 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_3680492 : Nat := 118140960795 + 3680492 * 2 ^ 59
def prefixEnd_3680492 : Nat := 4983230072969 + 3 ^ 40 * 3680492 * 2
def baseEnd_3680492 : Nat := 419969209117270953738607

theorem tailTrace_3680492 : CollatzResearch.WordTrace tailWord_3680492 prefixEnd_3680492 419969209117270953738607 := by
  unfold tailWord_3680492
  simp only [CollatzResearch.WordTrace]
  refine ⟨67119285691106768417529865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89492380921475691223373153 67119285691106768417529865)
  ·
    refine ⟨50339464268330076313147399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67119285691106768417529865 50339464268330076313147399)
    ·
      refine ⟨75509196402495114469721099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50339464268330076313147399 75509196402495114469721099)
      ·
        refine ⟨113263794603742671704581649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75509196402495114469721099 113263794603742671704581649)
        ·
          refine ⟨84947845952807003778436237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113263794603742671704581649 84947845952807003778436237)
          ·
            refine ⟨31855442232302626416913589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84947845952807003778436237 31855442232302626416913589)
            ·
              refine ⟨2986447709278371226585649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31855442232302626416913589 2986447709278371226585649)
              ·
                refine ⟨2239835781958778419939237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986447709278371226585649 2239835781958778419939237)
                ·
                  refine ⟨419969209117270953738607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2239835781958778419939237 419969209117270953738607)
                  ·
                    rfl

theorem cell22_3680492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_3680492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680492 prefixEnd_3680492 := by exact prefixLift 3680492
  have htrace : WordTrace (prefixWord ++ tailWord_3680492) baseStart_3680492 baseEnd_3680492 := by
    simpa [prefixWord, tailWord_3680492, baseEnd_3680492] using wordTrace_append hprefix tailTrace_3680492
  have hstable : (prefixWord ++ tailWord_3680492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680492).length < 2 ^ (prefixWord ++ tailWord_3680492).sum := by decide
  have hdescent : baseEnd_3680492 < baseStart_3680492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680554 : List Nat := [3, 1, 4, 2, 3, 1, 1, 7]
def baseStart_3680554 : Nat := 118140960795 + 3680554 * 2 ^ 59
def prefixEnd_3680554 : Nat := 4983230072969 + 3 ^ 40 * 3680554 * 2
def baseEnd_3680554 : Nat := 139992094579873929573959

theorem tailTrace_3680554 : CollatzResearch.WordTrace tailWord_3680554 prefixEnd_3680554 139992094579873929573959 := by
  unfold tailWord_3680554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33560208176997230355954179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89493888471992614282544477 33560208176997230355954179)
  ·
    refine ⟨50340312265495845533931269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33560208176997230355954179 50340312265495845533931269)
    ·
      refine ⟨9438808549780471037612113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50340312265495845533931269 9438808549780471037612113)
      ·
        refine ⟨7079106412335353278209085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438808549780471037612113 7079106412335353278209085)
        ·
          refine ⟨2654664904625757479328407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7079106412335353278209085 2654664904625757479328407)
          ·
            refine ⟨3981997356938636218992611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654664904625757479328407 3981997356938636218992611)
            ·
              refine ⟨5972996035407954328488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981997356938636218992611 5972996035407954328488917)
              ·
                refine ⟨139992094579873929573959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5972996035407954328488917 139992094579873929573959)
                ·
                  rfl

theorem cell22_3680554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_3680554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680554 prefixEnd_3680554 := by exact prefixLift 3680554
  have htrace : WordTrace (prefixWord ++ tailWord_3680554) baseStart_3680554 baseEnd_3680554 := by
    simpa [prefixWord, tailWord_3680554, baseEnd_3680554] using wordTrace_append hprefix tailTrace_3680554
  have hstable : (prefixWord ++ tailWord_3680554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680554).length < 2 ^ (prefixWord ++ tailWord_3680554).sum := by decide
  have hdescent : baseEnd_3680554 < baseStart_3680554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680565 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3680565 : Nat := 118140960795 + 3680565 * 2 ^ 59
def prefixEnd_3680565 : Nat := 4983230072969 + 3 ^ 40 * 3680565 * 2
def baseEnd_3680565 : Nat := 419977538914555001380199

theorem tailTrace_3680565 : CollatzResearch.WordTrace tailWord_3680565 prefixEnd_3680565 419977538914555001380199 := by
  unfold tailWord_3680565
  simp only [CollatzResearch.WordTrace]
  refine ⟨134241233910949070302467149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89494155940632713534978099 134241233910949070302467149)
  ·
    refine ⟨50340462716605901363425181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134241233910949070302467149 50340462716605901363425181)
    ·
      refine ⟨18877673518727213011284443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50340462716605901363425181 18877673518727213011284443)
      ·
        refine ⟨28316510278090819516926665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877673518727213011284443 28316510278090819516926665)
        ·
          refine ⟨21237382708568114637694999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28316510278090819516926665 21237382708568114637694999)
          ·
            refine ⟨31856074062852171956542499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237382708568114637694999 31856074062852171956542499)
            ·
              refine ⟨47784111094278257934813749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31856074062852171956542499 47784111094278257934813749)
              ·
                refine ⟨4479760415088586681388789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47784111094278257934813749 4479760415088586681388789)
                ·
                  refine ⟨419977538914555001380199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4479760415088586681388789 419977538914555001380199)
                  ·
                    rfl

theorem cell22_3680565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3680565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680565 prefixEnd_3680565 := by exact prefixLift 3680565
  have htrace : WordTrace (prefixWord ++ tailWord_3680565) baseStart_3680565 baseEnd_3680565 := by
    simpa [prefixWord, tailWord_3680565, baseEnd_3680565] using wordTrace_append hprefix tailTrace_3680565
  have hstable : (prefixWord ++ tailWord_3680565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680565).length < 2 ^ (prefixWord ++ tailWord_3680565).sum := by decide
  have hdescent : baseEnd_3680565 < baseStart_3680565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680629 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3680629 : Nat := 118140960795 + 3680629 * 2 ^ 59
def prefixEnd_3680629 : Nat := 4983230072969 + 3 ^ 40 * 3680629 * 2
def baseEnd_3680629 : Nat := 1259954525251590170540401

theorem tailTrace_3680629 : CollatzResearch.WordTrace tailWord_3680629 prefixEnd_3680629 1259954525251590170540401 := by
  unfold tailWord_3680629
  simp only [CollatzResearch.WordTrace]
  refine ⟨134243568182717209232796941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89495712121811472821864627 134243568182717209232796941)
  ·
    refine ⟨50341338068518953462298853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134243568182717209232796941 50341338068518953462298853)
    ·
      refine ⟨9439000887847303774181035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50341338068518953462298853 9439000887847303774181035)
      ·
        refine ⟨14158501331770955661271553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439000887847303774181035 14158501331770955661271553)
        ·
          refine ⟨10618875998828216745953665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14158501331770955661271553 10618875998828216745953665)
          ·
            refine ⟨7964156999121162559465249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618875998828216745953665 7964156999121162559465249)
            ·
              refine ⟨5973117749340871919598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964156999121162559465249 5973117749340871919598937)
              ·
                refine ⟨4479838312005653939699203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973117749340871919598937 4479838312005653939699203)
                ·
                  refine ⟨6719757468008480909548805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479838312005653939699203 6719757468008480909548805)
                  ·
                    refine ⟨1259954525251590170540401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719757468008480909548805 1259954525251590170540401)
                    ·
                      rfl

theorem cell22_3680629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3680629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680629 prefixEnd_3680629 := by exact prefixLift 3680629
  have htrace : WordTrace (prefixWord ++ tailWord_3680629) baseStart_3680629 baseEnd_3680629 := by
    simpa [prefixWord, tailWord_3680629, baseEnd_3680629] using wordTrace_append hprefix tailTrace_3680629
  have hstable : (prefixWord ++ tailWord_3680629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680629).length < 2 ^ (prefixWord ++ tailWord_3680629).sum := by decide
  have hdescent : baseEnd_3680629 < baseStart_3680629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680704 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_3680704 : Nat := 118140960795 + 3680704 * 2 ^ 59
def prefixEnd_3680704 : Nat := 4983230072969 + 3 ^ 40 * 3680704 * 2
def baseEnd_3680704 : Nat := 1259980199284314974915171

theorem tailTrace_3680704 : CollatzResearch.WordTrace tailWord_3680704 prefixEnd_3680704 1259980199284314974915171 := by
  unfold tailWord_3680704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123151828722748520888583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89497535771630331361184777 67123151828722748520888583)
  ·
    refine ⟨100684727743084122781332875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67123151828722748520888583 100684727743084122781332875)
    ·
      refine ⟨151027091614626184171999313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100684727743084122781332875 151027091614626184171999313)
      ·
        refine ⟨113270318710969638128999485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151027091614626184171999313 113270318710969638128999485)
        ·
          refine ⟨42476369516613614298374807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113270318710969638128999485 42476369516613614298374807)
          ·
            refine ⟨63714554274920421447562211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42476369516613614298374807 63714554274920421447562211)
            ·
              refine ⟨95571831412380632171343317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63714554274920421447562211 95571831412380632171343317)
              ·
                refine ⟨2239964798727671066515859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95571831412380632171343317 2239964798727671066515859)
                ·
                  refine ⟨3359947198091506599773789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239964798727671066515859 3359947198091506599773789)
                  ·
                    refine ⟨1259980199284314974915171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359947198091506599773789 1259980199284314974915171)
                    ·
                      rfl

theorem cell22_3680704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_3680704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680704 prefixEnd_3680704 := by exact prefixLift 3680704
  have htrace : WordTrace (prefixWord ++ tailWord_3680704) baseStart_3680704 baseEnd_3680704 := by
    simpa [prefixWord, tailWord_3680704, baseEnd_3680704] using wordTrace_append hprefix tailTrace_3680704
  have hstable : (prefixWord ++ tailWord_3680704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680704).length < 2 ^ (prefixWord ++ tailWord_3680704).sum := by decide
  have hdescent : baseEnd_3680704 < baseStart_3680704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680715 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_3680715 : Nat := 118140960795 + 3680715 * 2 ^ 59
def prefixEnd_3680715 : Nat := 4983230072969 + 3 ^ 40 * 3680715 * 2
def baseEnd_3680715 : Nat := 1259983964809114612890137

theorem tailTrace_3680715 : CollatzResearch.WordTrace tailWord_3680715 prefixEnd_3680715 1259983964809114612890137 := by
  unfold tailWord_3680715
  simp only [CollatzResearch.WordTrace]
  refine ⟨134246704860405645920427599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89497803240270430613618399 134246704860405645920427599)
  ·
    refine ⟨201370057290608468880641399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134246704860405645920427599 201370057290608468880641399)
    ·
      refine ⟨302055085935912703320962099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201370057290608468880641399 302055085935912703320962099)
      ·
        refine ⟨453082628903869054981443149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302055085935912703320962099 453082628903869054981443149)
        ·
          refine ⟨169905985838950895618041181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453082628903869054981443149 169905985838950895618041181)
          ·
            refine ⟨63714744689606585856765443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169905985838950895618041181 63714744689606585856765443)
            ·
              refine ⟨95572117034409878785148165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63714744689606585856765443 95572117034409878785148165)
              ·
                refine ⟨17919771943951852272215281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95572117034409878785148165 17919771943951852272215281)
                ·
                  refine ⟨13439828957963889204161461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17919771943951852272215281 13439828957963889204161461)
                  ·
                    refine ⟨1259983964809114612890137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13439828957963889204161461 1259983964809114612890137)
                    ·
                      rfl

theorem cell22_3680715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_3680715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680715 prefixEnd_3680715 := by exact prefixLift 3680715
  have htrace : WordTrace (prefixWord ++ tailWord_3680715) baseStart_3680715 baseEnd_3680715 := by
    simpa [prefixWord, tailWord_3680715, baseEnd_3680715] using wordTrace_append hprefix tailTrace_3680715
  have hstable : (prefixWord ++ tailWord_3680715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680715).length < 2 ^ (prefixWord ++ tailWord_3680715).sum := by decide
  have hdescent : baseEnd_3680715 < baseStart_3680715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680738 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3680738 : Nat := 118140960795 + 3680738 * 2 ^ 59
def prefixEnd_3680738 : Nat := 4983230072969 + 3 ^ 40 * 3680738 * 2
def baseEnd_3680738 : Nat := 1259991838179150219565067

theorem tailTrace_3680738 : CollatzResearch.WordTrace tailWord_3680738 prefixEnd_3680738 1259991838179150219565067 := by
  unfold tailWord_3680738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33561885934830580212128717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89498362492881547232343245 33561885934830580212128717)
  ·
    refine ⟨12585707225561467579548269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33561885934830580212128717 12585707225561467579548269)
    ·
      refine ⟨4719640209585550342330601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12585707225561467579548269 4719640209585550342330601)
      ·
        refine ⟨3539730157189162756747951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719640209585550342330601 3539730157189162756747951)
        ·
          refine ⟨5309595235783744135121927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539730157189162756747951 5309595235783744135121927)
          ·
            refine ⟨7964392853675616202682891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309595235783744135121927 7964392853675616202682891)
            ·
              refine ⟨11946589280513424304024337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964392853675616202682891 11946589280513424304024337)
              ·
                refine ⟨8959941960385068228018253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11946589280513424304024337 8959941960385068228018253)
                ·
                  refine ⟨3359978235144400585506845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8959941960385068228018253 3359978235144400585506845)
                  ·
                    refine ⟨1259991838179150219565067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359978235144400585506845 1259991838179150219565067)
                    ·
                      rfl

theorem cell22_3680738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3680738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680738 prefixEnd_3680738 := by exact prefixLift 3680738
  have htrace : WordTrace (prefixWord ++ tailWord_3680738) baseStart_3680738 baseEnd_3680738 := by
    simpa [prefixWord, tailWord_3680738, baseEnd_3680738] using wordTrace_append hprefix tailTrace_3680738
  have hstable : (prefixWord ++ tailWord_3680738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680738).length < 2 ^ (prefixWord ++ tailWord_3680738).sum := by decide
  have hdescent : baseEnd_3680738 < baseStart_3680738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680747 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 1, 4]
def baseStart_3680747 : Nat := 118140960795 + 3680747 * 2 ^ 59
def prefixEnd_3680747 : Nat := 4983230072969 + 3 ^ 40 * 3680747 * 2
def baseEnd_3680747 : Nat := 1259994919063077196090039

theorem tailTrace_3680747 : CollatzResearch.WordTrace tailWord_3680747 prefixEnd_3680747 1259994919063077196090039 := by
  unfold tailWord_3680747
  simp only [CollatzResearch.WordTrace]
  refine ⟨134247871996289715385592495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89498581330859810257061663 134247871996289715385592495)
  ·
    refine ⟨201371807994434573078388743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134247871996289715385592495 201371807994434573078388743)
    ·
      refine ⟨302057711991651859617583115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201371807994434573078388743 302057711991651859617583115)
      ·
        refine ⟨453086567987477789426374673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302057711991651859617583115 453086567987477789426374673)
        ·
          refine ⟨339814925990608342069781005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453086567987477789426374673 339814925990608342069781005)
          ·
            refine ⟨127430597246478128276167877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339814925990608342069781005 127430597246478128276167877)
            ·
              refine ⟨23893236983714649051781477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127430597246478128276167877 23893236983714649051781477)
              ·
                refine ⟨4479981934446496697209027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23893236983714649051781477 4479981934446496697209027)
                ·
                  refine ⟨6719972901669745045813541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479981934446496697209027 6719972901669745045813541)
                  ·
                    refine ⟨1259994919063077196090039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6719972901669745045813541 1259994919063077196090039)
                    ·
                      rfl

theorem cell22_3680747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_3680747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680747 prefixEnd_3680747 := by exact prefixLift 3680747
  have htrace : WordTrace (prefixWord ++ tailWord_3680747) baseStart_3680747 baseEnd_3680747 := by
    simpa [prefixWord, tailWord_3680747, baseEnd_3680747] using wordTrace_append hprefix tailTrace_3680747
  have hstable : (prefixWord ++ tailWord_3680747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680747).length < 2 ^ (prefixWord ++ tailWord_3680747).sum := by decide
  have hdescent : baseEnd_3680747 < baseStart_3680747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680779 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 4]
def baseStart_3680779 : Nat := 118140960795 + 3680779 * 2 ^ 59
def prefixEnd_3680779 : Nat := 4983230072969 + 3 ^ 40 * 3680779 * 2
def baseEnd_3680779 : Nat := 420001957772346593096647

theorem tailTrace_3680779 : CollatzResearch.WordTrace tailWord_3680779 prefixEnd_3680779 420001957772346593096647 := by
  unfold tailWord_3680779
  simp only [CollatzResearch.WordTrace]
  refine ⟨134249039132173784850757391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89499359421449189900504927 134249039132173784850757391)
  ·
    refine ⟨201373558698260677276136087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134249039132173784850757391 201373558698260677276136087)
    ·
      refine ⟨302060338047391015914204131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201373558698260677276136087 302060338047391015914204131)
      ·
        refine ⟨453090507071086523871306197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302060338047391015914204131 453090507071086523871306197)
        ·
          refine ⟨10619308759478590403233739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 453090507071086523871306197 10619308759478590403233739)
          ·
            refine ⟨15928963139217885604850609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619308759478590403233739 15928963139217885604850609)
            ·
              refine ⟨11946722354413414203637957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15928963139217885604850609 11946722354413414203637957)
              ·
                refine ⟨2240010441452515163182117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11946722354413414203637957 2240010441452515163182117)
                ·
                  refine ⟨420001957772346593096647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240010441452515163182117 420001957772346593096647)
                  ·
                    rfl

theorem cell22_3680779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 4].length) (baseStart_3680779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680779 prefixEnd_3680779 := by exact prefixLift 3680779
  have htrace : WordTrace (prefixWord ++ tailWord_3680779) baseStart_3680779 baseEnd_3680779 := by
    simpa [prefixWord, tailWord_3680779, baseEnd_3680779] using wordTrace_append hprefix tailTrace_3680779
  have hstable : (prefixWord ++ tailWord_3680779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680779).length < 2 ^ (prefixWord ++ tailWord_3680779).sum := by decide
  have hdescent : baseEnd_3680779 < baseStart_3680779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680792 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_3680792 : Nat := 118140960795 + 3680792 * 2 ^ 59
def prefixEnd_3680792 : Nat := 4983230072969 + 3 ^ 40 * 3680792 * 2
def baseEnd_3680792 : Nat := 1260010323482712078714901

theorem tailTrace_3680792 : CollatzResearch.WordTrace tailWord_3680792 prefixEnd_3680792 1260010323482712078714901 := by
  unfold tailWord_3680792
  simp only [CollatzResearch.WordTrace]
  refine ⟨67124756640563344035490315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89499675520751125380653753 67124756640563344035490315)
  ·
    refine ⟨100687134960845016053235473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67124756640563344035490315 100687134960845016053235473)
    ·
      refine ⟨75515351220633762039926605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100687134960845016053235473 75515351220633762039926605)
      ·
        refine ⟨28318256707737660764972477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75515351220633762039926605 28318256707737660764972477)
        ·
          refine ⟨10619346265401622786864679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28318256707737660764972477 10619346265401622786864679)
          ·
            refine ⟨15929019398102434180297019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619346265401622786864679 15929019398102434180297019)
            ·
              refine ⟨23893529097153651270445529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929019398102434180297019 23893529097153651270445529)
              ·
                refine ⟨17920146822865238452834147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23893529097153651270445529 17920146822865238452834147)
                ·
                  refine ⟨26880220234297857679251221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17920146822865238452834147 26880220234297857679251221)
                  ·
                    refine ⟨1260010323482712078714901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26880220234297857679251221 1260010323482712078714901)
                    ·
                      rfl

theorem cell22_3680792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_3680792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680792 prefixEnd_3680792 := by exact prefixLift 3680792
  have htrace : WordTrace (prefixWord ++ tailWord_3680792) baseStart_3680792 baseEnd_3680792 := by
    simpa [prefixWord, tailWord_3680792, baseEnd_3680792] using wordTrace_append hprefix tailTrace_3680792
  have hstable : (prefixWord ++ tailWord_3680792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680792).length < 2 ^ (prefixWord ++ tailWord_3680792).sum := by decide
  have hdescent : baseEnd_3680792 < baseStart_3680792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680794 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_3680794 : Nat := 118140960795 + 3680794 * 2 ^ 59
def prefixEnd_3680794 : Nat := 4983230072969 + 3 ^ 40 * 3680794 * 2
def baseEnd_3680794 : Nat := 1260011008123584740164895

theorem tailTrace_3680794 : CollatzResearch.WordTrace tailWord_3680794 prefixEnd_3680794 1260011008123584740164895 := by
  unfold tailWord_3680794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33562396556779860603138359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89499724151412961608368957 33562396556779860603138359)
  ·
    refine ⟨50343594835169790904707539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33562396556779860603138359 50343594835169790904707539)
    ·
      refine ⟨75515392252754686357061309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50343594835169790904707539 75515392252754686357061309)
      ·
        refine ⟨28318272094783007383897991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75515392252754686357061309 28318272094783007383897991)
        ·
          refine ⟨42477408142174511075846987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28318272094783007383897991 42477408142174511075846987)
          ·
            refine ⟨63716112213261766613770481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42477408142174511075846987 63716112213261766613770481)
            ·
              refine ⟨47787084159946324960327861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63716112213261766613770481 47787084159946324960327861)
              ·
                refine ⟨4480039139994967965030737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47787084159946324960327861 4480039139994967965030737)
                ·
                  refine ⟨3360029354996225973773053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480039139994967965030737 3360029354996225973773053)
                  ·
                    refine ⟨1260011008123584740164895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3360029354996225973773053 1260011008123584740164895)
                    ·
                      rfl

theorem cell22_3680794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_3680794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680794 prefixEnd_3680794 := by exact prefixLift 3680794
  have htrace : WordTrace (prefixWord ++ tailWord_3680794) baseStart_3680794 baseEnd_3680794 := by
    simpa [prefixWord, tailWord_3680794, baseEnd_3680794] using wordTrace_append hprefix tailTrace_3680794
  have hstable : (prefixWord ++ tailWord_3680794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680794).length < 2 ^ (prefixWord ++ tailWord_3680794).sum := by decide
  have hdescent : baseEnd_3680794 < baseStart_3680794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680830 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3680830 : Nat := 118140960795 + 3680830 * 2 ^ 59
def prefixEnd_3680830 : Nat := 4983230072969 + 3 ^ 40 * 3680830 * 2
def baseEnd_3680830 : Nat := 420007777219764215421595

theorem tailTrace_3680830 : CollatzResearch.WordTrace tailWord_3680830 prefixEnd_3680830 420007777219764215421595 := by
  unfold tailWord_3680830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781362406873627570107993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89500599503326013707242629 16781362406873627570107993)
  ·
    refine ⟨12586021805155220677580995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16781362406873627570107993 12586021805155220677580995)
    ·
      refine ⟨18879032707732831016371493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586021805155220677580995 18879032707732831016371493)
      ·
        refine ⟨3539818632699905815569655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18879032707732831016371493 3539818632699905815569655)
        ·
          refine ⟨5309727949049858723354483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539818632699905815569655 5309727949049858723354483)
          ·
            refine ⟨7964591923574788085031725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309727949049858723354483 7964591923574788085031725)
            ·
              refine ⟨2986721971340545531886897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7964591923574788085031725 2986721971340545531886897)
              ·
                refine ⟨2240041478505409148915173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986721971340545531886897 2240041478505409148915173)
                ·
                  refine ⟨420007777219764215421595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240041478505409148915173 420007777219764215421595)
                  ·
                    rfl

theorem cell22_3680830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3680830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680830 prefixEnd_3680830 := by exact prefixLift 3680830
  have htrace : WordTrace (prefixWord ++ tailWord_3680830) baseStart_3680830 baseEnd_3680830 := by
    simpa [prefixWord, tailWord_3680830, baseEnd_3680830] using wordTrace_append hprefix tailTrace_3680830
  have hstable : (prefixWord ++ tailWord_3680830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680830).length < 2 ^ (prefixWord ++ tailWord_3680830).sum := by decide
  have hdescent : baseEnd_3680830 < baseStart_3680830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680845 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3680845 : Nat := 118140960795 + 3680845 * 2 ^ 59
def prefixEnd_3680845 : Nat := 4983230072969 + 3 ^ 40 * 3680845 * 2
def baseEnd_3680845 : Nat := 1260028466465837607139739

theorem tailTrace_3680845 : CollatzResearch.WordTrace tailWord_3680845 prefixEnd_3680845 1260028466465837607139739 := by
  unfold tailWord_3680845
  simp only [CollatzResearch.WordTrace]
  refine ⟨134251446349934678122659989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89500964233289785415106659 134251446349934678122659989)
  ·
    refine ⟨6293036547653188036999687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134251446349934678122659989 6293036547653188036999687)
    ·
      refine ⟨9439554821479782055499531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6293036547653188036999687 9439554821479782055499531)
      ·
        refine ⟨14159332232219673083249297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439554821479782055499531 14159332232219673083249297)
        ·
          refine ⟨10619499174164754812436973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14159332232219673083249297 10619499174164754812436973)
          ·
            refine ⟨3982312190311783054663865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10619499174164754812436973 3982312190311783054663865)
            ·
              refine ⟨2986734142733837290997899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982312190311783054663865 2986734142733837290997899)
              ·
                refine ⟨4480101214100755936496849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986734142733837290997899 4480101214100755936496849)
                ·
                  refine ⟨3360075910575566952372637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480101214100755936496849 3360075910575566952372637)
                  ·
                    refine ⟨1260028466465837607139739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3360075910575566952372637 1260028466465837607139739)
                    ·
                      rfl

theorem cell22_3680845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3680845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680845 prefixEnd_3680845 := by exact prefixLift 3680845
  have htrace : WordTrace (prefixWord ++ tailWord_3680845) baseStart_3680845 baseEnd_3680845 := by
    simpa [prefixWord, tailWord_3680845, baseEnd_3680845] using wordTrace_append hprefix tailTrace_3680845
  have hstable : (prefixWord ++ tailWord_3680845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680845).length < 2 ^ (prefixWord ++ tailWord_3680845).sum := by decide
  have hdescent : baseEnd_3680845 < baseStart_3680845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680914 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3680914 : Nat := 118140960795 + 3680914 * 2 ^ 59
def prefixEnd_3680914 : Nat := 4983230072969 + 3 ^ 40 * 3680914 * 2
def baseEnd_3680914 : Nat := 420017362191981475721509

theorem tailTrace_3680914 : CollatzResearch.WordTrace tailWord_3680914 prefixEnd_3680914 420017362191981475721509 := by
  unfold tailWord_3680914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563490746671175726730449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89502641991123135271281197 33563490746671175726730449)
  ·
    refine ⟨25172618060003381795047837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33563490746671175726730449 25172618060003381795047837)
    ·
      refine ⟨9439731772501268173142939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25172618060003381795047837 9439731772501268173142939)
      ·
        refine ⟨14159597658751902259714409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439731772501268173142939 14159597658751902259714409)
        ·
          refine ⟨10619698244063926694785807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14159597658751902259714409 10619698244063926694785807)
          ·
            refine ⟨15929547366095890042178711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619698244063926694785807 15929547366095890042178711)
            ·
              refine ⟨23894321049143835063268067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929547366095890042178711 23894321049143835063268067)
              ·
                refine ⟨35841481573715752594902101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23894321049143835063268067 35841481573715752594902101)
                ·
                  refine ⟨420017362191981475721509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35841481573715752594902101 420017362191981475721509)
                  ·
                    rfl

theorem cell22_3680914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3680914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680914 prefixEnd_3680914 := by exact prefixLift 3680914
  have htrace : WordTrace (prefixWord ++ tailWord_3680914) baseStart_3680914 baseEnd_3680914 := by
    simpa [prefixWord, tailWord_3680914, baseEnd_3680914] using wordTrace_append hprefix tailTrace_3680914
  have hstable : (prefixWord ++ tailWord_3680914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680914).length < 2 ^ (prefixWord ++ tailWord_3680914).sum := by decide
  have hdescent : baseEnd_3680914 < baseStart_3680914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680916 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3680916 : Nat := 118140960795 + 3680916 * 2 ^ 59
def prefixEnd_3680916 : Nat := 4983230072969 + 3 ^ 40 * 3680916 * 2
def baseEnd_3680916 : Nat := 1260052771216817088614521

theorem tailTrace_3680916 : CollatzResearch.WordTrace tailWord_3680916 prefixEnd_3680916 1260052771216817088614521 := by
  unfold tailWord_3680916
  simp only [CollatzResearch.WordTrace]
  refine ⟨67127017966338728624247301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89502690621784971498996401 67127017966338728624247301)
  ·
    refine ⟨12586315868688511617046369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67127017966338728624247301 12586315868688511617046369)
    ·
      refine ⟨9439736901516383712784777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12586315868688511617046369 9439736901516383712784777)
      ·
        refine ⟨7079802676137287784588583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9439736901516383712784777 7079802676137287784588583)
        ·
          refine ⟨10619704014205931676882875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7079802676137287784588583 10619704014205931676882875)
          ·
            refine ⟨15929556021308897515324313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619704014205931676882875 15929556021308897515324313)
            ·
              refine ⟨11947167015981673136493235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15929556021308897515324313 11947167015981673136493235)
              ·
                refine ⟨17920750523972509704739853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11947167015981673136493235 17920750523972509704739853)
                ·
                  refine ⟨6720281446489691139277445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17920750523972509704739853 6720281446489691139277445)
                  ·
                    refine ⟨1260052771216817088614521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720281446489691139277445 1260052771216817088614521)
                    ·
                      rfl

theorem cell22_3680916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3680916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3680916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3680916 prefixEnd_3680916 := by exact prefixLift 3680916
  have htrace : WordTrace (prefixWord ++ tailWord_3680916) baseStart_3680916 baseEnd_3680916 := by
    simpa [prefixWord, tailWord_3680916, baseEnd_3680916] using wordTrace_append hprefix tailTrace_3680916
  have hstable : (prefixWord ++ tailWord_3680916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680916).length < 2 ^ (prefixWord ++ tailWord_3680916).sum := by decide
  have hdescent : baseEnd_3680916 < baseStart_3680916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681004 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_3681004 : Nat := 118140960795 + 3681004 * 2 ^ 59
def prefixEnd_3681004 : Nat := 4983230072969 + 3 ^ 40 * 3681004 * 2
def baseEnd_3681004 : Nat := 420027631805071397471417

theorem tailTrace_3681004 : CollatzResearch.WordTrace tailWord_3681004 prefixEnd_3681004 420027631805071397471417 := by
  unfold tailWord_3681004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67128622778179324138849033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89504830370905765518465377 67128622778179324138849033)
  ·
    refine ⟨50346467083634493104136775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67128622778179324138849033 50346467083634493104136775)
    ·
      refine ⟨75519700625451739656205163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50346467083634493104136775 75519700625451739656205163)
      ·
        refine ⟨113279550938177609484307745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75519700625451739656205163 113279550938177609484307745)
        ·
          refine ⟨84959663203633207113230809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113279550938177609484307745 84959663203633207113230809)
          ·
            refine ⟨63719747402724905334923107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84959663203633207113230809 63719747402724905334923107)
            ·
              refine ⟨95579621104087358002384661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63719747402724905334923107 95579621104087358002384661)
              ·
                refine ⟨4480294739254094906361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95579621104087358002384661 4480294739254094906361781)
                ·
                  refine ⟨420027631805071397471417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4480294739254094906361781 420027631805071397471417)
                  ·
                    rfl

theorem cell22_3681004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_3681004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681004 prefixEnd_3681004 := by exact prefixLift 3681004
  have htrace : WordTrace (prefixWord ++ tailWord_3681004) baseStart_3681004 baseEnd_3681004 := by
    simpa [prefixWord, tailWord_3681004, baseEnd_3681004] using wordTrace_append hprefix tailTrace_3681004
  have hstable : (prefixWord ++ tailWord_3681004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681004).length < 2 ^ (prefixWord ++ tailWord_3681004).sum := by decide
  have hdescent : baseEnd_3681004 < baseStart_3681004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681079 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3681079 : Nat := 118140960795 + 3681079 * 2 ^ 59
def prefixEnd_3681079 : Nat := 4983230072969 + 3 ^ 40 * 3681079 * 2
def baseEnd_3681079 : Nat := 1260108569447938996789021

theorem tailTrace_3681079 : CollatzResearch.WordTrace tailWord_3681079 prefixEnd_3681079 1260108569447938996789021 := by
  unfold tailWord_3681079
  simp only [CollatzResearch.WordTrace]
  refine ⟨134259981031086936086678291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89506654020724624057785527 134259981031086936086678291)
  ·
    refine ⟨201389971546630404130017437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134259981031086936086678291 201389971546630404130017437)
    ·
      refine ⟨75521239329986401548756539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201389971546630404130017437 75521239329986401548756539)
      ·
        refine ⟨113281858994979602323134809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75521239329986401548756539 113281858994979602323134809)
        ·
          refine ⟨84961394246234701742351107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113281858994979602323134809 84961394246234701742351107)
          ·
            refine ⟨127442091369352052613526661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84961394246234701742351107 127442091369352052613526661)
            ·
              refine ⟨23895392131753509865036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127442091369352052613526661 23895392131753509865036249)
              ·
                refine ⟨17921544098815132398777187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23895392131753509865036249 17921544098815132398777187)
                ·
                  refine ⟨26882316148222698598165781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17921544098815132398777187 26882316148222698598165781)
                  ·
                    refine ⟨1260108569447938996789021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26882316148222698598165781 1260108569447938996789021)
                    ·
                      rfl

theorem cell22_3681079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3681079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681079 prefixEnd_3681079 := by exact prefixLift 3681079
  have htrace : WordTrace (prefixWord ++ tailWord_3681079) baseStart_3681079 baseEnd_3681079 := by
    simpa [prefixWord, tailWord_3681079, baseEnd_3681079] using wordTrace_append hprefix tailTrace_3681079
  have hstable : (prefixWord ++ tailWord_3681079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681079).length < 2 ^ (prefixWord ++ tailWord_3681079).sum := by decide
  have hdescent : baseEnd_3681079 < baseStart_3681079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681216 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_3681216 : Nat := 118140960795 + 3681216 * 2 ^ 59
def prefixEnd_3681216 : Nat := 4983230072969 + 3 ^ 40 * 3681216 * 2
def baseEnd_3681216 : Nat := 1260155467347716306113601

theorem tailTrace_3681216 : CollatzResearch.WordTrace tailWord_3681216 prefixEnd_3681216 1260155467347716306113601 := by
  unfold tailWord_3681216
  simp only [CollatzResearch.WordTrace]
  refine ⟨67132488915795304242207751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89509985221060405656277001 67132488915795304242207751)
  ·
    refine ⟨100698733373692956363311627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67132488915795304242207751 100698733373692956363311627)
    ·
      refine ⟨151048100060539434544967441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100698733373692956363311627 151048100060539434544967441)
      ·
        refine ⟨113286075045404575908725581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151048100060539434544967441 113286075045404575908725581)
        ·
          refine ⟨42482278142026715965772093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113286075045404575908725581 42482278142026715965772093)
          ·
            refine ⟨15930854303260018487164535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42482278142026715965772093 15930854303260018487164535)
            ·
              refine ⟨23896281454890027730746803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930854303260018487164535 23896281454890027730746803)
              ·
                refine ⟨35844422182335041596120205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23896281454890027730746803 35844422182335041596120205)
                ·
                  refine ⟨13441658318375640598545077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35844422182335041596120205 13441658318375640598545077)
                  ·
                    refine ⟨1260155467347716306113601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13441658318375640598545077 1260155467347716306113601)
                    ·
                      rfl

theorem cell22_3681216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_3681216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681216 prefixEnd_3681216 := by exact prefixLift 3681216
  have htrace : WordTrace (prefixWord ++ tailWord_3681216) baseStart_3681216 baseEnd_3681216 := by
    simpa [prefixWord, tailWord_3681216, baseEnd_3681216] using wordTrace_append hprefix tailTrace_3681216
  have hstable : (prefixWord ++ tailWord_3681216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681216).length < 2 ^ (prefixWord ++ tailWord_3681216).sum := by decide
  have hdescent : baseEnd_3681216 < baseStart_3681216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681250 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3681250 : Nat := 118140960795 + 3681250 * 2 ^ 59
def prefixEnd_3681250 : Nat := 4983230072969 + 3 ^ 40 * 3681250 * 2
def baseEnd_3681250 : Nat := 1260167106242551550763497

theorem tailTrace_3681250 : CollatzResearch.WordTrace tailWord_3681250 prefixEnd_3681250 1260167106242551550763497 := by
  unfold tailWord_3681250
  simp only [CollatzResearch.WordTrace]
  refine ⟨33566554478366858072788301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89510811942311621527435469 33566554478366858072788301)
  ·
    refine ⟨12587457929387571777295613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33566554478366858072788301 12587457929387571777295613)
    ·
      refine ⟨4720296723520339416485855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12587457929387571777295613 4720296723520339416485855)
      ·
        refine ⟨7080445085280509124728783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720296723520339416485855 7080445085280509124728783)
        ·
          refine ⟨10620667627920763687093175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080445085280509124728783 10620667627920763687093175)
          ·
            refine ⟨15931001441881145530639763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620667627920763687093175 15931001441881145530639763)
            ·
              refine ⟨23896502162821718295959645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15931001441881145530639763 23896502162821718295959645)
              ·
                refine ⟨8961188311058144360984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23896502162821718295959645 8961188311058144360984867)
                ·
                  refine ⟨13441782466587216541477301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961188311058144360984867 13441782466587216541477301)
                  ·
                    refine ⟨1260167106242551550763497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13441782466587216541477301 1260167106242551550763497)
                    ·
                      rfl

theorem cell22_3681250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3681250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681250 prefixEnd_3681250 := by exact prefixLift 3681250
  have htrace : WordTrace (prefixWord ++ tailWord_3681250) baseStart_3681250 baseEnd_3681250 := by
    simpa [prefixWord, tailWord_3681250, baseEnd_3681250] using wordTrace_append hprefix tailTrace_3681250
  have hstable : (prefixWord ++ tailWord_3681250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681250).length < 2 ^ (prefixWord ++ tailWord_3681250).sum := by decide
  have hdescent : baseEnd_3681250 < baseStart_3681250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681263 : List Nat := [1, 1, 2, 1, 4, 4, 3, 6]
def baseStart_3681263 : Nat := 118140960795 + 3681263 * 2 ^ 59
def prefixEnd_3681263 : Nat := 4983230072969 + 3 ^ 40 * 3681263 * 2
def baseEnd_3681263 : Nat := 140019061823135983354273

theorem tailTrace_3681263 : CollatzResearch.WordTrace tailWord_3681263 prefixEnd_3681263 140019061823135983354273 := by
  unfold tailWord_3681263
  simp only [CollatzResearch.WordTrace]
  refine ⟨134266692062420335511376443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89511128041613557007584295 134266692062420335511376443)
  ·
    refine ⟨201400038093630503267064665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134266692062420335511376443 201400038093630503267064665)
    ·
      refine ⟨151050028570222877450298499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201400038093630503267064665 151050028570222877450298499)
      ·
        refine ⟨226575042855334316175447749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151050028570222877450298499 226575042855334316175447749)
        ·
          refine ⟨42482820535375184282896453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226575042855334316175447749 42482820535375184282896453)
          ·
            refine ⟨7965528850382847053043085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42482820535375184282896453 7965528850382847053043085)
            ·
              refine ⟨2987073318893567644891157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7965528850382847053043085 2987073318893567644891157)
              ·
                refine ⟨140019061823135983354273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2987073318893567644891157 140019061823135983354273)
                ·
                  rfl

theorem cell22_3681263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 6].length) (baseStart_3681263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681263 prefixEnd_3681263 := by exact prefixLift 3681263
  have htrace : WordTrace (prefixWord ++ tailWord_3681263) baseStart_3681263 baseEnd_3681263 := by
    simpa [prefixWord, tailWord_3681263, baseEnd_3681263] using wordTrace_append hprefix tailTrace_3681263
  have hstable : (prefixWord ++ tailWord_3681263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681263).length < 2 ^ (prefixWord ++ tailWord_3681263).sum := by decide
  have hdescent : baseEnd_3681263 < baseStart_3681263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681265 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_3681265 : Nat := 118140960795 + 3681265 * 2 ^ 59
def prefixEnd_3681265 : Nat := 4983230072969 + 3 ^ 40 * 3681265 * 2
def baseEnd_3681265 : Nat := 1260172241049096511638451

theorem tailTrace_3681265 : CollatzResearch.WordTrace tailWord_3681265 prefixEnd_3681265 1260172241049096511638451 := by
  unfold tailWord_3681265
  simp only [CollatzResearch.WordTrace]
  refine ⟨134266765008413089852949249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89511176672275393235299499 134266765008413089852949249)
  ·
    refine ⟨100700073756309817389711937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134266765008413089852949249 100700073756309817389711937)
    ·
      refine ⟨75525055317232363042283953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100700073756309817389711937 75525055317232363042283953)
      ·
        refine ⟨56643791487924272281712965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75525055317232363042283953 56643791487924272281712965)
        ·
          refine ⟨10620710903985801052821181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56643791487924272281712965 10620710903985801052821181)
          ·
            refine ⟨3982766588994675394807943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10620710903985801052821181 3982766588994675394807943)
            ·
              refine ⟨5974149883492013092211915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982766588994675394807943 5974149883492013092211915)
              ·
                refine ⟨8961224825238019638317873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974149883492013092211915 8961224825238019638317873)
                ·
                  refine ⟨6720918618928514728738405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961224825238019638317873 6720918618928514728738405)
                  ·
                    refine ⟨1260172241049096511638451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720918618928514728738405 1260172241049096511638451)
                    ·
                      rfl

theorem cell22_3681265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_3681265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681265 prefixEnd_3681265 := by exact prefixLift 3681265
  have htrace : WordTrace (prefixWord ++ tailWord_3681265) baseStart_3681265 baseEnd_3681265 := by
    simpa [prefixWord, tailWord_3681265, baseEnd_3681265] using wordTrace_append hprefix tailTrace_3681265
  have hstable : (prefixWord ++ tailWord_3681265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681265).length < 2 ^ (prefixWord ++ tailWord_3681265).sum := by decide
  have hdescent : baseEnd_3681265 < baseStart_3681265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681269 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 4]
def baseStart_3681269 : Nat := 118140960795 + 3681269 * 2 ^ 59
def prefixEnd_3681269 : Nat := 4983230072969 + 3 ^ 40 * 3681269 * 2
def baseEnd_3681269 : Nat := 420057870110280611512813

theorem tailTrace_3681269 : CollatzResearch.WordTrace tailWord_3681269 prefixEnd_3681269 420057870110280611512813 := by
  unfold tailWord_3681269
  simp only [CollatzResearch.WordTrace]
  refine ⟨134266910900398598536094861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89511273933599065690729907 134266910900398598536094861)
  ·
    refine ⟨50350091587649474451035573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134266910900398598536094861 50350091587649474451035573)
    ·
      refine ⟨4720321086342138229784585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50350091587649474451035573 4720321086342138229784585)
      ·
        refine ⟨3540240814756603672338439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4720321086342138229784585 3540240814756603672338439)
        ·
          refine ⟨5310361222134905508507659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540240814756603672338439 5310361222134905508507659)
          ·
            refine ⟨7965541833202358262761489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310361222134905508507659 7965541833202358262761489)
            ·
              refine ⟨5974156374901768697071117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965541833202358262761489 5974156374901768697071117)
              ·
                refine ⟨2240308640588163261401669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5974156374901768697071117 2240308640588163261401669)
                ·
                  refine ⟨420057870110280611512813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240308640588163261401669 420057870110280611512813)
                  ·
                    rfl

theorem cell22_3681269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_3681269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681269 prefixEnd_3681269 := by exact prefixLift 3681269
  have htrace : WordTrace (prefixWord ++ tailWord_3681269) baseStart_3681269 baseEnd_3681269 := by
    simpa [prefixWord, tailWord_3681269, baseEnd_3681269] using wordTrace_append hprefix tailTrace_3681269
  have hstable : (prefixWord ++ tailWord_3681269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681269).length < 2 ^ (prefixWord ++ tailWord_3681269).sum := by decide
  have hdescent : baseEnd_3681269 < baseStart_3681269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681368 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_3681368 : Nat := 118140960795 + 3681368 * 2 ^ 59
def prefixEnd_3681368 : Nat := 4983230072969 + 3 ^ 40 * 3681368 * 2
def baseEnd_3681368 : Nat := 1260207500054038576313135

theorem tailTrace_3681368 : CollatzResearch.WordTrace tailWord_3681368 prefixEnd_3681368 1260207500054038576313135 := by
  unfold tailWord_3681368
  simp only [CollatzResearch.WordTrace]
  refine ⟨67135260863519969221974379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89513681151359958962632505 67135260863519969221974379)
  ·
    refine ⟨100702891295279953832961569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67135260863519969221974379 100702891295279953832961569)
    ·
      refine ⟨75527168471459965374721177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100702891295279953832961569 75527168471459965374721177)
      ·
        refine ⟨56645376353594974031040883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75527168471459965374721177 56645376353594974031040883)
        ·
          refine ⟨84968064530392461046561325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56645376353594974031040883 84968064530392461046561325)
          ·
            refine ⟨31863024198897172892460497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84968064530392461046561325 31863024198897172892460497)
            ·
              refine ⟨23897268149172879669345373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31863024198897172892460497 23897268149172879669345373)
              ·
                refine ⟨8961475555939829876004515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23897268149172879669345373 8961475555939829876004515)
                ·
                  refine ⟨13442213333909744814006773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961475555939829876004515 13442213333909744814006773)
                  ·
                    refine ⟨1260207500054038576313135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13442213333909744814006773 1260207500054038576313135)
                    ·
                      rfl

theorem cell22_3681368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_3681368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681368 prefixEnd_3681368 := by exact prefixLift 3681368
  have htrace : WordTrace (prefixWord ++ tailWord_3681368) baseStart_3681368 baseEnd_3681368 := by
    simpa [prefixWord, tailWord_3681368, baseEnd_3681368] using wordTrace_append hprefix tailTrace_3681368
  have hstable : (prefixWord ++ tailWord_3681368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681368).length < 2 ^ (prefixWord ++ tailWord_3681368).sum := by decide
  have hdescent : baseEnd_3681368 < baseStart_3681368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681550 : List Nat := [4, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3681550 : Nat := 118140960795 + 3681550 * 2 ^ 59
def prefixEnd_3681550 : Nat := 4983230072969 + 3 ^ 40 * 3681550 * 2
def baseEnd_3681550 : Nat := 140029978041494529806953

theorem tailTrace_3681550 : CollatzResearch.WordTrace tailWord_3681550 prefixEnd_3681550 140029978041494529806953 := by
  unfold tailWord_3681550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784644976547572940884263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89518106541587055684716069 16784644976547572940884263)
  ·
    refine ⟨25176967464821359411326395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784644976547572940884263 25176967464821359411326395)
    ·
      refine ⟨37765451197232039116989593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25176967464821359411326395 37765451197232039116989593)
      ·
        refine ⟨28324088397924029337742195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37765451197232039116989593 28324088397924029337742195)
        ·
          refine ⟨42486132596886044006613293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28324088397924029337742195 42486132596886044006613293)
          ·
            refine ⟨15932299723832266502479985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42486132596886044006613293 15932299723832266502479985)
            ·
              refine ⟨11949224792874199876859989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15932299723832266502479985 11949224792874199876859989)
              ·
                refine ⟨140029978041494529806953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11949224792874199876859989 140029978041494529806953)
                ·
                  rfl

theorem cell22_3681550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3681550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681550 prefixEnd_3681550 := by exact prefixLift 3681550
  have htrace : WordTrace (prefixWord ++ tailWord_3681550) baseStart_3681550 baseEnd_3681550 := by
    simpa [prefixWord, tailWord_3681550, baseEnd_3681550] using wordTrace_append hprefix tailTrace_3681550
  have hstable : (prefixWord ++ tailWord_3681550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681550).length < 2 ^ (prefixWord ++ tailWord_3681550).sum := by decide
  have hdescent : baseEnd_3681550 < baseStart_3681550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681622 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3681622 : Nat := 118140960795 + 3681622 * 2 ^ 59
def prefixEnd_3681622 : Nat := 4983230072969 + 3 ^ 40 * 3681622 * 2
def baseEnd_3681622 : Nat := 1260294449444866580462357

theorem tailTrace_3681622 : CollatzResearch.WordTrace tailWord_3681622 prefixEnd_3681622 1260294449444866580462357 := by
  unfold tailWord_3681622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392486616757483738980945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89519857245413159882463413 8392486616757483738980945)
  ·
    refine ⟨6294364962568112804235709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8392486616757483738980945 6294364962568112804235709)
    ·
      refine ⟨2360386860963042301588391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6294364962568112804235709 2360386860963042301588391)
      ·
        refine ⟨3540580291444563452382587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360386860963042301588391 3540580291444563452382587)
        ·
          refine ⟨5310870437166845178573881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540580291444563452382587 5310870437166845178573881)
          ·
            refine ⟨3983152827875133883930411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310870437166845178573881 3983152827875133883930411)
            ·
              refine ⟨5974729241812700825895617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983152827875133883930411 5974729241812700825895617)
              ·
                refine ⟨4481046931359525619421713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974729241812700825895617 4481046931359525619421713)
                ·
                  refine ⟨3360785198519644214566285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4481046931359525619421713 3360785198519644214566285)
                  ·
                    refine ⟨1260294449444866580462357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3360785198519644214566285 1260294449444866580462357)
                    ·
                      rfl

theorem cell22_3681622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3681622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681622 prefixEnd_3681622 := by exact prefixLift 3681622
  have htrace : WordTrace (prefixWord ++ tailWord_3681622) baseStart_3681622 baseEnd_3681622 := by
    simpa [prefixWord, tailWord_3681622, baseEnd_3681622] using wordTrace_append hprefix tailTrace_3681622
  have hstable : (prefixWord ++ tailWord_3681622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681622).length < 2 ^ (prefixWord ++ tailWord_3681622).sum := by decide
  have hdescent : baseEnd_3681622 < baseStart_3681622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681685 : List Nat := [1, 3, 2, 1, 1, 2, 12]
def baseStart_3681685 : Nat := 118140960795 + 3681685 * 2 ^ 59
def prefixEnd_3681685 : Nat := 4983230072969 + 3 ^ 40 * 3681685 * 2
def baseEnd_3681685 : Nat := 46678370949346496893969

theorem tailTrace_3681685 : CollatzResearch.WordTrace tailWord_3681685 prefixEnd_3681685 46678370949346496893969 := by
  unfold tailWord_3681685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134282083666891501583238509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89521389111261001055492339 134282083666891501583238509)
  ·
    refine ⟨50355781375084313093714441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134282083666891501583238509 50355781375084313093714441)
    ·
      refine ⟨37766836031313234820285831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50355781375084313093714441 37766836031313234820285831)
      ·
        refine ⟨56650254046969852230428747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37766836031313234820285831 56650254046969852230428747)
        ·
          refine ⟨84975381070454778345643121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56650254046969852230428747 84975381070454778345643121)
          ·
            refine ⟨63731535802841083759232341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84975381070454778345643121 63731535802841083759232341)
            ·
              refine ⟨46678370949346496893969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63731535802841083759232341 46678370949346496893969)
              ·
                rfl

theorem cell22_3681685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 12].length) (baseStart_3681685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681685 prefixEnd_3681685 := by exact prefixLift 3681685
  have htrace : WordTrace (prefixWord ++ tailWord_3681685) baseStart_3681685 baseEnd_3681685 := by
    simpa [prefixWord, tailWord_3681685, baseEnd_3681685] using wordTrace_append hprefix tailTrace_3681685
  have hstable : (prefixWord ++ tailWord_3681685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681685).length < 2 ^ (prefixWord ++ tailWord_3681685).sum := by decide
  have hdescent : baseEnd_3681685 < baseStart_3681685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681809 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 4]
def baseStart_3681809 : Nat := 118140960795 + 3681809 * 2 ^ 59
def prefixEnd_3681809 : Nat := 4983230072969 + 3 ^ 40 * 3681809 * 2
def baseEnd_3681809 : Nat := 420119487788820142012261

theorem tailTrace_3681809 : CollatzResearch.WordTrace tailWord_3681809 prefixEnd_3681809 420119487788820142012261 := by
  unfold tailWord_3681809
  simp only [CollatzResearch.WordTrace]
  refine ⟨134286606318442270760752481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89524404212294847173834987 134286606318442270760752481)
  ·
    refine ⟨100714954738831703070564361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134286606318442270760752481 100714954738831703070564361)
    ·
      refine ⟨75536216054123777302923271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100714954738831703070564361 75536216054123777302923271)
      ·
        refine ⟨113304324081185665954384907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75536216054123777302923271 113304324081185665954384907)
        ·
          refine ⟨169956486121778498931577361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113304324081185665954384907 169956486121778498931577361)
          ·
            refine ⟨127467364591333874198683021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169956486121778498931577361 127467364591333874198683021)
            ·
              refine ⟨47800261721750202824506133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127467364591333874198683021 47800261721750202824506133)
              ·
                refine ⟨2240637268207040757398725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47800261721750202824506133 2240637268207040757398725)
                ·
                  refine ⟨420119487788820142012261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240637268207040757398725 420119487788820142012261)
                  ·
                    rfl

theorem cell22_3681809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_3681809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681809 prefixEnd_3681809 := by exact prefixLift 3681809
  have htrace : WordTrace (prefixWord ++ tailWord_3681809) baseStart_3681809 baseEnd_3681809 := by
    simpa [prefixWord, tailWord_3681809, baseEnd_3681809] using wordTrace_append hprefix tailTrace_3681809
  have hstable : (prefixWord ++ tailWord_3681809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681809).length < 2 ^ (prefixWord ++ tailWord_3681809).sum := by decide
  have hdescent : baseEnd_3681809 < baseStart_3681809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681867 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_3681867 : Nat := 118140960795 + 3681867 * 2 ^ 59
def prefixEnd_3681867 : Nat := 4983230072969 + 3 ^ 40 * 3681867 * 2
def baseEnd_3681867 : Nat := 1260378317951767608086605

theorem tailTrace_3681867 : CollatzResearch.WordTrace tailWord_3681867 prefixEnd_3681867 1260378317951767608086605 := by
  unfold tailWord_3681867
  simp only [CollatzResearch.WordTrace]
  refine ⟨134288721752232146666363855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89525814501488097777575903 134288721752232146666363855)
  ·
    refine ⟨201433082628348219999545783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134288721752232146666363855 201433082628348219999545783)
    ·
      refine ⟨302149623942522329999318675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201433082628348219999545783 302149623942522329999318675)
      ·
        refine ⟨453224435913783494998978013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302149623942522329999318675 453224435913783494998978013)
        ·
          refine ⟨169959163467668810624616755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453224435913783494998978013 169959163467668810624616755)
          ·
            refine ⟨254938745201503215936925133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169959163467668810624616755 254938745201503215936925133)
            ·
              refine ⟨95602029450563705976346925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254938745201503215936925133 95602029450563705976346925)
              ·
                refine ⟨35850761043961389741130097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95602029450563705976346925 35850761043961389741130097)
                ·
                  refine ⟨26888070782971042305847573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35850761043961389741130097 26888070782971042305847573)
                  ·
                    refine ⟨1260378317951767608086605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26888070782971042305847573 1260378317951767608086605)
                    ·
                      rfl

theorem cell22_3681867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_3681867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681867 prefixEnd_3681867 := by exact prefixLift 3681867
  have htrace : WordTrace (prefixWord ++ tailWord_3681867) baseStart_3681867 baseEnd_3681867 := by
    simpa [prefixWord, tailWord_3681867, baseEnd_3681867] using wordTrace_append hprefix tailTrace_3681867
  have hstable : (prefixWord ++ tailWord_3681867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681867).length < 2 ^ (prefixWord ++ tailWord_3681867).sum := by decide
  have hdescent : baseEnd_3681867 < baseStart_3681867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681929 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_3681929 : Nat := 118140960795 + 3681929 * 2 ^ 59
def prefixEnd_3681929 : Nat := 4983230072969 + 3 ^ 40 * 3681929 * 2
def baseEnd_3681929 : Nat := 1260399541818820113036415

theorem tailTrace_3681929 : CollatzResearch.WordTrace tailWord_3681929 prefixEnd_3681929 1260399541818820113036415 := by
  unfold tailWord_3681929
  simp only [CollatzResearch.WordTrace]
  refine ⟨134290983078007531255120841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89527322052005020836747227 134290983078007531255120841)
  ·
    refine ⟨100718237308505648441340631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134290983078007531255120841 100718237308505648441340631)
    ·
      refine ⟨151077355962758472662010947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100718237308505648441340631 151077355962758472662010947)
      ·
        refine ⟨226616033944137708993016421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151077355962758472662010947 226616033944137708993016421)
        ·
          refine ⟨42490506364525820436190579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226616033944137708993016421 42490506364525820436190579)
          ·
            refine ⟨63735759546788730654285869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42490506364525820436190579 63735759546788730654285869)
            ·
              refine ⟨23900909830045773995357201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63735759546788730654285869 23900909830045773995357201)
              ·
                refine ⟨17925682372534330496517901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23900909830045773995357201 17925682372534330496517901)
                ·
                  refine ⟨6722130889700373936194213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17925682372534330496517901 6722130889700373936194213)
                  ·
                    refine ⟨1260399541818820113036415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722130889700373936194213 1260399541818820113036415)
                    ·
                      rfl

theorem cell22_3681929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_3681929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681929 prefixEnd_3681929 := by exact prefixLift 3681929
  have htrace : WordTrace (prefixWord ++ tailWord_3681929) baseStart_3681929 baseEnd_3681929 := by
    simpa [prefixWord, tailWord_3681929, baseEnd_3681929] using wordTrace_append hprefix tailTrace_3681929
  have hstable : (prefixWord ++ tailWord_3681929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681929).length < 2 ^ (prefixWord ++ tailWord_3681929).sum := by decide
  have hdescent : baseEnd_3681929 < baseStart_3681929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681944 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_3681944 : Nat := 118140960795 + 3681944 * 2 ^ 59
def prefixEnd_3681944 : Nat := 4983230072969 + 3 ^ 40 * 3681944 * 2
def baseEnd_3681944 : Nat := 420134892208455024637123

theorem tailTrace_3681944 : CollatzResearch.WordTrace tailWord_3681944 prefixEnd_3681944 420134892208455024637123 := by
  unfold tailWord_3681944
  simp only [CollatzResearch.WordTrace]
  refine ⟨67145765086476594408458443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89527686781968792544611257 67145765086476594408458443)
  ·
    refine ⟨100718647629714891612687665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67145765086476594408458443 100718647629714891612687665)
    ·
      refine ⟨75538985722286168709515749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100718647629714891612687665 75538985722286168709515749)
      ·
        refine ⟨14163559822928656633034203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75538985722286168709515749 14163559822928656633034203)
        ·
          refine ⟨21245339734392984949551305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163559822928656633034203 21245339734392984949551305)
          ·
            refine ⟨15934004800794738712163479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21245339734392984949551305 15934004800794738712163479)
            ·
              refine ⟨23901007201192108068245219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934004800794738712163479 23901007201192108068245219)
              ·
                refine ⟨35851510801788162102367829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23901007201192108068245219 35851510801788162102367829)
                ·
                  refine ⟨420134892208455024637123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35851510801788162102367829 420134892208455024637123)
                  ·
                    rfl

theorem cell22_3681944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_3681944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3681944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3681944 prefixEnd_3681944 := by exact prefixLift 3681944
  have htrace : WordTrace (prefixWord ++ tailWord_3681944) baseStart_3681944 baseEnd_3681944 := by
    simpa [prefixWord, tailWord_3681944, baseEnd_3681944] using wordTrace_append hprefix tailTrace_3681944
  have hstable : (prefixWord ++ tailWord_3681944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681944).length < 2 ^ (prefixWord ++ tailWord_3681944).sum := by decide
  have hdescent : baseEnd_3681944 < baseStart_3681944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682012 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_3682012 : Nat := 118140960795 + 3682012 * 2 ^ 59
def prefixEnd_3682012 : Nat := 4983230072969 + 3 ^ 40 * 3682012 * 2
def baseEnd_3682012 : Nat := 420142651471678521070387

theorem tailTrace_3682012 : CollatzResearch.WordTrace tailWord_3682012 prefixEnd_3682012 420142651471678521070387 := by
  unfold tailWord_3682012
  simp only [CollatzResearch.WordTrace]
  refine ⟨67147005168353418215196145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89529340224471224286928193 67147005168353418215196145)
  ·
    refine ⟨50360253876265063661397109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67147005168353418215196145 50360253876265063661397109)
    ·
      refine ⟨4721273800899849718255979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50360253876265063661397109 4721273800899849718255979)
      ·
        refine ⟨7081910701349774577383969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721273800899849718255979 7081910701349774577383969)
        ·
          refine ⟨5311433026012330933037977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7081910701349774577383969 5311433026012330933037977)
          ·
            refine ⟨3983574769509248199778483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311433026012330933037977 3983574769509248199778483)
            ·
              refine ⟨5975362154263872299667725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983574769509248199778483 5975362154263872299667725)
              ·
                refine ⟨2240760807848952112375397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975362154263872299667725 2240760807848952112375397)
                ·
                  refine ⟨420142651471678521070387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240760807848952112375397 420142651471678521070387)
                  ·
                    rfl

theorem cell22_3682012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_3682012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682012 prefixEnd_3682012 := by exact prefixLift 3682012
  have htrace : WordTrace (prefixWord ++ tailWord_3682012) baseStart_3682012 baseEnd_3682012 := by
    simpa [prefixWord, tailWord_3682012, baseEnd_3682012] using wordTrace_append hprefix tailTrace_3682012
  have hstable : (prefixWord ++ tailWord_3682012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682012).length < 2 ^ (prefixWord ++ tailWord_3682012).sum := by decide
  have hdescent : baseEnd_3682012 < baseStart_3682012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682023 : List Nat := [1, 1, 5, 4, 1, 2, 8]
def baseStart_3682023 : Nat := 118140960795 + 3682023 * 2 ^ 59
def prefixEnd_3682023 : Nat := 4983230072969 + 3 ^ 40 * 3682023 * 2
def baseEnd_3682023 : Nat := 46682656294067970414301

theorem tailTrace_3682023 : CollatzResearch.WordTrace tailWord_3682023 prefixEnd_3682023 46682656294067970414301 := by
  unfold tailWord_3682023
  simp only [CollatzResearch.WordTrace]
  refine ⟨134294411539666985309042723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89529607693111323539361815 134294411539666985309042723)
  ·
    refine ⟨201441617309500477963564085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134294411539666985309042723 201441617309500477963564085)
    ·
      refine ⟨18885151622765669809084133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201441617309500477963564085 18885151622765669809084133)
      ·
        refine ⟨3540965929268563089203275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18885151622765669809084133 3540965929268563089203275)
        ·
          refine ⟨5311448893902844633804913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540965929268563089203275 5311448893902844633804913)
          ·
            refine ⟨3983586670427133475353685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311448893902844633804913 3983586670427133475353685)
            ·
              refine ⟨46682656294067970414301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3983586670427133475353685 46682656294067970414301)
              ·
                rfl

theorem cell22_3682023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 8].length) (baseStart_3682023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682023 prefixEnd_3682023 := by exact prefixLift 3682023
  have htrace : WordTrace (prefixWord ++ tailWord_3682023) baseStart_3682023 baseEnd_3682023 := by
    simpa [prefixWord, tailWord_3682023, baseEnd_3682023] using wordTrace_append hprefix tailTrace_3682023
  have hstable : (prefixWord ++ tailWord_3682023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682023).length < 2 ^ (prefixWord ++ tailWord_3682023).sum := by decide
  have hdescent : baseEnd_3682023 < baseStart_3682023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682130 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_3682130 : Nat := 118140960795 + 3682130 * 2 ^ 59
def prefixEnd_3682130 : Nat := 4983230072969 + 3 ^ 40 * 3682130 * 2
def baseEnd_3682130 : Nat := 420156116075507529586933

theorem tailTrace_3682130 : CollatzResearch.WordTrace tailWord_3682130 prefixEnd_3682130 420156116075507529586933 := by
  unfold tailWord_3682130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33574578537569835645796961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89532209433519561722125229 33574578537569835645796961)
  ·
    refine ⟨25180933903177376734347721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33574578537569835645796961 25180933903177376734347721)
    ·
      refine ⟨18885700427383032550760791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25180933903177376734347721 18885700427383032550760791)
      ·
        refine ⟨28328550641074548826141187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18885700427383032550760791 28328550641074548826141187)
        ·
          refine ⟨42492825961611823239211781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28328550641074548826141187 42492825961611823239211781)
          ·
            refine ⟨7967404867802216857352209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42492825961611823239211781 7967404867802216857352209)
            ·
              refine ⟨5975553650851662643014157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967404867802216857352209 5975553650851662643014157)
              ·
                refine ⟨2240832619069373491130309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975553650851662643014157 2240832619069373491130309)
                ·
                  refine ⟨420156116075507529586933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2240832619069373491130309 420156116075507529586933)
                  ·
                    rfl

theorem cell22_3682130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_3682130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682130 prefixEnd_3682130 := by exact prefixLift 3682130
  have htrace : WordTrace (prefixWord ++ tailWord_3682130) baseStart_3682130 baseEnd_3682130 := by
    simpa [prefixWord, tailWord_3682130, baseEnd_3682130] using wordTrace_append hprefix tailTrace_3682130
  have hstable : (prefixWord ++ tailWord_3682130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682130).length < 2 ^ (prefixWord ++ tailWord_3682130).sum := by decide
  have hdescent : baseEnd_3682130 < baseStart_3682130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682132 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3682132 : Nat := 118140960795 + 3682132 * 2 ^ 59
def prefixEnd_3682132 : Nat := 4983230072969 + 3 ^ 40 * 3682132 * 2
def baseEnd_3682132 : Nat := 1260469032867395250210793

theorem tailTrace_3682132 : CollatzResearch.WordTrace tailWord_3682132 prefixEnd_3682132 1260469032867395250210793 := by
  unfold tailWord_3682132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67149193548136048462380325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89532258064181397949840433 67149193548136048462380325)
  ·
    refine ⟨12590473790275509086696311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67149193548136048462380325 12590473790275509086696311)
    ·
      refine ⟨18885710685413263630044467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12590473790275509086696311 18885710685413263630044467)
      ·
        refine ⟨28328566028119895445066701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18885710685413263630044467 28328566028119895445066701)
        ·
          refine ⟨10623212260544960791900013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28328566028119895445066701 10623212260544960791900013)
          ·
            refine ⟨3983704597704360296962505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10623212260544960791900013 3983704597704360296962505)
            ·
              refine ⟨2987778448278270222721879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983704597704360296962505 2987778448278270222721879)
              ·
                refine ⟨4481667672417405334082819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987778448278270222721879 4481667672417405334082819)
                ·
                  refine ⟨6722501508626108001124229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481667672417405334082819 6722501508626108001124229)
                  ·
                    refine ⟨1260469032867395250210793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722501508626108001124229 1260469032867395250210793)
                    ·
                      rfl

theorem cell22_3682132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3682132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682132 prefixEnd_3682132 := by exact prefixLift 3682132
  have htrace : WordTrace (prefixWord ++ tailWord_3682132) baseStart_3682132 baseEnd_3682132 := by
    simpa [prefixWord, tailWord_3682132, baseEnd_3682132] using wordTrace_append hprefix tailTrace_3682132
  have hstable : (prefixWord ++ tailWord_3682132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682132).length < 2 ^ (prefixWord ++ tailWord_3682132).sum := by decide
  have hdescent : baseEnd_3682132 < baseStart_3682132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682201 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_3682201 : Nat := 118140960795 + 3682201 * 2 ^ 59
def prefixEnd_3682201 : Nat := 4983230072969 + 3 ^ 40 * 3682201 * 2
def baseEnd_3682201 : Nat := 1260492652977502070235581

theorem tailTrace_3682201 : CollatzResearch.WordTrace tailWord_3682201 prefixEnd_3682201 1260492652977502070235581 := by
  unfold tailWord_3682201
  simp only [CollatzResearch.WordTrace]
  refine ⟨134300903733022121709022457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89533935822014747806014971 134300903733022121709022457)
  ·
    refine ⟨100725677799766591281766843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134300903733022121709022457 100725677799766591281766843)
    ·
      refine ⟨151088516699649886922650265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100725677799766591281766843 151088516699649886922650265)
      ·
        refine ⟨113316387524737415191987699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151088516699649886922650265 113316387524737415191987699)
        ·
          refine ⟨169974581287106122787981549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113316387524737415191987699 169974581287106122787981549)
          ·
            refine ⟨63740467982664796045493081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169974581287106122787981549 63740467982664796045493081)
            ·
              refine ⟨47805350986998597034119811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63740467982664796045493081 47805350986998597034119811)
              ·
                refine ⟨71708026480497895551179717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47805350986998597034119811 71708026480497895551179717)
                ·
                  refine ⟨13445254965093355415846197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71708026480497895551179717 13445254965093355415846197)
                  ·
                    refine ⟨1260492652977502070235581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13445254965093355415846197 1260492652977502070235581)
                    ·
                      rfl

theorem cell22_3682201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_3682201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682201 prefixEnd_3682201 := by exact prefixLift 3682201
  have htrace : WordTrace (prefixWord ++ tailWord_3682201) baseStart_3682201 baseEnd_3682201 := by
    simpa [prefixWord, tailWord_3682201, baseEnd_3682201] using wordTrace_append hprefix tailTrace_3682201
  have hstable : (prefixWord ++ tailWord_3682201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682201).length < 2 ^ (prefixWord ++ tailWord_3682201).sum := by decide
  have hdescent : baseEnd_3682201 < baseStart_3682201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682207 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 3, 3]
def baseStart_3682207 : Nat := 118140960795 + 3682207 * 2 ^ 59
def prefixEnd_3682207 : Nat := 4983230072969 + 3 ^ 40 * 3682207 * 2
def baseEnd_3682207 : Nat := 1260494706900120054585563

theorem tailTrace_3682207 : CollatzResearch.WordTrace tailWord_3682207 prefixEnd_3682207 1260494706900120054585563 := by
  unfold tailWord_3682207
  simp only [CollatzResearch.WordTrace]
  refine ⟨134301122571000384733740875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89534081714000256489160583 134301122571000384733740875)
  ·
    refine ⟨201451683856500577100611313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134301122571000384733740875 201451683856500577100611313)
    ·
      refine ⟨151088762892375432825458485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201451683856500577100611313 151088762892375432825458485)
      ·
        refine ⟨14164571521160196827386733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151088762892375432825458485 14164571521160196827386733)
        ·
          refine ⟨5311714320435073810270025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14164571521160196827386733 5311714320435073810270025)
          ·
            refine ⟨3983785740326305357702519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311714320435073810270025 3983785740326305357702519)
            ·
              refine ⟨5975678610489458036553779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983785740326305357702519 5975678610489458036553779)
              ·
                refine ⟨8963517915734187054830669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975678610489458036553779 8963517915734187054830669)
                ·
                  refine ⟨3361319218400320145561501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8963517915734187054830669 3361319218400320145561501)
                  ·
                    refine ⟨1260494706900120054585563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361319218400320145561501 1260494706900120054585563)
                    ·
                      rfl

theorem cell22_3682207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_3682207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682207 prefixEnd_3682207 := by exact prefixLift 3682207
  have htrace : WordTrace (prefixWord ++ tailWord_3682207) baseStart_3682207 baseEnd_3682207 := by
    simpa [prefixWord, tailWord_3682207, baseEnd_3682207] using wordTrace_append hprefix tailTrace_3682207
  have hstable : (prefixWord ++ tailWord_3682207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682207).length < 2 ^ (prefixWord ++ tailWord_3682207).sum := by decide
  have hdescent : baseEnd_3682207 < baseStart_3682207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682231 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 8]
def baseStart_3682231 : Nat := 118140960795 + 3682231 * 2 ^ 59
def prefixEnd_3682231 : Nat := 4983230072969 + 3 ^ 40 * 3682231 * 2
def baseEnd_3682231 : Nat := 420167640863530663995163

theorem tailTrace_3682231 : CollatzResearch.WordTrace tailWord_3682231 prefixEnd_3682231 420167640863530663995163 := by
  unfold tailWord_3682231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134301997922913436832614547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89534665281942291221743031 134301997922913436832614547)
  ·
    refine ⟨201452996884370155248921821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134301997922913436832614547 201452996884370155248921821)
    ·
      refine ⟨75544873831638808218345683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201452996884370155248921821 75544873831638808218345683)
      ·
        refine ⟨113317310747458212327518525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75544873831638808218345683 113317310747458212327518525)
        ·
          refine ⟨42493991530296829622819447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113317310747458212327518525 42493991530296829622819447)
          ·
            refine ⟨63740987295445244434229171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42493991530296829622819447 63740987295445244434229171)
            ·
              refine ⟨95611480943167866651343757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63740987295445244434229171 95611480943167866651343757)
              ·
                refine ⟨35854305353687949994253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95611480943167866651343757 35854305353687949994253909)
                ·
                  refine ⟨420167640863530663995163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35854305353687949994253909 420167640863530663995163)
                  ·
                    rfl

theorem cell22_3682231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_3682231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682231 prefixEnd_3682231 := by exact prefixLift 3682231
  have htrace : WordTrace (prefixWord ++ tailWord_3682231) baseStart_3682231 baseEnd_3682231 := by
    simpa [prefixWord, tailWord_3682231, baseEnd_3682231] using wordTrace_append hprefix tailTrace_3682231
  have hstable : (prefixWord ++ tailWord_3682231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682231).length < 2 ^ (prefixWord ++ tailWord_3682231).sum := by decide
  have hdescent : baseEnd_3682231 < baseStart_3682231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682233 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3682233 : Nat := 118140960795 + 3682233 * 2 ^ 59
def prefixEnd_3682233 : Nat := 4983230072969 + 3 ^ 40 * 3682233 * 2
def baseEnd_3682233 : Nat := 1260503607231464653435483

theorem tailTrace_3682233 : CollatzResearch.WordTrace tailWord_3682233 prefixEnd_3682233 1260503607231464653435483 := by
  unfold tailWord_3682233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134302070868906191174187353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89534713912604127449458235 134302070868906191174187353)
  ·
    refine ⟨100726553151679643380640515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134302070868906191174187353 100726553151679643380640515)
    ·
      refine ⟨151089829727519465070960773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100726553151679643380640515 151089829727519465070960773)
      ·
        refine ⟨28329343073909899700805145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151089829727519465070960773 28329343073909899700805145)
        ·
          refine ⟨21247007305432424775603859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28329343073909899700805145 21247007305432424775603859)
          ·
            refine ⟨31870510958148637163405789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21247007305432424775603859 31870510958148637163405789)
            ·
              refine ⟨11951441609305738936277171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31870510958148637163405789 11951441609305738936277171)
              ·
                refine ⟨17927162413958608404415757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11951441609305738936277171 17927162413958608404415757)
                ·
                  refine ⟨6722685905234478151655909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17927162413958608404415757 6722685905234478151655909)
                  ·
                    refine ⟨1260503607231464653435483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722685905234478151655909 1260503607231464653435483)
                    ·
                      rfl

theorem cell22_3682233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3682233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682233 prefixEnd_3682233 := by exact prefixLift 3682233
  have htrace : WordTrace (prefixWord ++ tailWord_3682233) baseStart_3682233 baseEnd_3682233 := by
    simpa [prefixWord, tailWord_3682233, baseEnd_3682233] using wordTrace_append hprefix tailTrace_3682233
  have hstable : (prefixWord ++ tailWord_3682233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682233).length < 2 ^ (prefixWord ++ tailWord_3682233).sum := by decide
  have hdescent : baseEnd_3682233 < baseStart_3682233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682258 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3682258 : Nat := 118140960795 + 3682258 * 2 ^ 59
def prefixEnd_3682258 : Nat := 4983230072969 + 3 ^ 40 * 3682258 * 2
def baseEnd_3682258 : Nat := 1260512165242372921560407

theorem tailTrace_3682258 : CollatzResearch.WordTrace tailWord_3682258 prefixEnd_3682258 1260512165242372921560407 := by
  unfold tailWord_3682258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33575745673453905110961857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89535321795877080295898285 33575745673453905110961857)
  ·
    refine ⟨25181809255090428833221393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33575745673453905110961857 25181809255090428833221393)
    ·
      refine ⟨18886356941317821624916045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25181809255090428833221393 18886356941317821624916045)
      ·
        refine ⟨7082383852994183109343517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18886356941317821624916045 7082383852994183109343517)
        ·
          refine ⟨2655893944872818666003819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7082383852994183109343517 2655893944872818666003819)
          ·
            refine ⟨3983840917309227999005729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655893944872818666003819 3983840917309227999005729)
            ·
              refine ⟨2987880687981920999254297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983840917309227999005729 2987880687981920999254297)
              ·
                refine ⟨2240910515986440749440723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987880687981920999254297 2240910515986440749440723)
                ·
                  refine ⟨3361365773979661124161085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240910515986440749440723 3361365773979661124161085)
                  ·
                    refine ⟨1260512165242372921560407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361365773979661124161085 1260512165242372921560407)
                    ·
                      rfl

theorem cell22_3682258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3682258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682258 prefixEnd_3682258 := by exact prefixLift 3682258
  have htrace : WordTrace (prefixWord ++ tailWord_3682258) baseStart_3682258 baseEnd_3682258 := by
    simpa [prefixWord, tailWord_3682258, baseEnd_3682258] using wordTrace_append hprefix tailTrace_3682258
  have hstable : (prefixWord ++ tailWord_3682258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682258).length < 2 ^ (prefixWord ++ tailWord_3682258).sum := by decide
  have hdescent : baseEnd_3682258 < baseStart_3682258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682314 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3682314 : Nat := 118140960795 + 3682314 * 2 ^ 59
def prefixEnd_3682314 : Nat := 4983230072969 + 3 ^ 40 * 3682314 * 2
def baseEnd_3682314 : Nat := 1260531335186807442160235

theorem tailTrace_3682314 : CollatzResearch.WordTrace tailWord_3682314 prefixEnd_3682314 1260531335186807442160235 := by
  unfold tailWord_3682314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576256295403185501971499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89536683454408494671923997 33576256295403185501971499)
  ·
    refine ⟨50364384443104778252957249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33576256295403185501971499 50364384443104778252957249)
    ·
      refine ⟨37773288332328583689717937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50364384443104778252957249 37773288332328583689717937)
      ·
        refine ⟨28329966249246437767288453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37773288332328583689717937 28329966249246437767288453)
        ·
          refine ⟨5311868671733707081366585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28329966249246437767288453 5311868671733707081366585)
          ·
            refine ⟨3983901503800280311024939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311868671733707081366585 3983901503800280311024939)
            ·
              refine ⟨5975852255700420466537409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983901503800280311024939 5975852255700420466537409)
              ·
                refine ⟨4481889191775315349903057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5975852255700420466537409 4481889191775315349903057)
                ·
                  refine ⟨3361416893831486512427293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4481889191775315349903057 3361416893831486512427293)
                  ·
                    refine ⟨1260531335186807442160235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361416893831486512427293 1260531335186807442160235)
                    ·
                      rfl

theorem cell22_3682314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3682314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682314 prefixEnd_3682314 := by exact prefixLift 3682314
  have htrace : WordTrace (prefixWord ++ tailWord_3682314) baseStart_3682314 baseEnd_3682314 := by
    simpa [prefixWord, tailWord_3682314, baseEnd_3682314] using wordTrace_append hprefix tailTrace_3682314
  have hstable : (prefixWord ++ tailWord_3682314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682314).length < 2 ^ (prefixWord ++ tailWord_3682314).sum := by decide
  have hdescent : baseEnd_3682314 < baseStart_3682314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682344 : List Nat := [2, 1, 5, 3, 1, 2, 2, 6]
def baseStart_3682344 : Nat := 118140960795 + 3682344 * 2 ^ 59
def prefixEnd_3682344 : Nat := 4983230072969 + 3 ^ 40 * 3682344 * 2
def baseEnd_3682344 : Nat := 140060178311099707101127

theorem tailTrace_3682344 : CollatzResearch.WordTrace tailWord_3682344 prefixEnd_3682344 140060178311099707101127 := by
  unfold tailWord_3682344
  simp only [CollatzResearch.WordTrace]
  refine ⟨67153059685752028565739043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89537412914336038087652057 67153059685752028565739043)
  ·
    refine ⟨100729589528628042848608565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67153059685752028565739043 100729589528628042848608565)
    ·
      refine ⟨9443399018308879017057053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100729589528628042848608565 9443399018308879017057053)
      ·
        refine ⟨3541274631865829631396395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9443399018308879017057053 3541274631865829631396395)
        ·
          refine ⟨5311911947798744447094593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541274631865829631396395 5311911947798744447094593)
          ·
            refine ⟨3983933960849058335320945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311911947798744447094593 3983933960849058335320945)
            ·
              refine ⟨2987950470636793751490709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983933960849058335320945 2987950470636793751490709)
              ·
                refine ⟨140060178311099707101127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2987950470636793751490709 140060178311099707101127)
                ·
                  rfl

theorem cell22_3682344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 6].length) (baseStart_3682344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682344 prefixEnd_3682344 := by exact prefixLift 3682344
  have htrace : WordTrace (prefixWord ++ tailWord_3682344) baseStart_3682344 baseEnd_3682344 := by
    simpa [prefixWord, tailWord_3682344, baseEnd_3682344] using wordTrace_append hprefix tailTrace_3682344
  have hstable : (prefixWord ++ tailWord_3682344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682344).length < 2 ^ (prefixWord ++ tailWord_3682344).sum := by decide
  have hdescent : baseEnd_3682344 < baseStart_3682344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682415 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3682415 : Nat := 118140960795 + 3682415 * 2 ^ 59
def prefixEnd_3682415 : Nat := 4983230072969 + 3 ^ 40 * 3682415 * 2
def baseEnd_3682415 : Nat := 1260565909550876845384925

theorem tailTrace_3682415 : CollatzResearch.WordTrace tailWord_3682415 prefixEnd_3682415 1260565909550876845384925 := by
  unfold tailWord_3682415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134308708954246836257312699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89539139302831224171541799 134308708954246836257312699)
  ·
    refine ⟨201463063431370254385969049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134308708954246836257312699 201463063431370254385969049)
    ·
      refine ⟨151097297573527690789476787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201463063431370254385969049 151097297573527690789476787)
      ·
        refine ⟨226645946360291536184215181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151097297573527690789476787 226645946360291536184215181)
        ·
          refine ⟨84992229885109326069080693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226645946360291536184215181 84992229885109326069080693)
          ·
            refine ⟨7968021551728999318976315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84992229885109326069080693 7968021551728999318976315)
            ·
              refine ⟨11952032327593498978464473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968021551728999318976315 11952032327593498978464473)
              ·
                refine ⟨8964024245695124233848355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952032327593498978464473 8964024245695124233848355)
                ·
                  refine ⟨13446036368542686350772533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8964024245695124233848355 13446036368542686350772533)
                  ·
                    refine ⟨1260565909550876845384925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13446036368542686350772533 1260565909550876845384925)
                    ·
                      rfl

theorem cell22_3682415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3682415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682415 prefixEnd_3682415 := by exact prefixLift 3682415
  have htrace : WordTrace (prefixWord ++ tailWord_3682415) baseStart_3682415 baseEnd_3682415 := by
    simpa [prefixWord, tailWord_3682415, baseEnd_3682415] using wordTrace_append hprefix tailTrace_3682415
  have hstable : (prefixWord ++ tailWord_3682415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682415).length < 2 ^ (prefixWord ++ tailWord_3682415).sum := by decide
  have hdescent : baseEnd_3682415 < baseStart_3682415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682428 : List Nat := [2, 2, 2, 1, 1, 14]
def baseStart_3682428 : Nat := 118140960795 + 3682428 * 2 ^ 59
def prefixEnd_3682428 : Nat := 4983230072969 + 3 ^ 40 * 3682428 * 2
def baseEnd_3682428 : Nat := 15562597033537643763085

theorem tailTrace_3682428 : CollatzResearch.WordTrace tailWord_3682428 prefixEnd_3682428 15562597033537643763085 := by
  unfold tailWord_3682428
  simp only [CollatzResearch.WordTrace]
  refine ⟨67154591551599869738767969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89539455402133159651690625 67154591551599869738767969)
  ·
    refine ⟨50365943663699902304075977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67154591551599869738767969 50365943663699902304075977)
    ·
      refine ⟨37774457747774926728056983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50365943663699902304075977 37774457747774926728056983)
      ·
        refine ⟨56661686621662390092085475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37774457747774926728056983 56661686621662390092085475)
        ·
          refine ⟨84992529932493585138128213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56661686621662390092085475 84992529932493585138128213)
          ·
            refine ⟨15562597033537643763085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 84992529932493585138128213 15562597033537643763085)
            ·
              rfl

theorem cell22_3682428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 14].length) (baseStart_3682428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682428 prefixEnd_3682428 := by exact prefixLift 3682428
  have htrace : WordTrace (prefixWord ++ tailWord_3682428) baseStart_3682428 baseEnd_3682428 := by
    simpa [prefixWord, tailWord_3682428, baseEnd_3682428] using wordTrace_append hprefix tailTrace_3682428
  have hstable : (prefixWord ++ tailWord_3682428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682428).length < 2 ^ (prefixWord ++ tailWord_3682428).sum := by decide
  have hdescent : baseEnd_3682428 < baseStart_3682428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_3682443 : Nat := 118140960795 + 3682443 * 2 ^ 59
def prefixEnd_3682443 : Nat := 4983230072969 + 3 ^ 40 * 3682443 * 2
def baseEnd_3682443 : Nat := 1260575494523094105684839

theorem tailTrace_3682443 : CollatzResearch.WordTrace tailWord_3682443 prefixEnd_3682443 1260575494523094105684839 := by
  unfold tailWord_3682443
  simp only [CollatzResearch.WordTrace]
  refine ⟨134309730198145397039331983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89539820132096931359554655 134309730198145397039331983)
  ·
    refine ⟨201464595297218095558997975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134309730198145397039331983 201464595297218095558997975)
    ·
      refine ⟨302196892945827143338496963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201464595297218095558997975 302196892945827143338496963)
      ·
        refine ⟨453295339418740715007745445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302196892945827143338496963 453295339418740715007745445)
        ·
          refine ⟨84992876141013884063952271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453295339418740715007745445 84992876141013884063952271)
          ·
            refine ⟨127489314211520826095928407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84992876141013884063952271 127489314211520826095928407)
            ·
              refine ⟨191233971317281239143892611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127489314211520826095928407 191233971317281239143892611)
              ·
                refine ⟨286850956975921858715838917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191233971317281239143892611 286850956975921858715838917)
                ·
                  refine ⟨53784554432985348509219797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286850956975921858715838917 53784554432985348509219797)
                  ·
                    refine ⟨1260575494523094105684839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53784554432985348509219797 1260575494523094105684839)
                    ·
                      rfl

theorem cell22_3682443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_3682443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682443 prefixEnd_3682443 := by exact prefixLift 3682443
  have htrace : WordTrace (prefixWord ++ tailWord_3682443) baseStart_3682443 baseEnd_3682443 := by
    simpa [prefixWord, tailWord_3682443, baseEnd_3682443] using wordTrace_append hprefix tailTrace_3682443
  have hstable : (prefixWord ++ tailWord_3682443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682443).length < 2 ^ (prefixWord ++ tailWord_3682443).sum := by decide
  have hdescent : baseEnd_3682443 < baseStart_3682443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682507 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 5]
def baseStart_3682507 : Nat := 118140960795 + 3682507 * 2 ^ 59
def prefixEnd_3682507 : Nat := 4983230072969 + 3 ^ 40 * 3682507 * 2
def baseEnd_3682507 : Nat := 420199134343673090694881

theorem tailTrace_3682507 : CollatzResearch.WordTrace tailWord_3682507 prefixEnd_3682507 420199134343673090694881 := by
  unfold tailWord_3682507
  simp only [CollatzResearch.WordTrace]
  refine ⟨134312064469913535969661775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89541376313275690646441183 134312064469913535969661775)
  ·
    refine ⟨201468096704870303954492663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134312064469913535969661775 201468096704870303954492663)
    ·
      refine ⟨302202145057305455931738995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201468096704870303954492663 302202145057305455931738995)
      ·
        refine ⟨453303217585958183897608493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302202145057305455931738995 453303217585958183897608493)
        ·
          refine ⟨169988706594734318961603185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453303217585958183897608493 169988706594734318961603185)
          ·
            refine ⟨127491529946050739221202389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169988706594734318961603185 127491529946050739221202389)
            ·
              refine ⟨2988082733110564200496931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127491529946050739221202389 2988082733110564200496931)
              ·
                refine ⟨4482124099665846300745397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988082733110564200496931 4482124099665846300745397)
                ·
                  refine ⟨420199134343673090694881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482124099665846300745397 420199134343673090694881)
                  ·
                    rfl

theorem cell22_3682507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 5].length) (baseStart_3682507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682507 prefixEnd_3682507 := by exact prefixLift 3682507
  have htrace : WordTrace (prefixWord ++ tailWord_3682507) baseStart_3682507 baseEnd_3682507 := by
    simpa [prefixWord, tailWord_3682507, baseEnd_3682507] using wordTrace_append hprefix tailTrace_3682507
  have hstable : (prefixWord ++ tailWord_3682507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682507).length < 2 ^ (prefixWord ++ tailWord_3682507).sum := by decide
  have hdescent : baseEnd_3682507 < baseStart_3682507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682552 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_3682552 : Nat := 118140960795 + 3682552 * 2 ^ 59
def prefixEnd_3682552 : Nat := 4983230072969 + 3 ^ 40 * 3682552 * 2
def baseEnd_3682552 : Nat := 420204269150218051569835

theorem tailTrace_3682552 : CollatzResearch.WordTrace tailWord_3682552 prefixEnd_3682552 420204269150218051569835 := by
  unfold tailWord_3682552
  simp only [CollatzResearch.WordTrace]
  refine ⟨67156852877375254327524955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89542470503167005770033273 67156852877375254327524955)
  ·
    refine ⟨100735279316062881491287433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67156852877375254327524955 100735279316062881491287433)
    ·
      refine ⟨75551459487047161118465575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100735279316062881491287433 75551459487047161118465575)
      ·
        refine ⟨113327189230570741677698363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75551459487047161118465575 113327189230570741677698363)
        ·
          refine ⟨169990783845856112516547545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113327189230570741677698363 169990783845856112516547545)
          ·
            refine ⟨127493087884392084387410659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169990783845856112516547545 127493087884392084387410659)
            ·
              refine ⟨191239631826588126581115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127493087884392084387410659 191239631826588126581115989)
              ·
                refine ⟨2241089435467829608372453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 191239631826588126581115989 2241089435467829608372453)
                ·
                  refine ⟨420204269150218051569835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241089435467829608372453 420204269150218051569835)
                  ·
                    rfl

theorem cell22_3682552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_3682552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682552 prefixEnd_3682552 := by exact prefixLift 3682552
  have htrace : WordTrace (prefixWord ++ tailWord_3682552) baseStart_3682552 baseEnd_3682552 := by
    simpa [prefixWord, tailWord_3682552, baseEnd_3682552] using wordTrace_append hprefix tailTrace_3682552
  have hstable : (prefixWord ++ tailWord_3682552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682552).length < 2 ^ (prefixWord ++ tailWord_3682552).sum := by decide
  have hdescent : baseEnd_3682552 < baseStart_3682552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682565 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_3682565 : Nat := 118140960795 + 3682565 * 2 ^ 59
def prefixEnd_3682565 : Nat := 4983230072969 + 3 ^ 40 * 3682565 * 2
def baseEnd_3682565 : Nat := 1260617257616326454134465

theorem tailTrace_3682565 : CollatzResearch.WordTrace tailWord_3682565 prefixEnd_3682565 1260617257616326454134465 := by
  unfold tailWord_3682565
  simp only [CollatzResearch.WordTrace]
  refine ⟨134314179903703411875273149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89542786602468941250182099 134314179903703411875273149)
  ·
    refine ⟨50367817463888779453227431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134314179903703411875273149 50367817463888779453227431)
    ·
      refine ⟨75551726195833169179841147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50367817463888779453227431 75551726195833169179841147)
      ·
        refine ⟨113327589293749753769761721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75551726195833169179841147 113327589293749753769761721)
        ·
          refine ⟨84995691970312315327321291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113327589293749753769761721 84995691970312315327321291)
          ·
            refine ⟨127493537955468472990981937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84995691970312315327321291 127493537955468472990981937)
            ·
              refine ⟨95620153466601354743236453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127493537955468472990981937 95620153466601354743236453)
              ·
                refine ⟨17928778774987754014356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95620153466601354743236453 17928778774987754014356835)
                ·
                  refine ⟨26893168162481631021535253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17928778774987754014356835 26893168162481631021535253)
                  ·
                    refine ⟨1260617257616326454134465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26893168162481631021535253 1260617257616326454134465)
                    ·
                      rfl

theorem cell22_3682565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_3682565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682565 prefixEnd_3682565 := by exact prefixLift 3682565
  have htrace : WordTrace (prefixWord ++ tailWord_3682565) baseStart_3682565 baseEnd_3682565 := by
    simpa [prefixWord, tailWord_3682565, baseEnd_3682565] using wordTrace_append hprefix tailTrace_3682565
  have hstable : (prefixWord ++ tailWord_3682565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682565).length < 2 ^ (prefixWord ++ tailWord_3682565).sum := by decide
  have hdescent : baseEnd_3682565 < baseStart_3682565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682597 : List Nat := [1, 3, 1, 2, 6, 9]
def baseStart_3682597 : Nat := 118140960795 + 3682597 * 2 ^ 59
def prefixEnd_3682597 : Nat := 4983230072969 + 3 ^ 40 * 3682597 * 2
def baseEnd_3682597 : Nat := 15563311257657889349807

theorem tailTrace_3682597 : CollatzResearch.WordTrace tailWord_3682597 prefixEnd_3682597 15563311257657889349807 := by
  unfold tailWord_3682597
  simp only [CollatzResearch.WordTrace]
  refine ⟨134315347039587481340438045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89543564693058320893625363 134315347039587481340438045)
  ·
    refine ⟨50368255139845305502664267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134315347039587481340438045 50368255139845305502664267)
    ·
      refine ⟨75552382709767958253996401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50368255139845305502664267 75552382709767958253996401)
      ·
        refine ⟨56664287032325968690497301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75552382709767958253996401 56664287032325968690497301)
        ·
          refine ⟨2656138454640279782367061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56664287032325968690497301 2656138454640279782367061)
          ·
            refine ⟨15563311257657889349807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2656138454640279782367061 15563311257657889349807)
            ·
              rfl

theorem cell22_3682597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 9].length) (baseStart_3682597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682597 prefixEnd_3682597 := by exact prefixLift 3682597
  have htrace : WordTrace (prefixWord ++ tailWord_3682597) baseStart_3682597 baseEnd_3682597 := by
    simpa [prefixWord, tailWord_3682597, baseEnd_3682597] using wordTrace_append hprefix tailTrace_3682597
  have hstable : (prefixWord ++ tailWord_3682597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682597).length < 2 ^ (prefixWord ++ tailWord_3682597).sum := by decide
  have hdescent : baseEnd_3682597 < baseStart_3682597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682719 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 4, 3]
def baseStart_3682719 : Nat := 118140960795 + 3682719 * 2 ^ 59
def prefixEnd_3682719 : Nat := 4983230072969 + 3 ^ 40 * 3682719 * 2
def baseEnd_3682719 : Nat := 1260669974963521385783993

theorem tailTrace_3682719 : CollatzResearch.WordTrace tailWord_3682719 prefixEnd_3682719 1260669974963521385783993 := by
  unfold tailWord_3682719
  simp only [CollatzResearch.WordTrace]
  refine ⟨134319796745145496176379211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89546531163430330784252807 134319796745145496176379211)
  ·
    refine ⟨201479695117718244264568817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134319796745145496176379211 201479695117718244264568817)
    ·
      refine ⟨151109771338288683198426613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201479695117718244264568817 151109771338288683198426613)
      ·
        refine ⟨14166541062964564049852495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151109771338288683198426613 14166541062964564049852495)
        ·
          refine ⟨21249811594446846074778743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166541062964564049852495 21249811594446846074778743)
          ·
            refine ⟨31874717391670269112168115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21249811594446846074778743 31874717391670269112168115)
            ·
              refine ⟨47812076087505403668252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31874717391670269112168115 47812076087505403668252173)
              ·
                refine ⟨17929528532814526375594565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47812076087505403668252173 17929528532814526375594565)
                ·
                  refine ⟨3361786599902723695423981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17929528532814526375594565 3361786599902723695423981)
                  ·
                    refine ⟨1260669974963521385783993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361786599902723695423981 1260669974963521385783993)
                    ·
                      rfl

theorem cell22_3682719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_3682719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682719 prefixEnd_3682719 := by exact prefixLift 3682719
  have htrace : WordTrace (prefixWord ++ tailWord_3682719) baseStart_3682719 baseEnd_3682719 := by
    simpa [prefixWord, tailWord_3682719, baseEnd_3682719] using wordTrace_append hprefix tailTrace_3682719
  have hstable : (prefixWord ++ tailWord_3682719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682719).length < 2 ^ (prefixWord ++ tailWord_3682719).sum := by decide
  have hdescent : baseEnd_3682719 < baseStart_3682719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682770 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_3682770 : Nat := 118140960795 + 3682770 * 2 ^ 59
def prefixEnd_3682770 : Nat := 4983230072969 + 3 ^ 40 * 3682770 * 2
def baseEnd_3682770 : Nat := 1260687433305774252758837

theorem tailTrace_3682770 : CollatzResearch.WordTrace tailWord_3682770 prefixEnd_3682770 1260687433305774252758837 := by
  unfold tailWord_3682770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580414216990182971621441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89547771245307154590990509 33580414216990182971621441)
  ·
    refine ⟨25185310662742637228716081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33580414216990182971621441 25185310662742637228716081)
    ·
      refine ⟨18888982997056977921537061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25185310662742637228716081 18888982997056977921537061)
      ·
        refine ⟨3541684311948183360288199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18888982997056977921537061 3541684311948183360288199)
        ·
          refine ⟨5312526467922275040432299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541684311948183360288199 5312526467922275040432299)
          ·
            refine ⟨7968789701883412560648449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312526467922275040432299 7968789701883412560648449)
            ·
              refine ⟨5976592276412559420486337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968789701883412560648449 5976592276412559420486337)
              ·
                refine ⟨4482444207309419565364753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976592276412559420486337 4482444207309419565364753)
                ·
                  refine ⟨3361833155482064674023565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4482444207309419565364753 3361833155482064674023565)
                  ·
                    refine ⟨1260687433305774252758837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361833155482064674023565 1260687433305774252758837)
                    ·
                      rfl

theorem cell22_3682770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_3682770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682770 prefixEnd_3682770 := by exact prefixLift 3682770
  have htrace : WordTrace (prefixWord ++ tailWord_3682770) baseStart_3682770 baseEnd_3682770 := by
    simpa [prefixWord, tailWord_3682770, baseEnd_3682770] using wordTrace_append hprefix tailTrace_3682770
  have hstable : (prefixWord ++ tailWord_3682770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682770).length < 2 ^ (prefixWord ++ tailWord_3682770).sum := by decide
  have hdescent : baseEnd_3682770 < baseStart_3682770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682781 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_3682781 : Nat := 118140960795 + 3682781 * 2 ^ 59
def prefixEnd_3682781 : Nat := 4983230072969 + 3 ^ 40 * 3682781 * 2
def baseEnd_3682781 : Nat := 1260691198830573890733803

theorem tailTrace_3682781 : CollatzResearch.WordTrace tailWord_3682781 prefixEnd_3682781 1260691198830573890733803 := by
  unfold tailWord_3682781
  simp only [CollatzResearch.WordTrace]
  refine ⟨134322058070920880765136197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89548038713947253843424131 134322058070920880765136197)
  ·
    refine ⟨25185385888297665143463037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134322058070920880765136197 25185385888297665143463037)
    ·
      refine ⟨9444519708111624428798639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25185385888297665143463037 9444519708111624428798639)
      ·
        refine ⟨14166779562167436643197959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444519708111624428798639 14166779562167436643197959)
        ·
          refine ⟨21250169343251154964796939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166779562167436643197959 21250169343251154964796939)
          ·
            refine ⟨31875254014876732447195409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250169343251154964796939 31875254014876732447195409)
            ·
              refine ⟨23906440511157549335396557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31875254014876732447195409 23906440511157549335396557)
              ·
                refine ⟨8964915191684081000773709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23906440511157549335396557 8964915191684081000773709)
                ·
                  refine ⟨3361843196881530375290141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8964915191684081000773709 3361843196881530375290141)
                  ·
                    refine ⟨1260691198830573890733803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361843196881530375290141 1260691198830573890733803)
                    ·
                      rfl

theorem cell22_3682781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_3682781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682781 prefixEnd_3682781 := by exact prefixLift 3682781
  have htrace : WordTrace (prefixWord ++ tailWord_3682781) baseStart_3682781 baseEnd_3682781 := by
    simpa [prefixWord, tailWord_3682781, baseEnd_3682781] using wordTrace_append hprefix tailTrace_3682781
  have hstable : (prefixWord ++ tailWord_3682781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682781).length < 2 ^ (prefixWord ++ tailWord_3682781).sum := by decide
  have hdescent : baseEnd_3682781 < baseStart_3682781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682856 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_3682856 : Nat := 118140960795 + 3682856 * 2 ^ 59
def prefixEnd_3682856 : Nat := 4983230072969 + 3 ^ 40 * 3682856 * 2
def baseEnd_3682856 : Nat := 420238957621099565036191

theorem tailTrace_3682856 : CollatzResearch.WordTrace tailWord_3682856 prefixEnd_3682856 420238957621099565036191 := by
  unfold tailWord_3682856
  simp only [CollatzResearch.WordTrace]
  refine ⟨67162396772824584287058211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89549862363766112382744281 67162396772824584287058211)
  ·
    refine ⟨100743595159236876430587317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67162396772824584287058211 100743595159236876430587317)
    ·
      refine ⟨9444712046178457165367561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100743595159236876430587317 9444712046178457165367561)
      ·
        refine ⟨7083534034633842874025671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9444712046178457165367561 7083534034633842874025671)
        ·
          refine ⟨10625301051950764311038507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083534034633842874025671 10625301051950764311038507)
          ·
            refine ⟨15937951577926146466557761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625301051950764311038507 15937951577926146466557761)
            ·
              refine ⟨11953463683444609849918321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15937951577926146466557761 11953463683444609849918321)
              ·
                refine ⟨8965097762583457387438741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11953463683444609849918321 8965097762583457387438741)
                ·
                  refine ⟨420238957621099565036191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8965097762583457387438741 420238957621099565036191)
                  ·
                    rfl

theorem cell22_3682856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_3682856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682856 prefixEnd_3682856 := by exact prefixLift 3682856
  have htrace : WordTrace (prefixWord ++ tailWord_3682856) baseStart_3682856 baseEnd_3682856 := by
    simpa [prefixWord, tailWord_3682856, baseEnd_3682856] using wordTrace_append hprefix tailTrace_3682856
  have hstable : (prefixWord ++ tailWord_3682856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682856).length < 2 ^ (prefixWord ++ tailWord_3682856).sum := by decide
  have hdescent : baseEnd_3682856 < baseStart_3682856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682858 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3682858 : Nat := 118140960795 + 3682858 * 2 ^ 59
def prefixEnd_3682858 : Nat := 4983230072969 + 3 ^ 40 * 3682858 * 2
def baseEnd_3682858 : Nat := 1260717557504171356558567

theorem tailTrace_3682858 : CollatzResearch.WordTrace tailWord_3682858 prefixEnd_3682858 1260717557504171356558567 := by
  unfold tailWord_3682858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33581216622910480728922307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89549910994427948610459485 33581216622910480728922307)
  ·
    refine ⟨50371824934365721093383461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33581216622910480728922307 50371824934365721093383461)
    ·
      refine ⟨9444717175193572705009399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50371824934365721093383461 9444717175193572705009399)
      ·
        refine ⟨14167075762790359057514099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444717175193572705009399 14167075762790359057514099)
        ·
          refine ⟨21250613644185538586271149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167075762790359057514099 21250613644185538586271149)
          ·
            refine ⟨7968980116569576969851681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21250613644185538586271149 7968980116569576969851681)
            ·
              refine ⟨5976735087427182727388761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968980116569576969851681 5976735087427182727388761)
              ·
                refine ⟨4482551315570387045541571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976735087427182727388761 4482551315570387045541571)
                ·
                  refine ⟨6723826973355580568312357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482551315570387045541571 6723826973355580568312357)
                  ·
                    refine ⟨1260717557504171356558567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6723826973355580568312357 1260717557504171356558567)
                    ·
                      rfl

theorem cell22_3682858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3682858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682858 prefixEnd_3682858 := by exact prefixLift 3682858
  have htrace : WordTrace (prefixWord ++ tailWord_3682858) baseStart_3682858 baseEnd_3682858 := by
    simpa [prefixWord, tailWord_3682858, baseEnd_3682858] using wordTrace_append hprefix tailTrace_3682858
  have hstable : (prefixWord ++ tailWord_3682858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682858).length < 2 ^ (prefixWord ++ tailWord_3682858).sum := by decide
  have hdescent : baseEnd_3682858 < baseStart_3682858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682869 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3682869 : Nat := 118140960795 + 3682869 * 2 ^ 59
def prefixEnd_3682869 : Nat := 4983230072969 + 3 ^ 40 * 3682869 * 2
def baseEnd_3682869 : Nat := 1260721323028970994533533

theorem tailTrace_3682869 : CollatzResearch.WordTrace tailWord_3682869 prefixEnd_3682869 1260721323028970994533533 := by
  unfold tailWord_3682869
  simp only [CollatzResearch.WordTrace]
  refine ⟨134325267694602071794339661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89550178463068047862893107 134325267694602071794339661)
  ·
    refine ⟨50371975385475776922877373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134325267694602071794339661 50371975385475776922877373)
    ·
      refine ⟨18889490769553416346079015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50371975385475776922877373 18889490769553416346079015)
      ·
        refine ⟨28334236154330124519118523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18889490769553416346079015 28334236154330124519118523)
        ·
          refine ⟨42501354231495186778677785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28334236154330124519118523 42501354231495186778677785)
          ·
            refine ⟨31876015673621390084008339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42501354231495186778677785 31876015673621390084008339)
            ·
              refine ⟨47814023510432085126012509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31876015673621390084008339 47814023510432085126012509)
              ·
                refine ⟨17930258816412031922254691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47814023510432085126012509 17930258816412031922254691)
                ·
                  refine ⟨26895388224618047883382037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930258816412031922254691 26895388224618047883382037)
                  ·
                    refine ⟨1260721323028970994533533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26895388224618047883382037 1260721323028970994533533)
                    ·
                      rfl

theorem cell22_3682869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3682869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682869 prefixEnd_3682869 := by exact prefixLift 3682869
  have htrace : WordTrace (prefixWord ++ tailWord_3682869) baseStart_3682869 baseEnd_3682869 := by
    simpa [prefixWord, tailWord_3682869, baseEnd_3682869] using wordTrace_append hprefix tailTrace_3682869
  have hstable : (prefixWord ++ tailWord_3682869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682869).length < 2 ^ (prefixWord ++ tailWord_3682869).sum := by decide
  have hdescent : baseEnd_3682869 < baseStart_3682869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682916 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_3682916 : Nat := 118140960795 + 3682916 * 2 ^ 59
def prefixEnd_3682916 : Nat := 4983230072969 + 3 ^ 40 * 3682916 * 2
def baseEnd_3682916 : Nat := 1260737412089478538608389

theorem tailTrace_3682916 : CollatzResearch.WordTrace tailWord_3682916 prefixEnd_3682916 1260737412089478538608389 := by
  unfold tailWord_3682916
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163490962715899410650301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89551321283621199214200401 67163490962715899410650301)
  ·
    refine ⟨25186309111018462278993863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67163490962715899410650301 25186309111018462278993863)
    ·
      refine ⟨37779463666527693418490795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25186309111018462278993863 37779463666527693418490795)
      ·
        refine ⟨56669195499791540127736193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37779463666527693418490795 56669195499791540127736193)
        ·
          refine ⟨42501896624843655095802145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56669195499791540127736193 42501896624843655095802145)
          ·
            refine ⟨31876422468632741321851609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42501896624843655095802145 31876422468632741321851609)
            ·
              refine ⟨23907316851474555991388707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31876422468632741321851609 23907316851474555991388707)
              ·
                refine ⟨35860975277211833987083061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23907316851474555991388707 35860975277211833987083061)
                ·
                  refine ⟨3361966432238609436289037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35860975277211833987083061 3361966432238609436289037)
                  ·
                    refine ⟨1260737412089478538608389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361966432238609436289037 1260737412089478538608389)
                    ·
                      rfl

theorem cell22_3682916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_3682916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3682916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3682916 prefixEnd_3682916 := by exact prefixLift 3682916
  have htrace : WordTrace (prefixWord ++ tailWord_3682916) baseStart_3682916 baseEnd_3682916 := by
    simpa [prefixWord, tailWord_3682916, baseEnd_3682916] using wordTrace_append hprefix tailTrace_3682916
  have hstable : (prefixWord ++ tailWord_3682916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682916).length < 2 ^ (prefixWord ++ tailWord_3682916).sum := by decide
  have hdescent : baseEnd_3682916 < baseStart_3682916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683008 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_3683008 : Nat := 118140960795 + 3683008 * 2 ^ 59
def prefixEnd_3683008 : Nat := 4983230072969 + 3 ^ 40 * 3683008 * 2
def baseEnd_3683008 : Nat := 420256301856540321769369

theorem tailTrace_3683008 : CollatzResearch.WordTrace tailWord_3683008 prefixEnd_3683008 420256301856540321769369 := by
  unfold tailWord_3683008
  simp only [CollatzResearch.WordTrace]
  refine ⟨67165168720549249266824839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89553558294065665689099785 67165168720549249266824839)
  ·
    refine ⟨100747753080823873900237259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67165168720549249266824839 100747753080823873900237259)
    ·
      refine ⟨151121629621235810850355889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100747753080823873900237259 151121629621235810850355889)
      ·
        refine ⟨113341222215926858137766917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151121629621235810850355889 113341222215926858137766917)
        ·
          refine ⟨21251479165486285900831297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113341222215926858137766917 21251479165486285900831297)
          ·
            refine ⟨15938609374114714425623473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21251479165486285900831297 15938609374114714425623473)
            ·
              refine ⟨11953957030586035819217605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15938609374114714425623473 11953957030586035819217605)
              ·
                refine ⟨2241366943234881716103301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11953957030586035819217605 2241366943234881716103301)
                ·
                  refine ⟨420256301856540321769369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241366943234881716103301 420256301856540321769369)
                  ·
                    rfl

theorem cell22_3683008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_3683008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683008 prefixEnd_3683008 := by exact prefixLift 3683008
  have htrace : WordTrace (prefixWord ++ tailWord_3683008) baseStart_3683008 baseEnd_3683008 := by
    simpa [prefixWord, tailWord_3683008, baseEnd_3683008] using wordTrace_append hprefix tailTrace_3683008
  have hstable : (prefixWord ++ tailWord_3683008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683008).length < 2 ^ (prefixWord ++ tailWord_3683008).sum := by decide
  have hdescent : baseEnd_3683008 < baseStart_3683008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683014 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3683014 : Nat := 118140960795 + 3683014 * 2 ^ 59
def prefixEnd_3683014 : Nat := 4983230072969 + 3 ^ 40 * 3683014 * 2
def baseEnd_3683014 : Nat := 420256986497412983219363

theorem tailTrace_3683014 : CollatzResearch.WordTrace tailWord_3683014 prefixEnd_3683014 420256986497412983219363 := by
  unfold tailWord_3683014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197829883721148798699003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89553704186051174372245397 4197829883721148798699003)
  ·
    refine ⟨6296744825581723198048505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197829883721148798699003 6296744825581723198048505)
    ·
      refine ⟨4722558619186292398536379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6296744825581723198048505 4722558619186292398536379)
      ·
        refine ⟨7083837928779438597804569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722558619186292398536379 7083837928779438597804569)
        ·
          refine ⟨5312878446584578948353427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083837928779438597804569 5312878446584578948353427)
          ·
            refine ⟨7969317669876868422530141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312878446584578948353427 7969317669876868422530141)
            ·
              refine ⟨2988494126203825658448803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7969317669876868422530141 2988494126203825658448803)
              ·
                refine ⟨4482741189305738487673205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988494126203825658448803 4482741189305738487673205)
                ·
                  refine ⟨420256986497412983219363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482741189305738487673205 420256986497412983219363)
                  ·
                    rfl

theorem cell22_3683014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3683014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683014 prefixEnd_3683014 := by exact prefixLift 3683014
  have htrace : WordTrace (prefixWord ++ tailWord_3683014) baseStart_3683014 baseEnd_3683014 := by
    simpa [prefixWord, tailWord_3683014, baseEnd_3683014] using wordTrace_append hprefix tailTrace_3683014
  have hstable : (prefixWord ++ tailWord_3683014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683014).length < 2 ^ (prefixWord ++ tailWord_3683014).sum := by decide
  have hdescent : baseEnd_3683014 < baseStart_3683014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683074 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3683074 : Nat := 118140960795 + 3683074 * 2 ^ 59
def prefixEnd_3683074 : Nat := 4983230072969 + 3 ^ 40 * 3683074 * 2
def baseEnd_3683074 : Nat := 1260791498718418793157905

theorem tailTrace_3683074 : CollatzResearch.WordTrace tailWord_3683074 prefixEnd_3683074 1260791498718418793157905 := by
  unfold tailWord_3683074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33583186164714847951388069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89555163105906261203701517 33583186164714847951388069)
  ·
    refine ⟨6296847405884033990885263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33583186164714847951388069 6296847405884033990885263)
    ·
      refine ⟨9445271108826050986327895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296847405884033990885263 9445271108826050986327895)
      ·
        refine ⟨14167906663239076479491843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445271108826050986327895 14167906663239076479491843)
        ·
          refine ⟨21251859994858614719237765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167906663239076479491843 21251859994858614719237765)
          ·
            refine ⟨3984723749035990259857081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21251859994858614719237765 3984723749035990259857081)
            ·
              refine ⟨2988542811776992694892811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984723749035990259857081 2988542811776992694892811)
              ·
                refine ⟨4482814217665489042339217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988542811776992694892811 4482814217665489042339217)
                ·
                  refine ⟨3362110663249116781754413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4482814217665489042339217 3362110663249116781754413)
                  ·
                    refine ⟨1260791498718418793157905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362110663249116781754413 1260791498718418793157905)
                    ·
                      rfl

theorem cell22_3683074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3683074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683074 prefixEnd_3683074 := by exact prefixLift 3683074
  have htrace : WordTrace (prefixWord ++ tailWord_3683074) baseStart_3683074 baseEnd_3683074 := by
    simpa [prefixWord, tailWord_3683074, baseEnd_3683074] using wordTrace_append hprefix tailTrace_3683074
  have hstable : (prefixWord ++ tailWord_3683074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683074).length < 2 ^ (prefixWord ++ tailWord_3683074).sum := by decide
  have hdescent : baseEnd_3683074 < baseStart_3683074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683096 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_3683096 : Nat := 118140960795 + 3683096 * 2 ^ 59
def prefixEnd_3683096 : Nat := 4983230072969 + 3 ^ 40 * 3683096 * 2
def baseEnd_3683096 : Nat := 1260799029768018069107837

theorem tailTrace_3683096 : CollatzResearch.WordTrace tailWord_3683096 prefixEnd_3683096 1260799029768018069107837 := by
  unfold tailWord_3683096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67166773532389844781426571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89555698043186459708568761 67166773532389844781426571)
  ·
    refine ⟨100750160298584767172139857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67166773532389844781426571 100750160298584767172139857)
    ·
      refine ⟨75562620223938575379104893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100750160298584767172139857 75562620223938575379104893)
      ·
        refine ⟨28335982583976965767164335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75562620223938575379104893 28335982583976965767164335)
        ·
          refine ⟨42503973875965448650746503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28335982583976965767164335 42503973875965448650746503)
          ·
            refine ⟨63755960813948172976119755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42503973875965448650746503 63755960813948172976119755)
            ·
              refine ⟨95633941220922259464179633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63755960813948172976119755 95633941220922259464179633)
              ·
                refine ⟨71725455915691694598134725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95633941220922259464179633 71725455915691694598134725)
                ·
                  refine ⟨13448522984192192737150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71725455915691694598134725 13448522984192192737150261)
                  ·
                    refine ⟨1260799029768018069107837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13448522984192192737150261 1260799029768018069107837)
                    ·
                      rfl

theorem cell22_3683096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_3683096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683096 prefixEnd_3683096 := by exact prefixLift 3683096
  have htrace : WordTrace (prefixWord ++ tailWord_3683096) baseStart_3683096 baseEnd_3683096 := by
    simpa [prefixWord, tailWord_3683096, baseEnd_3683096] using wordTrace_append hprefix tailTrace_3683096
  have hstable : (prefixWord ++ tailWord_3683096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683096).length < 2 ^ (prefixWord ++ tailWord_3683096).sum := by decide
  have hdescent : baseEnd_3683096 < baseStart_3683096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
