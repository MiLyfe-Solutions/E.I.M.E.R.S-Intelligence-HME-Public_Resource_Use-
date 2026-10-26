import V185TrunkScan22Chunk292

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2614040 : List Nat := [2, 1, 2, 3, 1, 1, 1, 11]
def baseStart_2614040 : Nat := 118140960795 + 2614040 * 2 ^ 59
def prefixEnd_2614040 : Nat := 4983230072969 + 3 ^ 40 * 2614040 * 2
def baseEnd_2614040 : Nat := 99426590376226502976167

theorem tailTrace_2614040 : CollatzResearch.WordTrace tailWord_2614040 prefixEnd_2614040 99426590376226502976167 := by
  unfold tailWord_2614040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47670935724893498667003787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63561247633191331556005049 47670935724893498667003787)
  ·
    refine ⟨71506403587340248000505681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47670935724893498667003787 71506403587340248000505681)
    ·
      refine ⟨53629802690505186000379261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71506403587340248000505681 53629802690505186000379261)
      ·
        refine ⟨20111176008939444750142223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53629802690505186000379261 20111176008939444750142223)
        ·
          refine ⟨30166764013409167125213335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111176008939444750142223 30166764013409167125213335)
          ·
            refine ⟨45250146020113750687820003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30166764013409167125213335 45250146020113750687820003)
            ·
              refine ⟨67875219030170626031730005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45250146020113750687820003 67875219030170626031730005)
              ·
                refine ⟨99426590376226502976167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67875219030170626031730005 99426590376226502976167)
                ·
                  rfl

theorem cell22_2614040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_2614040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614040 prefixEnd_2614040 := by exact prefixLift 2614040
  have htrace : WordTrace (prefixWord ++ tailWord_2614040) baseStart_2614040 baseEnd_2614040 := by
    simpa [prefixWord, tailWord_2614040, baseEnd_2614040] using wordTrace_append hprefix tailTrace_2614040
  have hstable : (prefixWord ++ tailWord_2614040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614040).length < 2 ^ (prefixWord ++ tailWord_2614040).sum := by decide
  have hdescent : baseEnd_2614040 < baseStart_2614040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614044 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2614044 : Nat := 118140960795 + 2614044 * 2 ^ 59
def prefixEnd_2614044 : Nat := 4983230072969 + 3 ^ 40 * 2614044 * 2
def baseEnd_2614044 : Nat := 894840682667783849685491

theorem tailTrace_2614044 : CollatzResearch.WordTrace tailWord_2614044 prefixEnd_2614044 894840682667783849685491 := by
  unfold tailWord_2614044
  simp only [CollatzResearch.WordTrace]
  refine ⟨47671008670886253008576593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63561344894515004011435457 47671008670886253008576593)
  ·
    refine ⟨35753256503164689756432445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47671008670886253008576593 35753256503164689756432445)
    ·
      refine ⟨13407471188686758658662167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35753256503164689756432445 13407471188686758658662167)
      ·
        refine ⟨20111206783030137987993251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13407471188686758658662167 20111206783030137987993251)
        ·
          refine ⟨30166810174545206981989877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111206783030137987993251 30166810174545206981989877)
          ·
            refine ⟨2828138453863613154561551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30166810174545206981989877 2828138453863613154561551)
            ·
              refine ⟨4242207680795419731842327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828138453863613154561551 4242207680795419731842327)
              ·
                refine ⟨6363311521193129597763491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242207680795419731842327 6363311521193129597763491)
                ·
                  refine ⟨9544967281789694396645237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363311521193129597763491 9544967281789694396645237)
                  ·
                    refine ⟨894840682667783849685491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9544967281789694396645237 894840682667783849685491)
                    ·
                      rfl

theorem cell22_2614044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2614044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614044 prefixEnd_2614044 := by exact prefixLift 2614044
  have htrace : WordTrace (prefixWord ++ tailWord_2614044) baseStart_2614044 baseEnd_2614044 := by
    simpa [prefixWord, tailWord_2614044, baseEnd_2614044] using wordTrace_append hprefix tailTrace_2614044
  have hstable : (prefixWord ++ tailWord_2614044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614044).length < 2 ^ (prefixWord ++ tailWord_2614044).sum := by decide
  have hdescent : baseEnd_2614044 < baseStart_2614044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614074 : List Nat := [3, 1, 1, 1, 7, 1, 8]
def baseStart_2614074 : Nat := 118140960795 + 2614074 * 2 ^ 59
def prefixEnd_2614074 : Nat := 4983230072969 + 3 ^ 40 * 2614074 * 2
def baseEnd_2614074 : Nat := 33142627862254584127237

theorem tailTrace_2614074 : CollatzResearch.WordTrace tailWord_2614074 prefixEnd_2614074 33142627862254584127237 := by
  unfold tailWord_2614074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23835777882915955285186319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63562074354442547427163517 23835777882915955285186319)
  ·
    refine ⟨35753666824373932927779479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23835777882915955285186319 35753666824373932927779479)
    ·
      refine ⟨53630500236560899391669219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35753666824373932927779479 53630500236560899391669219)
      ·
        refine ⟨80445750354841349087503829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53630500236560899391669219 80445750354841349087503829)
        ·
          refine ⟨1885447273941594119238371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80445750354841349087503829 1885447273941594119238371)
          ·
            refine ⟨2828170910912391178857557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885447273941594119238371 2828170910912391178857557)
            ·
              refine ⟨33142627862254584127237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2828170910912391178857557 33142627862254584127237)
              ·
                rfl

theorem cell22_2614074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 8].length) (baseStart_2614074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614074 prefixEnd_2614074 := by exact prefixLift 2614074
  have htrace : WordTrace (prefixWord ++ tailWord_2614074) baseStart_2614074 baseEnd_2614074 := by
    simpa [prefixWord, tailWord_2614074, baseEnd_2614074] using wordTrace_append hprefix tailTrace_2614074
  have hstable : (prefixWord ++ tailWord_2614074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614074).length < 2 ^ (prefixWord ++ tailWord_2614074).sum := by decide
  have hdescent : baseEnd_2614074 < baseStart_2614074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614089 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_2614089 : Nat := 118140960795 + 2614089 * 2 ^ 59
def prefixEnd_2614089 : Nat := 4983230072969 + 3 ^ 40 * 2614089 * 2
def baseEnd_2614089 : Nat := 894856087087418732310353

theorem tailTrace_2614089 : CollatzResearch.WordTrace tailWord_2614089 prefixEnd_2614089 894856087087418732310353 := by
  unfold tailWord_2614089
  simp only [CollatzResearch.WordTrace]
  refine ⟨95343658626609478702541321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63562439084406319135027547 95343658626609478702541321)
  ·
    refine ⟨71507743969957109026905991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95343658626609478702541321 71507743969957109026905991)
    ·
      refine ⟨107261615954935663540358987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71507743969957109026905991 107261615954935663540358987)
      ·
        refine ⟨160892423932403495310538481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107261615954935663540358987 160892423932403495310538481)
        ·
          refine ⟨120669317949302621482903861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160892423932403495310538481 120669317949302621482903861)
          ·
            refine ⟨11312748557747120764022237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120669317949302621482903861 11312748557747120764022237)
            ·
              refine ⟨4242280709155170286508339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11312748557747120764022237 4242280709155170286508339)
              ·
                refine ⟨6363421063732755429762509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242280709155170286508339 6363421063732755429762509)
                ·
                  refine ⟨2386282898899783286160941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6363421063732755429762509 2386282898899783286160941)
                  ·
                    refine ⟨894856087087418732310353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386282898899783286160941 894856087087418732310353)
                    ·
                      rfl

theorem cell22_2614089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_2614089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614089 prefixEnd_2614089 := by exact prefixLift 2614089
  have htrace : WordTrace (prefixWord ++ tailWord_2614089) baseStart_2614089 baseEnd_2614089 := by
    simpa [prefixWord, tailWord_2614089, baseEnd_2614089] using wordTrace_append hprefix tailTrace_2614089
  have hstable : (prefixWord ++ tailWord_2614089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614089).length < 2 ^ (prefixWord ++ tailWord_2614089).sum := by decide
  have hdescent : baseEnd_2614089 < baseStart_2614089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614147 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 6]
def baseStart_2614147 : Nat := 118140960795 + 2614147 * 2 ^ 59
def prefixEnd_2614147 : Nat := 4983230072969 + 3 ^ 40 * 2614147 * 2
def baseEnd_2614147 : Nat := 298291980557575304786725

theorem tailTrace_2614147 : CollatzResearch.WordTrace tailWord_2614147 prefixEnd_2614147 298291980557575304786725 := by
  unfold tailWord_2614147
  simp only [CollatzResearch.WordTrace]
  refine ⟨95345774060399354608152695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63563849373599569738768463 95345774060399354608152695)
  ·
    refine ⟨143018661090599031912229043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95345774060399354608152695 143018661090599031912229043)
    ·
      refine ⟨214527991635898547868343565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143018661090599031912229043 214527991635898547868343565)
      ·
        refine ⟨80447996863461955450628837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214527991635898547868343565 80447996863461955450628837)
        ·
          refine ⟨15083999411899116646992907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80447996863461955450628837 15083999411899116646992907)
          ·
            refine ⟨22625999117848674970489361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15083999411899116646992907 22625999117848674970489361)
            ·
              refine ⟨16969499338386506227867021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22625999117848674970489361 16969499338386506227867021)
              ·
                refine ⟨6363562251894939835450133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16969499338386506227867021 6363562251894939835450133)
                ·
                  refine ⟨298291980557575304786725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6363562251894939835450133 298291980557575304786725)
                  ·
                    rfl

theorem cell22_2614147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_2614147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614147 prefixEnd_2614147 := by exact prefixLift 2614147
  have htrace : WordTrace (prefixWord ++ tailWord_2614147) baseStart_2614147 baseEnd_2614147 := by
    simpa [prefixWord, tailWord_2614147, baseEnd_2614147] using wordTrace_append hprefix tailTrace_2614147
  have hstable : (prefixWord ++ tailWord_2614147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614147).length < 2 ^ (prefixWord ++ tailWord_2614147).sum := by decide
  have hdescent : baseEnd_2614147 < baseStart_2614147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614164 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_2614164 : Nat := 118140960795 + 2614164 * 2 ^ 59
def prefixEnd_2614164 : Nat := 4983230072969 + 3 ^ 40 * 2614164 * 2
def baseEnd_2614164 : Nat := 298293920373381178895041

theorem tailTrace_2614164 : CollatzResearch.WordTrace tailWord_2614164 prefixEnd_2614164 298293920373381178895041 := by
  unfold tailWord_2614164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47673197050668883255760773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63564262734225177674347697 47673197050668883255760773)
  ·
    refine ⟨8938724447000415610455145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47673197050668883255760773 8938724447000415610455145)
    ·
      refine ⟨6704043335250311707841359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8938724447000415610455145 6704043335250311707841359)
      ·
        refine ⟨10056065002875467561762039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6704043335250311707841359 10056065002875467561762039)
        ·
          refine ⟨15084097504313201342643059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10056065002875467561762039 15084097504313201342643059)
          ·
            refine ⟨22626146256469802013964589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15084097504313201342643059 22626146256469802013964589)
            ·
              refine ⟨8484804846176175755236721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22626146256469802013964589 8484804846176175755236721)
              ·
                refine ⟨6363603634632131816427541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8484804846176175755236721 6363603634632131816427541)
                ·
                  refine ⟨298293920373381178895041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6363603634632131816427541 298293920373381178895041)
                  ·
                    rfl

theorem cell22_2614164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_2614164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614164 prefixEnd_2614164 := by exact prefixLift 2614164
  have htrace : WordTrace (prefixWord ++ tailWord_2614164) baseStart_2614164 baseEnd_2614164 := by
    simpa [prefixWord, tailWord_2614164, baseEnd_2614164] using wordTrace_append hprefix tailTrace_2614164
  have hstable : (prefixWord ++ tailWord_2614164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614164).length < 2 ^ (prefixWord ++ tailWord_2614164).sum := by decide
  have hdescent : baseEnd_2614164 < baseStart_2614164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614226 : List Nat := [3, 2, 2, 3, 1, 1, 4, 6]
def baseStart_2614226 : Nat := 118140960795 + 2614226 * 2 ^ 59
def prefixEnd_2614226 : Nat := 4983230072969 + 3 ^ 40 * 2614226 * 2
def baseEnd_2614226 : Nat := 99433664998577337959437

theorem tailTrace_2614226 : CollatzResearch.WordTrace tailWord_2614226 prefixEnd_2614226 99433664998577337959437 := by
  unfold tailWord_2614226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837163856778287775069633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63565770284742100733519021 23837163856778287775069633)
  ·
    refine ⟨17877872892583715831302225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23837163856778287775069633 17877872892583715831302225)
    ·
      refine ⟨13408404669437786873476669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17877872892583715831302225 13408404669437786873476669)
      ·
        refine ⟨5028151751039170077553751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13408404669437786873476669 5028151751039170077553751)
        ·
          refine ⟨7542227626558755116330627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028151751039170077553751 7542227626558755116330627)
          ·
            refine ⟨11313341439838132674495941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542227626558755116330627 11313341439838132674495941)
            ·
              refine ⟨2121251519969649876467989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11313341439838132674495941 2121251519969649876467989)
              ·
                refine ⟨99433664998577337959437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2121251519969649876467989 99433664998577337959437)
                ·
                  rfl

theorem cell22_2614226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_2614226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614226 prefixEnd_2614226 := by exact prefixLift 2614226
  have htrace : WordTrace (prefixWord ++ tailWord_2614226) baseStart_2614226 baseEnd_2614226 := by
    simpa [prefixWord, tailWord_2614226, baseEnd_2614226] using wordTrace_append hprefix tailTrace_2614226
  have hstable : (prefixWord ++ tailWord_2614226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614226).length < 2 ^ (prefixWord ++ tailWord_2614226).sum := by decide
  have hdescent : baseEnd_2614226 < baseStart_2614226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614267 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_2614267 : Nat := 118140960795 + 2614267 * 2 ^ 59
def prefixEnd_2614267 : Nat := 4983230072969 + 3 ^ 40 * 2614267 * 2
def baseEnd_2614267 : Nat := 894917020125085601359807

theorem tailTrace_2614267 : CollatzResearch.WordTrace tailWord_2614267 prefixEnd_2614267 894917020125085601359807 := by
  unfold tailWord_2614267
  simp only [CollatzResearch.WordTrace]
  refine ⟨95350150819964615102521055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63566767213309743401680703 95350150819964615102521055)
  ·
    refine ⟨143025226229946922653781583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95350150819964615102521055 143025226229946922653781583)
    ·
      refine ⟨214537839344920383980672375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143025226229946922653781583 214537839344920383980672375)
      ·
        refine ⟨321806759017380575971008563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214537839344920383980672375 321806759017380575971008563)
        ·
          refine ⟨482710138526070863956512845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321806759017380575971008563 482710138526070863956512845)
          ·
            refine ⟨181016301947276573983692317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482710138526070863956512845 181016301947276573983692317)
            ·
              refine ⟨67881113230228715243884619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181016301947276573983692317 67881113230228715243884619)
              ·
                refine ⟨101821669845343072865826929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67881113230228715243884619 101821669845343072865826929)
                ·
                  refine ⟨76366252384007304649370197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101821669845343072865826929 76366252384007304649370197)
                  ·
                    refine ⟨894917020125085601359807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76366252384007304649370197 894917020125085601359807)
                    ·
                      rfl

theorem cell22_2614267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_2614267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614267 prefixEnd_2614267 := by exact prefixLift 2614267
  have htrace : WordTrace (prefixWord ++ tailWord_2614267) baseStart_2614267 baseEnd_2614267 := by
    simpa [prefixWord, tailWord_2614267, baseEnd_2614267] using wordTrace_append hprefix tailTrace_2614267
  have hstable : (prefixWord ++ tailWord_2614267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614267).length < 2 ^ (prefixWord ++ tailWord_2614267).sum := by decide
  have hdescent : baseEnd_2614267 < baseStart_2614267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614316 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_2614316 : Nat := 118140960795 + 2614316 * 2 ^ 59
def prefixEnd_2614316 : Nat := 4983230072969 + 3 ^ 40 * 2614316 * 2
def baseEnd_2614316 : Nat := 298311264608821935628219

theorem tailTrace_2614316 : CollatzResearch.WordTrace tailWord_2614316 prefixEnd_2614316 298311264608821935628219 := by
  unfold tailWord_2614316
  simp only [CollatzResearch.WordTrace]
  refine ⟨47675968998393548235527401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63567958664524730980703201 47675968998393548235527401)
  ·
    refine ⟨35756976748795161176645551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47675968998393548235527401 35756976748795161176645551)
    ·
      refine ⟨53635465123192741764968327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35756976748795161176645551 53635465123192741764968327)
      ·
        refine ⟨80453197684789112647452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53635465123192741764968327 80453197684789112647452491)
        ·
          refine ⟨120679796527183668971178737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80453197684789112647452491 120679796527183668971178737)
          ·
            refine ⟨90509847395387751728384053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120679796527183668971178737 90509847395387751728384053)
            ·
              refine ⟨8485298193317601724536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90509847395387751728384053 8485298193317601724536005)
              ·
                refine ⟨1590993411247050323350501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8485298193317601724536005 1590993411247050323350501)
                ·
                  refine ⟨298311264608821935628219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590993411247050323350501 298311264608821935628219)
                  ·
                    rfl

theorem cell22_2614316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_2614316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614316 prefixEnd_2614316 := by exact prefixLift 2614316
  have htrace : WordTrace (prefixWord ++ tailWord_2614316) baseStart_2614316 baseEnd_2614316 := by
    simpa [prefixWord, tailWord_2614316, baseEnd_2614316] using wordTrace_append hprefix tailTrace_2614316
  have hstable : (prefixWord ++ tailWord_2614316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614316).length < 2 ^ (prefixWord ++ tailWord_2614316).sum := by decide
  have hdescent : baseEnd_2614316 < baseStart_2614316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614346 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_2614346 : Nat := 118140960795 + 2614346 * 2 ^ 59
def prefixEnd_2614346 : Nat := 4983230072969 + 3 ^ 40 * 2614346 * 2
def baseEnd_2614346 : Nat := 894944063439555728634565

theorem tailTrace_2614346 : CollatzResearch.WordTrace tailWord_2614346 prefixEnd_2614346 894944063439555728634565 := by
  unfold tailWord_2614346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838258046669602898661723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63568688124452274396431261 23838258046669602898661723)
  ·
    refine ⟨35757387070004404347992585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23838258046669602898661723 35757387070004404347992585)
    ·
      refine ⟨26818040302503303260994439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35757387070004404347992585 26818040302503303260994439)
      ·
        refine ⟨40227060453754954891491659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26818040302503303260994439 40227060453754954891491659)
        ·
          refine ⟨60340590680632432337237489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40227060453754954891491659 60340590680632432337237489)
          ·
            refine ⟨45255443010474324252928117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60340590680632432337237489 45255443010474324252928117)
            ·
              refine ⟨4242697782231967898712011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45255443010474324252928117 4242697782231967898712011)
              ·
                refine ⟨6364046673347951848068017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242697782231967898712011 6364046673347951848068017)
                ·
                  refine ⟨4773035005010963886051013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364046673347951848068017 4773035005010963886051013)
                  ·
                    refine ⟨894944063439555728634565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773035005010963886051013 894944063439555728634565)
                    ·
                      rfl

theorem cell22_2614346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_2614346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614346 prefixEnd_2614346 := by exact prefixLift 2614346
  have htrace : WordTrace (prefixWord ++ tailWord_2614346) baseStart_2614346 baseEnd_2614346 := by
    simpa [prefixWord, tailWord_2614346, baseEnd_2614346] using wordTrace_append hprefix tailTrace_2614346
  have hstable : (prefixWord ++ tailWord_2614346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614346).length < 2 ^ (prefixWord ++ tailWord_2614346).sum := by decide
  have hdescent : baseEnd_2614346 < baseStart_2614346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614365 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2614365 : Nat := 118140960795 + 2614365 * 2 ^ 59
def prefixEnd_2614365 : Nat := 4983230072969 + 3 ^ 40 * 2614365 * 2
def baseEnd_2614365 : Nat := 894950567527846012409507

theorem tailTrace_2614365 : CollatzResearch.WordTrace tailWord_2614365 prefixEnd_2614365 894950567527846012409507 := by
  unfold tailWord_2614365
  simp only [CollatzResearch.WordTrace]
  refine ⟨95353725173609577839588549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63569150115739718559725699 95353725173609577839588549)
  ·
    refine ⟨17878823470051795844922853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95353725173609577839588549 17878823470051795844922853)
    ·
      refine ⟨3352279400634711720923035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17878823470051795844922853 3352279400634711720923035)
      ·
        refine ⟨5028419100952067581384553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352279400634711720923035 5028419100952067581384553)
        ·
          refine ⟨3771314325714050686038415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5028419100952067581384553 3771314325714050686038415)
          ·
            refine ⟨5656971488571076029057623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771314325714050686038415 5656971488571076029057623)
            ·
              refine ⟨8485457232856614043586435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656971488571076029057623 8485457232856614043586435)
              ·
                refine ⟨12728185849284921065379653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8485457232856614043586435 12728185849284921065379653)
                ·
                  refine ⟨2386534846740922699758685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12728185849284921065379653 2386534846740922699758685)
                  ·
                    refine ⟨894950567527846012409507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386534846740922699758685 894950567527846012409507)
                    ·
                      rfl

theorem cell22_2614365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2614365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614365 prefixEnd_2614365 := by exact prefixLift 2614365
  have htrace : WordTrace (prefixWord ++ tailWord_2614365) baseStart_2614365 baseEnd_2614365 := by
    simpa [prefixWord, tailWord_2614365, baseEnd_2614365] using wordTrace_append hprefix tailTrace_2614365
  have hstable : (prefixWord ++ tailWord_2614365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614365).length < 2 ^ (prefixWord ++ tailWord_2614365).sum := by decide
  have hdescent : baseEnd_2614365 < baseStart_2614365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614485 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 4]
def baseStart_2614485 : Nat := 118140960795 + 2614485 * 2 ^ 59
def prefixEnd_2614485 : Nat := 4983230072969 + 3 ^ 40 * 2614485 * 2
def baseEnd_2614485 : Nat := 298330548660068566469713

theorem tailTrace_2614485 : CollatzResearch.WordTrace tailWord_2614485 prefixEnd_2614485 298330548660068566469713 := by
  unfold tailWord_2614485
  simp only [CollatzResearch.WordTrace]
  refine ⟨95358101933174838333956909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63572067955449892222637939 95358101933174838333956909)
  ·
    refine ⟨35759288224940564375233841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95358101933174838333956909 35759288224940564375233841)
    ·
      refine ⟨26819466168705423281425381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35759288224940564375233841 26819466168705423281425381)
      ·
        refine ⟨5028649906632266865267259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26819466168705423281425381 5028649906632266865267259)
        ·
          refine ⟨7542974859948400297900889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028649906632266865267259 7542974859948400297900889)
          ·
            refine ⟨5657231144961300223425667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7542974859948400297900889 5657231144961300223425667)
            ·
              refine ⟨8485846717441950335138501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657231144961300223425667 8485846717441950335138501)
              ·
                refine ⟨1591096259520365687838469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8485846717441950335138501 1591096259520365687838469)
                ·
                  refine ⟨298330548660068566469713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591096259520365687838469 298330548660068566469713)
                  ·
                    rfl

theorem cell22_2614485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_2614485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614485 prefixEnd_2614485 := by exact prefixLift 2614485
  have htrace : WordTrace (prefixWord ++ tailWord_2614485) baseStart_2614485 baseEnd_2614485 := by
    simpa [prefixWord, tailWord_2614485, baseEnd_2614485] using wordTrace_append hprefix tailTrace_2614485
  have hstable : (prefixWord ++ tailWord_2614485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614485).length < 2 ^ (prefixWord ++ tailWord_2614485).sum := by decide
  have hdescent : baseEnd_2614485 < baseStart_2614485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614496 : List Nat := [2, 1, 1, 3, 1, 4, 3, 7]
def baseStart_2614496 : Nat := 118140960795 + 2614496 * 2 ^ 59
def prefixEnd_2614496 : Nat := 4983230072969 + 3 ^ 40 * 2614496 * 2
def baseEnd_2614496 : Nat := 99443934611667259709345

theorem tailTrace_2614496 : CollatzResearch.WordTrace tailWord_2614496 prefixEnd_2614496 99443934611667259709345 := by
  unfold tailWord_2614496
  simp only [CollatzResearch.WordTrace]
  refine ⟨47679251568067493606303671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63572335424089991475071561 47679251568067493606303671)
  ·
    refine ⟨71518877352101240409455507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47679251568067493606303671 71518877352101240409455507)
    ·
      refine ⟨107278316028151860614183261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71518877352101240409455507 107278316028151860614183261)
      ·
        refine ⟨40229368510556947730318723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107278316028151860614183261 40229368510556947730318723)
        ·
          refine ⟨60344052765835421595478085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40229368510556947730318723 60344052765835421595478085)
          ·
            refine ⟨11314509893594141549152141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60344052765835421595478085 11314509893594141549152141)
            ·
              refine ⟨4242941210097803080932053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11314509893594141549152141 4242941210097803080932053)
              ·
                refine ⟨99443934611667259709345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4242941210097803080932053 99443934611667259709345)
                ·
                  rfl

theorem cell22_2614496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_2614496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614496 prefixEnd_2614496 := by exact prefixLift 2614496
  have htrace : WordTrace (prefixWord ++ tailWord_2614496) baseStart_2614496 baseEnd_2614496 := by
    simpa [prefixWord, tailWord_2614496, baseEnd_2614496] using wordTrace_append hprefix tailTrace_2614496
  have hstable : (prefixWord ++ tailWord_2614496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614496).length < 2 ^ (prefixWord ++ tailWord_2614496).sum := by decide
  have hdescent : baseEnd_2614496 < baseStart_2614496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614545 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2614545 : Nat := 118140960795 + 2614545 * 2 ^ 59
def prefixEnd_2614545 : Nat := 4983230072969 + 3 ^ 40 * 2614545 * 2
def baseEnd_2614545 : Nat := 895012185206385542908955

theorem tailTrace_2614545 : CollatzResearch.WordTrace tailWord_2614545 prefixEnd_2614545 895012185206385542908955 := by
  unfold tailWord_2614545
  simp only [CollatzResearch.WordTrace]
  refine ⟨95360290312957468581141089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63573526875304979054094059 95360290312957468581141089)
  ·
    refine ⟨71520217734718101435855817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95360290312957468581141089 71520217734718101435855817)
    ·
      refine ⟨53640163301038576076891863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71520217734718101435855817 53640163301038576076891863)
      ·
        refine ⟨80460244951557864115337795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53640163301038576076891863 80460244951557864115337795)
        ·
          refine ⟨120690367427336796173006693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80460244951557864115337795 120690367427336796173006693)
          ·
            refine ⟨22629443892625649282438755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120690367427336796173006693 22629443892625649282438755)
            ·
              refine ⟨33944165838938473923658133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22629443892625649282438755 33944165838938473923658133)
              ·
                refine ⟨1591132773700240965171475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33944165838938473923658133 1591132773700240965171475)
                ·
                  refine ⟨2386699160550361447757213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591132773700240965171475 2386699160550361447757213)
                  ·
                    refine ⟨895012185206385542908955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386699160550361447757213 895012185206385542908955)
                    ·
                      rfl

theorem cell22_2614545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2614545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614545 prefixEnd_2614545 := by exact prefixLift 2614545
  have htrace : WordTrace (prefixWord ++ tailWord_2614545) baseStart_2614545 baseEnd_2614545 := by
    simpa [prefixWord, tailWord_2614545, baseEnd_2614545] using wordTrace_append hprefix tailTrace_2614545
  have hstable : (prefixWord ++ tailWord_2614545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614545).length < 2 ^ (prefixWord ++ tailWord_2614545).sum := by decide
  have hdescent : baseEnd_2614545 < baseStart_2614545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614596 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2614596 : Nat := 118140960795 + 2614596 * 2 ^ 59
def prefixEnd_2614596 : Nat := 4983230072969 + 3 ^ 40 * 2614596 * 2
def baseEnd_2614596 : Nat := 895029643548638409883799

theorem tailTrace_2614596 : CollatzResearch.WordTrace tailWord_2614596 prefixEnd_2614596 895029643548638409883799 := by
  unfold tailWord_2614596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47681075217886352145623821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63574766957181802860831761 47681075217886352145623821)
  ·
    refine ⟨17880403206707382054608933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47681075217886352145623821 17880403206707382054608933)
    ·
      refine ⟨3352575601257634135239175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17880403206707382054608933 3352575601257634135239175)
      ·
        refine ⟨5028863401886451202858763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352575601257634135239175 5028863401886451202858763)
        ·
          refine ⟨7543295102829676804288145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028863401886451202858763 7543295102829676804288145)
          ·
            refine ⟨5657471327122257603216109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7543295102829676804288145 5657471327122257603216109)
            ·
              refine ⟨2121551747670846601206041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5657471327122257603216109 2121551747670846601206041)
              ·
                refine ⟨1591163810753134950904531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121551747670846601206041 1591163810753134950904531)
                ·
                  refine ⟨2386745716129702426356797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591163810753134950904531 2386745716129702426356797)
                  ·
                    refine ⟨895029643548638409883799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386745716129702426356797 895029643548638409883799)
                    ·
                      rfl

theorem cell22_2614596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2614596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614596 prefixEnd_2614596 := by exact prefixLift 2614596
  have htrace : WordTrace (prefixWord ++ tailWord_2614596) baseStart_2614596 baseEnd_2614596 := by
    simpa [prefixWord, tailWord_2614596, baseEnd_2614596] using wordTrace_append hprefix tailTrace_2614596
  have hstable : (prefixWord ++ tailWord_2614596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614596).length < 2 ^ (prefixWord ++ tailWord_2614596).sum := by decide
  have hdescent : baseEnd_2614596 < baseStart_2614596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614665 : List Nat := [1, 2, 1, 1, 7, 2, 1, 7]
def baseStart_2614665 : Nat := 118140960795 + 2614665 * 2 ^ 59
def prefixEnd_2614665 : Nat := 4983230072969 + 3 ^ 40 * 2614665 * 2
def baseEnd_2614665 : Nat := 99450362628749469989843

theorem tailTrace_2614665 : CollatzResearch.WordTrace tailWord_2614665 prefixEnd_2614665 99450362628749469989843 := by
  unfold tailWord_2614665
  simp only [CollatzResearch.WordTrace]
  refine ⟨95364667072522729075509449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63576444715015152717006299 95364667072522729075509449)
  ·
    refine ⟨71523500304392046806632087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95364667072522729075509449 71523500304392046806632087)
    ·
      refine ⟨107285250456588070209948131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71523500304392046806632087 107285250456588070209948131)
      ·
        refine ⟨160927875684882105314922197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107285250456588070209948131 160927875684882105314922197)
        ·
          refine ⟨3771747086364424343318489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 160927875684882105314922197 3771747086364424343318489)
          ·
            refine ⟨2828810314773318257488867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771747086364424343318489 2828810314773318257488867)
            ·
              refine ⟨4243215472159977386233301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828810314773318257488867 4243215472159977386233301)
              ·
                refine ⟨99450362628749469989843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4243215472159977386233301 99450362628749469989843)
                ·
                  rfl

theorem cell22_2614665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 7].length) (baseStart_2614665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614665 prefixEnd_2614665 := by exact prefixLift 2614665
  have htrace : WordTrace (prefixWord ++ tailWord_2614665) baseStart_2614665 baseEnd_2614665 := by
    simpa [prefixWord, tailWord_2614665, baseEnd_2614665] using wordTrace_append hprefix tailTrace_2614665
  have hstable : (prefixWord ++ tailWord_2614665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614665).length < 2 ^ (prefixWord ++ tailWord_2614665).sum := by decide
  have hdescent : baseEnd_2614665 < baseStart_2614665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614684 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2614684 : Nat := 118140960795 + 2614684 * 2 ^ 59
def prefixEnd_2614684 : Nat := 4983230072969 + 3 ^ 40 * 2614684 * 2
def baseEnd_2614684 : Nat := 895059767747035513683529

theorem tailTrace_2614684 : CollatzResearch.WordTrace tailWord_2614684 prefixEnd_2614684 895059767747035513683529 := by
  unfold tailWord_2614684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47682680029726947660225553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63576906706302596880300737 47682680029726947660225553)
  ·
    refine ⟨35762010022295210745169165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47682680029726947660225553 35762010022295210745169165)
    ·
      refine ⟨13410753758360704029438437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35762010022295210745169165 13410753758360704029438437)
      ·
        refine ⟨2514516329692632005519707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13410753758360704029438437 2514516329692632005519707)
        ·
          refine ⟨3771774494538948008279561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514516329692632005519707 3771774494538948008279561)
          ·
            refine ⟨2828830870904211006209671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771774494538948008279561 2828830870904211006209671)
            ·
              refine ⟨4243246306356316509314507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828830870904211006209671 4243246306356316509314507)
              ·
                refine ⟨6364869459534474763971761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243246306356316509314507 6364869459534474763971761)
                ·
                  refine ⟨4773652094650856072978821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364869459534474763971761 4773652094650856072978821)
                  ·
                    refine ⟨895059767747035513683529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773652094650856072978821 895059767747035513683529)
                    ·
                      rfl

theorem cell22_2614684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2614684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614684 prefixEnd_2614684 := by exact prefixLift 2614684
  have htrace : WordTrace (prefixWord ++ tailWord_2614684) baseStart_2614684 baseEnd_2614684 := by
    simpa [prefixWord, tailWord_2614684, baseEnd_2614684] using wordTrace_append hprefix tailTrace_2614684
  have hstable : (prefixWord ++ tailWord_2614684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614684).length < 2 ^ (prefixWord ++ tailWord_2614684).sum := by decide
  have hdescent : baseEnd_2614684 < baseStart_2614684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614723 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_2614723 : Nat := 118140960795 + 2614723 * 2 ^ 59
def prefixEnd_2614723 : Nat := 4983230072969 + 3 ^ 40 * 2614723 * 2
def baseEnd_2614723 : Nat := 895073118244052411958409

theorem tailTrace_2614723 : CollatzResearch.WordTrace tailWord_2614723 prefixEnd_2614723 895073118244052411958409 := by
  unfold tailWord_2614723
  simp only [CollatzResearch.WordTrace]
  refine ⟨95366782506312604981120823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63577855004208403320747215 95366782506312604981120823)
  ·
    refine ⟨143050173759468907471681235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95366782506312604981120823 143050173759468907471681235)
    ·
      refine ⟨214575260639203361207521853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143050173759468907471681235 214575260639203361207521853)
      ·
        refine ⟨80465722739701260452820695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214575260639203361207521853 80465722739701260452820695)
        ·
          refine ⟨120698584109551890679231043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80465722739701260452820695 120698584109551890679231043)
          ·
            refine ⟨181047876164327836018846565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120698584109551890679231043 181047876164327836018846565)
            ·
              refine ⟨33946476780811469253533731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181047876164327836018846565 33946476780811469253533731)
              ·
                refine ⟨50919715171217203880300597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33946476780811469253533731 50919715171217203880300597)
                ·
                  refine ⟨4773723297301612863778181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50919715171217203880300597 4773723297301612863778181)
                  ·
                    refine ⟨895073118244052411958409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773723297301612863778181 895073118244052411958409)
                    ·
                      rfl

theorem cell22_2614723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_2614723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614723 prefixEnd_2614723 := by exact prefixLift 2614723
  have htrace : WordTrace (prefixWord ++ tailWord_2614723) baseStart_2614723 baseEnd_2614723 := by
    simpa [prefixWord, tailWord_2614723, baseEnd_2614723] using wordTrace_append hprefix tailTrace_2614723
  have hstable : (prefixWord ++ tailWord_2614723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614723).length < 2 ^ (prefixWord ++ tailWord_2614723).sum := by decide
  have hdescent : baseEnd_2614723 < baseStart_2614723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614757 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2614757 : Nat := 118140960795 + 2614757 * 2 ^ 59
def prefixEnd_2614757 : Nat := 4983230072969 + 3 ^ 40 * 2614757 * 2
def baseEnd_2614757 : Nat := 895084757138887656608305

theorem tailTrace_2614757 : CollatzResearch.WordTrace tailWord_2614757 prefixEnd_2614757 895084757138887656608305 := by
  unfold tailWord_2614757
  simp only [CollatzResearch.WordTrace]
  refine ⟨95368022588189428787858525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63578681725459619191905683 95368022588189428787858525)
  ·
    refine ⟨35763008470571035795446947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95368022588189428787858525 35763008470571035795446947)
    ·
      refine ⟨53644512705856553693170421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35763008470571035795446947 53644512705856553693170421)
      ·
        refine ⟨5029173066174051908734727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53644512705856553693170421 5029173066174051908734727)
        ·
          refine ⟨7543759599261077863102091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029173066174051908734727 7543759599261077863102091)
          ·
            refine ⟨11315639398891616794653137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543759599261077863102091 11315639398891616794653137)
            ·
              refine ⟨8486729549168712595989853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11315639398891616794653137 8486729549168712595989853)
              ·
                refine ⟨3182523580938267223496195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8486729549168712595989853 3182523580938267223496195)
                ·
                  refine ⟨4773785371407400835244293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182523580938267223496195 4773785371407400835244293)
                  ·
                    refine ⟨895084757138887656608305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4773785371407400835244293 895084757138887656608305)
                    ·
                      rfl

theorem cell22_2614757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2614757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614757 prefixEnd_2614757 := by exact prefixLift 2614757
  have htrace : WordTrace (prefixWord ++ tailWord_2614757) baseStart_2614757 baseEnd_2614757 := by
    simpa [prefixWord, tailWord_2614757, baseEnd_2614757] using wordTrace_append hprefix tailTrace_2614757
  have hstable : (prefixWord ++ tailWord_2614757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614757).length < 2 ^ (prefixWord ++ tailWord_2614757).sum := by decide
  have hdescent : baseEnd_2614757 < baseStart_2614757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614804 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2614804 : Nat := 118140960795 + 2614804 * 2 ^ 59
def prefixEnd_2614804 : Nat := 4983230072969 + 3 ^ 40 * 2614804 * 2
def baseEnd_2614804 : Nat := 895100846199395200683161

theorem tailTrace_2614804 : CollatzResearch.WordTrace tailWord_2614804 prefixEnd_2614804 895100846199395200683161 := by
  unfold tailWord_2614804
  simp only [CollatzResearch.WordTrace]
  refine ⟨47684868409509577907409733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63579824546012770543212977 47684868409509577907409733)
  ·
    refine ⟨8940912826783045857639325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47684868409509577907409733 8940912826783045857639325)
    ·
      refine ⟨3352842310043642196614747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8940912826783045857639325 3352842310043642196614747)
      ·
        refine ⟨5029263465065463294922121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352842310043642196614747 5029263465065463294922121)
        ·
          refine ⟨3771947598799097471191591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5029263465065463294922121 3771947598799097471191591)
          ·
            refine ⟨5657921398198646206787387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771947598799097471191591 5657921398198646206787387)
            ·
              refine ⟨8486882097297969310181081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657921398198646206787387 8486882097297969310181081)
              ·
                refine ⟨6365161572973476982635811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8486882097297969310181081 6365161572973476982635811)
                ·
                  refine ⟨9547742359460215473953717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365161572973476982635811 9547742359460215473953717)
                  ·
                    refine ⟨895100846199395200683161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9547742359460215473953717 895100846199395200683161)
                    ·
                      rfl

theorem cell22_2614804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2614804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614804 prefixEnd_2614804 := by exact prefixLift 2614804
  have htrace : WordTrace (prefixWord ++ tailWord_2614804) baseStart_2614804 baseEnd_2614804 := by
    simpa [prefixWord, tailWord_2614804, baseEnd_2614804] using wordTrace_append hprefix tailTrace_2614804
  have hstable : (prefixWord ++ tailWord_2614804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614804).length < 2 ^ (prefixWord ++ tailWord_2614804).sum := by decide
  have hdescent : baseEnd_2614804 < baseStart_2614804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614866 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_2614866 : Nat := 118140960795 + 2614866 * 2 ^ 59
def prefixEnd_2614866 : Nat := 4983230072969 + 3 ^ 40 * 2614866 * 2
def baseEnd_2614866 : Nat := 895122070066447705632971

theorem tailTrace_2614866 : CollatzResearch.WordTrace tailWord_2614866 prefixEnd_2614866 895122070066447705632971 := by
  unfold tailWord_2614866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842999536198635100894113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63581332096529693602384301 23842999536198635100894113)
  ·
    refine ⟨17882249652148976325670585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23842999536198635100894113 17882249652148976325670585)
    ·
      refine ⟨13411687239111732244252939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17882249652148976325670585 13411687239111732244252939)
      ·
        refine ⟨20117530858667598366379409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13411687239111732244252939 20117530858667598366379409)
        ·
          refine ⟨15088148144000698774784557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20117530858667598366379409 15088148144000698774784557)
          ·
            refine ⟨5658055554000262040544209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15088148144000698774784557 5658055554000262040544209)
            ·
              refine ⟨4243541665500196530408157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658055554000262040544209 4243541665500196530408157)
              ·
                refine ⟨1591328124562573698903059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243541665500196530408157 1591328124562573698903059)
                ·
                  refine ⟨2386992186843860548354589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591328124562573698903059 2386992186843860548354589)
                  ·
                    refine ⟨895122070066447705632971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386992186843860548354589 895122070066447705632971)
                    ·
                      rfl

theorem cell22_2614866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_2614866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614866 prefixEnd_2614866 := by exact prefixLift 2614866
  have htrace : WordTrace (prefixWord ++ tailWord_2614866) baseStart_2614866 baseEnd_2614866 := by
    simpa [prefixWord, tailWord_2614866, baseEnd_2614866] using wordTrace_append hprefix tailTrace_2614866
  have hstable : (prefixWord ++ tailWord_2614866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614866).length < 2 ^ (prefixWord ++ tailWord_2614866).sum := by decide
  have hdescent : baseEnd_2614866 < baseStart_2614866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614909 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2614909 : Nat := 118140960795 + 2614909 * 2 ^ 59
def prefixEnd_2614909 : Nat := 4983230072969 + 3 ^ 40 * 2614909 * 2
def baseEnd_2614909 : Nat := 895136789845209926807839

theorem tailTrace_2614909 : CollatzResearch.WordTrace tailWord_2614909 prefixEnd_2614909 895136789845209926807839 := by
  unfold tailWord_2614909
  simp only [CollatzResearch.WordTrace]
  refine ⟨95373566483638758747391781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63582377655759172498261187 95373566483638758747391781)
  ·
    refine ⟨17882543715682267265135959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95373566483638758747391781 17882543715682267265135959)
    ·
      refine ⟨26823815573523400897703939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17882543715682267265135959 26823815573523400897703939)
      ·
        refine ⟨40235723360285101346555909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26823815573523400897703939 40235723360285101346555909)
        ·
          refine ⟨7544198130053456502479233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40235723360285101346555909 7544198130053456502479233)
          ·
            refine ⟨5658148597540092376859425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7544198130053456502479233 5658148597540092376859425)
            ·
              refine ⟨4243611448155069282644569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658148597540092376859425 4243611448155069282644569)
              ·
                refine ⟨3182708586116301961983427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4243611448155069282644569 3182708586116301961983427)
                ·
                  refine ⟨4774062879174452942975141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182708586116301961983427 4774062879174452942975141)
                  ·
                    refine ⟨895136789845209926807839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774062879174452942975141 895136789845209926807839)
                    ·
                      rfl

theorem cell22_2614909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2614909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614909 prefixEnd_2614909 := by exact prefixLift 2614909
  have htrace : WordTrace (prefixWord ++ tailWord_2614909) baseStart_2614909 baseEnd_2614909 := by
    simpa [prefixWord, tailWord_2614909, baseEnd_2614909] using wordTrace_append hprefix tailTrace_2614909
  have hstable : (prefixWord ++ tailWord_2614909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614909).length < 2 ^ (prefixWord ++ tailWord_2614909).sum := by decide
  have hdescent : baseEnd_2614909 < baseStart_2614909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614935 : List Nat := [1, 1, 3, 3, 2, 2, 10]
def baseStart_2614935 : Nat := 118140960795 + 2614935 * 2 ^ 59
def prefixEnd_2614935 : Nat := 4983230072969 + 3 ^ 40 * 2614935 * 2
def baseEnd_2614935 : Nat := 33153544080613130579917

theorem tailTrace_2614935 : CollatzResearch.WordTrace tailWord_2614935 prefixEnd_2614935 33153544080613130579917 := by
  unfold tailWord_2614935
  simp only [CollatzResearch.WordTrace]
  refine ⟨95374514781544565187838259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63583009854363043458558839 95374514781544565187838259)
  ·
    refine ⟨143061772172316847781757389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95374514781544565187838259 143061772172316847781757389)
    ·
      refine ⟨53648164564618817918159021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143061772172316847781757389 53648164564618817918159021)
      ·
        refine ⟨20118061711732056719309633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53648164564618817918159021 20118061711732056719309633)
        ·
          refine ⟨15088546283799042539482225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20118061711732056719309633 15088546283799042539482225)
          ·
            refine ⟨11316409712849281904611669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15088546283799042539482225 11316409712849281904611669)
            ·
              refine ⟨33153544080613130579917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11316409712849281904611669 33153544080613130579917)
              ·
                rfl

theorem cell22_2614935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 10].length) (baseStart_2614935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2614935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2614935 prefixEnd_2614935 := by exact prefixLift 2614935
  have htrace : WordTrace (prefixWord ++ tailWord_2614935) baseStart_2614935 baseEnd_2614935 := by
    simpa [prefixWord, tailWord_2614935, baseEnd_2614935] using wordTrace_append hprefix tailTrace_2614935
  have hstable : (prefixWord ++ tailWord_2614935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614935).length < 2 ^ (prefixWord ++ tailWord_2614935).sum := by decide
  have hdescent : baseEnd_2614935 < baseStart_2614935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615001 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_2615001 : Nat := 118140960795 + 2615001 * 2 ^ 59
def prefixEnd_2615001 : Nat := 4983230072969 + 3 ^ 40 * 2615001 * 2
def baseEnd_2615001 : Nat := 895168283325352353507557

theorem tailTrace_2615001 : CollatzResearch.WordTrace tailWord_2615001 prefixEnd_2615001 895168283325352353507557 := by
  unfold tailWord_2615001
  simp only [CollatzResearch.WordTrace]
  refine ⟨95376921999305458459740857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63584614666203638973160571 95376921999305458459740857)
  ·
    refine ⟨71532691499479093844805643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95376921999305458459740857 71532691499479093844805643)
    ·
      refine ⟨107299037249218640767208465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71532691499479093844805643 107299037249218640767208465)
      ·
        refine ⟨80474277936913980575406349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107299037249218640767208465 80474277936913980575406349)
        ·
          refine ⟨30177854226342742715777381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80474277936913980575406349 30177854226342742715777381)
          ·
            refine ⟨5658347667439264259208259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30177854226342742715777381 5658347667439264259208259)
            ·
              refine ⟨8487521501158896388812389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658347667439264259208259 8487521501158896388812389)
              ·
                refine ⟨1591410281467293072902323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8487521501158896388812389 1591410281467293072902323)
                ·
                  refine ⟨2387115422200939609353485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591410281467293072902323 2387115422200939609353485)
                  ·
                    refine ⟨895168283325352353507557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387115422200939609353485 895168283325352353507557)
                    ·
                      rfl

theorem cell22_2615001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_2615001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615001 prefixEnd_2615001 := by exact prefixLift 2615001
  have htrace : WordTrace (prefixWord ++ tailWord_2615001) baseStart_2615001 baseEnd_2615001 := by
    simpa [prefixWord, tailWord_2615001, baseEnd_2615001] using wordTrace_append hprefix tailTrace_2615001
  have hstable : (prefixWord ++ tailWord_2615001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615001).length < 2 ^ (prefixWord ++ tailWord_2615001).sum := by decide
  have hdescent : baseEnd_2615001 < baseStart_2615001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615012 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2615012 : Nat := 118140960795 + 2615012 * 2 ^ 59
def prefixEnd_2615012 : Nat := 4983230072969 + 3 ^ 40 * 2615012 * 2
def baseEnd_2615012 : Nat := 895172048850151991482523

theorem tailTrace_2615012 : CollatzResearch.WordTrace tailWord_2615012 prefixEnd_2615012 895172048850151991482523 := by
  unfold tailWord_2615012
  simp only [CollatzResearch.WordTrace]
  refine ⟨47688661601132803669195645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63584882134843738225594193 47688661601132803669195645)
  ·
    refine ⟨17883248100424801375948367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47688661601132803669195645 17883248100424801375948367)
    ·
      refine ⟨26824872150637202063922551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17883248100424801375948367 26824872150637202063922551)
      ·
        refine ⟨40237308225955803095883827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26824872150637202063922551 40237308225955803095883827)
        ·
          refine ⟨60355962338933704643825741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40237308225955803095883827 60355962338933704643825741)
          ·
            refine ⟨22633485877100139241434653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60355962338933704643825741 22633485877100139241434653)
            ·
              refine ⟨8487557203912552215537995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22633485877100139241434653 8487557203912552215537995)
              ·
                refine ⟨12731335805868828323306993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487557203912552215537995 12731335805868828323306993)
                ·
                  refine ⟨9548501854401621242480245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12731335805868828323306993 9548501854401621242480245)
                  ·
                    refine ⟨895172048850151991482523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9548501854401621242480245 895172048850151991482523)
                    ·
                      rfl

theorem cell22_2615012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2615012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615012 prefixEnd_2615012 := by exact prefixLift 2615012
  have htrace : WordTrace (prefixWord ++ tailWord_2615012) baseStart_2615012 baseEnd_2615012 := by
    simpa [prefixWord, tailWord_2615012, baseEnd_2615012] using wordTrace_append hprefix tailTrace_2615012
  have hstable : (prefixWord ++ tailWord_2615012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615012).length < 2 ^ (prefixWord ++ tailWord_2615012).sum := by decide
  have hdescent : baseEnd_2615012 < baseStart_2615012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615027 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_2615027 : Nat := 118140960795 + 2615027 * 2 ^ 59
def prefixEnd_2615027 : Nat := 4983230072969 + 3 ^ 40 * 2615027 * 2
def baseEnd_2615027 : Nat := 895177183656696952357477

theorem tailTrace_2615027 : CollatzResearch.WordTrace tailWord_2615027 prefixEnd_2615027 895177183656696952357477 := by
  unfold tailWord_2615027
  simp only [CollatzResearch.WordTrace]
  refine ⟨95377870297211264900187335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63585246864807509933458223 95377870297211264900187335)
  ·
    refine ⟨143066805445816897350281003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95377870297211264900187335 143066805445816897350281003)
    ·
      refine ⟨214600208168725346025421505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143066805445816897350281003 214600208168725346025421505)
      ·
        refine ⟨160950156126544009519066129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214600208168725346025421505 160950156126544009519066129)
        ·
          refine ⟨120712617094908007139299597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160950156126544009519066129 120712617094908007139299597)
          ·
            refine ⟨45267231410590502677237349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120712617094908007139299597 45267231410590502677237349)
            ·
              refine ⟨8487605889485719251982003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45267231410590502677237349 8487605889485719251982003)
              ·
                refine ⟨12731408834228578877973005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487605889485719251982003 12731408834228578877973005)
                ·
                  refine ⟨4774278312835717079239877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12731408834228578877973005 4774278312835717079239877)
                  ·
                    refine ⟨895177183656696952357477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774278312835717079239877 895177183656696952357477)
                    ·
                      rfl

theorem cell22_2615027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_2615027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615027 prefixEnd_2615027 := by exact prefixLift 2615027
  have htrace : WordTrace (prefixWord ++ tailWord_2615027) baseStart_2615027 baseEnd_2615027 := by
    simpa [prefixWord, tailWord_2615027, baseEnd_2615027] using wordTrace_append hprefix tailTrace_2615027
  have hstable : (prefixWord ++ tailWord_2615027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615027).length < 2 ^ (prefixWord ++ tailWord_2615027).sum := by decide
  have hdescent : baseEnd_2615027 < baseStart_2615027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615072 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_2615072 : Nat := 118140960795 + 2615072 * 2 ^ 59
def prefixEnd_2615072 : Nat := 4983230072969 + 3 ^ 40 * 2615072 * 2
def baseEnd_2615072 : Nat := 895192588076331834982339

theorem tailTrace_2615072 : CollatzResearch.WordTrace tailWord_2615072 prefixEnd_2615072 895192588076331834982339 := by
  unfold tailWord_2615072
  simp only [CollatzResearch.WordTrace]
  refine ⟨47689755791024118792787735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63586341054698825057050313 47689755791024118792787735)
  ·
    refine ⟨71534633686536178189181603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47689755791024118792787735 71534633686536178189181603)
    ·
      refine ⟨107301950529804267283772405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71534633686536178189181603 107301950529804267283772405)
      ·
        refine ⟨10059557862169150057853663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107301950529804267283772405 10059557862169150057853663)
        ·
          refine ⟨15089336793253725086780495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059557862169150057853663 15089336793253725086780495)
          ·
            refine ⟨22634005189880587630170743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15089336793253725086780495 22634005189880587630170743)
            ·
              refine ⟨33951007784820881445256115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22634005189880587630170743 33951007784820881445256115)
              ·
                refine ⟨50926511677231322167884173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33951007784820881445256115 50926511677231322167884173)
                ·
                  refine ⟨19097441878961745812956565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50926511677231322167884173 19097441878961745812956565)
                  ·
                    refine ⟨895192588076331834982339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19097441878961745812956565 895192588076331834982339)
                    ·
                      rfl

theorem cell22_2615072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_2615072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615072 prefixEnd_2615072 := by exact prefixLift 2615072
  have htrace : WordTrace (prefixWord ++ tailWord_2615072) baseStart_2615072 baseEnd_2615072 := by
    simpa [prefixWord, tailWord_2615072, baseEnd_2615072] using wordTrace_append hprefix tailTrace_2615072
  have hstable : (prefixWord ++ tailWord_2615072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615072).length < 2 ^ (prefixWord ++ tailWord_2615072).sum := by decide
  have hdescent : baseEnd_2615072 < baseStart_2615072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615093 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 4]
def baseStart_2615093 : Nat := 118140960795 + 2615093 * 2 ^ 59
def prefixEnd_2615093 : Nat := 4983230072969 + 3 ^ 40 * 2615093 * 2
def baseEnd_2615093 : Nat := 298399925601831593402425

theorem tailTrace_2615093 : CollatzResearch.WordTrace tailWord_2615093 prefixEnd_2615093 298399925601831593402425 := by
  unfold tailWord_2615093
  simp only [CollatzResearch.WordTrace]
  refine ⟨95380277514972158172089933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63586851676648105448059955 95380277514972158172089933)
  ·
    refine ⟨35767604068114559314533725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95380277514972158172089933 35767604068114559314533725)
    ·
      refine ⟨13412851525542959742950147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35767604068114559314533725 13412851525542959742950147)
      ·
        refine ⟨20119277288314439614425221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13412851525542959742950147 20119277288314439614425221)
        ·
          refine ⟨3772364491558957427704729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20119277288314439614425221 3772364491558957427704729)
          ·
            refine ⟨2829273368669218070778547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772364491558957427704729 2829273368669218070778547)
            ·
              refine ⟨4243910053003827106167821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829273368669218070778547 4243910053003827106167821)
              ·
                refine ⟨1591466269876435164812933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243910053003827106167821 1591466269876435164812933)
                ·
                  refine ⟨298399925601831593402425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1591466269876435164812933 298399925601831593402425)
                  ·
                    rfl

theorem cell22_2615093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_2615093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615093 prefixEnd_2615093 := by exact prefixLift 2615093
  have htrace : WordTrace (prefixWord ++ tailWord_2615093) baseStart_2615093 baseEnd_2615093 := by
    simpa [prefixWord, tailWord_2615093, baseEnd_2615093] using wordTrace_append hprefix tailTrace_2615093
  have hstable : (prefixWord ++ tailWord_2615093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615093).length < 2 ^ (prefixWord ++ tailWord_2615093).sum := by decide
  have hdescent : baseEnd_2615093 < baseStart_2615093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615147 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_2615147 : Nat := 118140960795 + 2615147 * 2 ^ 59
def prefixEnd_2615147 : Nat := 4983230072969 + 3 ^ 40 * 2615147 * 2
def baseEnd_2615147 : Nat := 895218262109056639357109

theorem tailTrace_2615147 : CollatzResearch.WordTrace tailWord_2615147 prefixEnd_2615147 895218262109056639357109 := by
  unfold tailWord_2615147
  simp only [CollatzResearch.WordTrace]
  refine ⟨95382247056776525394555695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63588164704517683596370463 95382247056776525394555695)
  ·
    refine ⟨143073370585164788091833543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95382247056776525394555695 143073370585164788091833543)
    ·
      refine ⟨214610055877747182137750315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143073370585164788091833543 214610055877747182137750315)
      ·
        refine ⟨321915083816620773206625473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214610055877747182137750315 321915083816620773206625473)
        ·
          refine ⟨241436312862465579904969105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321915083816620773206625473 241436312862465579904969105)
          ·
            refine ⟨181077234646849184928726829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241436312862465579904969105 181077234646849184928726829)
            ·
              refine ⟨67903962992568444348272561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181077234646849184928726829 67903962992568444348272561)
              ·
                refine ⟨50927972244426333261204421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67903962992568444348272561 50927972244426333261204421)
                ·
                  refine ⟨9548994795829937486475829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50927972244426333261204421 9548994795829937486475829)
                  ·
                    refine ⟨895218262109056639357109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9548994795829937486475829 895218262109056639357109)
                    ·
                      rfl

theorem cell22_2615147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_2615147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615147 prefixEnd_2615147 := by exact prefixLift 2615147
  have htrace : WordTrace (prefixWord ++ tailWord_2615147) baseStart_2615147 baseEnd_2615147 := by
    simpa [prefixWord, tailWord_2615147, baseEnd_2615147] using wordTrace_append hprefix tailTrace_2615147
  have hstable : (prefixWord ++ tailWord_2615147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615147).length < 2 ^ (prefixWord ++ tailWord_2615147).sum := by decide
  have hdescent : baseEnd_2615147 < baseStart_2615147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615194 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_2615194 : Nat := 118140960795 + 2615194 * 2 ^ 59
def prefixEnd_2615194 : Nat := 4983230072969 + 3 ^ 40 * 2615194 * 2
def baseEnd_2615194 : Nat := 298411450389854727810655

theorem tailTrace_2615194 : CollatzResearch.WordTrace tailWord_2615194 prefixEnd_2615194 298411450389854727810655 := by
  unfold tailWord_2615194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845990321901563105379159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63589307525070834947677757 23845990321901563105379159)
  ·
    refine ⟨35768985482852344658068739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23845990321901563105379159 35768985482852344658068739)
    ·
      refine ⟨53653478224278516987103109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35768985482852344658068739 53653478224278516987103109)
      ·
        refine ⟨10060027167052221935081833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53653478224278516987103109 10060027167052221935081833)
        ·
          refine ⟨7545020375289166451311375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10060027167052221935081833 7545020375289166451311375)
          ·
            refine ⟨11317530562933749676967063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545020375289166451311375 11317530562933749676967063)
            ·
              refine ⟨16976295844400624515450595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11317530562933749676967063 16976295844400624515450595)
              ·
                refine ⟨25464443766600936773175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16976295844400624515450595 25464443766600936773175893)
                ·
                  refine ⟨298411450389854727810655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25464443766600936773175893 298411450389854727810655)
                  ·
                    rfl

theorem cell22_2615194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_2615194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615194 prefixEnd_2615194 := by exact prefixLift 2615194
  have htrace : WordTrace (prefixWord ++ tailWord_2615194) baseStart_2615194 baseEnd_2615194 := by
    simpa [prefixWord, tailWord_2615194, baseEnd_2615194] using wordTrace_append hprefix tailTrace_2615194
  have hstable : (prefixWord ++ tailWord_2615194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615194).length < 2 ^ (prefixWord ++ tailWord_2615194).sum := by decide
  have hdescent : baseEnd_2615194 < baseStart_2615194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615196 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2615196 : Nat := 118140960795 + 2615196 * 2 ^ 59
def prefixEnd_2615196 : Nat := 4983230072969 + 3 ^ 40 * 2615196 * 2
def baseEnd_2615196 : Nat := 895235035810436844881959

theorem tailTrace_2615196 : CollatzResearch.WordTrace tailWord_2615196 prefixEnd_2615196 895235035810436844881959 := by
  unfold tailWord_2615196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47692017116799503381544721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63589356155732671175392961 47692017116799503381544721)
  ·
    refine ⟨35769012837599627536158541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47692017116799503381544721 35769012837599627536158541)
    ·
      refine ⟨13413379814099860326059453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35769012837599627536158541 13413379814099860326059453)
      ·
        refine ⟨5030017430287447622272295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13413379814099860326059453 5030017430287447622272295)
        ·
          refine ⟨7545026145431171433408443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030017430287447622272295 7545026145431171433408443)
          ·
            refine ⟨11317539218146757150112665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545026145431171433408443 11317539218146757150112665)
            ·
              refine ⟨8488154413610067862584499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317539218146757150112665 8488154413610067862584499)
              ·
                refine ⟨12732231620415101793876749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488154413610067862584499 12732231620415101793876749)
                ·
                  refine ⟨4774586857655663172703781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12732231620415101793876749 4774586857655663172703781)
                  ·
                    refine ⟨895235035810436844881959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774586857655663172703781 895235035810436844881959)
                    ·
                      rfl

theorem cell22_2615196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2615196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615196 prefixEnd_2615196 := by exact prefixLift 2615196
  have htrace : WordTrace (prefixWord ++ tailWord_2615196) baseStart_2615196 baseEnd_2615196 := by
    simpa [prefixWord, tailWord_2615196, baseEnd_2615196] using wordTrace_append hprefix tailTrace_2615196
  have hstable : (prefixWord ++ tailWord_2615196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615196).length < 2 ^ (prefixWord ++ tailWord_2615196).sum := by decide
  have hdescent : baseEnd_2615196 < baseStart_2615196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615224 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_2615224 : Nat := 118140960795 + 2615224 * 2 ^ 59
def prefixEnd_2615224 : Nat := 4983230072969 + 3 ^ 40 * 2615224 * 2
def baseEnd_2615224 : Nat := 895244620782654105181873

theorem tailTrace_2615224 : CollatzResearch.WordTrace tailWord_2615224 prefixEnd_2615224 895244620782654105181873 := by
  unfold tailWord_2615224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47692527738748783772554363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63590036984998378363405817 47692527738748783772554363)
  ·
    refine ⟨71538791608123175658831545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47692527738748783772554363 71538791608123175658831545)
    ·
      refine ⟨53654093706092381744123659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71538791608123175658831545 53654093706092381744123659)
      ·
        refine ⟨80481140559138572616185489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53654093706092381744123659 80481140559138572616185489)
        ·
          refine ⟨60360855419353929462139117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80481140559138572616185489 60360855419353929462139117)
          ·
            refine ⟨22635320782257723548302169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60360855419353929462139117 22635320782257723548302169)
            ·
              refine ⟨16976490586693292661226627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22635320782257723548302169 16976490586693292661226627)
              ·
                refine ⟨25464735880039938991839941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16976490586693292661226627 25464735880039938991839941)
                ·
                  refine ⟨4774637977507488560969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25464735880039938991839941 4774637977507488560969989)
                  ·
                    refine ⟨895244620782654105181873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774637977507488560969989 895244620782654105181873)
                    ·
                      rfl

theorem cell22_2615224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_2615224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615224 prefixEnd_2615224 := by exact prefixLift 2615224
  have htrace : WordTrace (prefixWord ++ tailWord_2615224) baseStart_2615224 baseEnd_2615224 := by
    simpa [prefixWord, tailWord_2615224, baseEnd_2615224] using wordTrace_append hprefix tailTrace_2615224
  have hstable : (prefixWord ++ tailWord_2615224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615224).length < 2 ^ (prefixWord ++ tailWord_2615224).sum := by decide
  have hdescent : baseEnd_2615224 < baseStart_2615224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615226 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_2615226 : Nat := 118140960795 + 2615226 * 2 ^ 59
def prefixEnd_2615226 : Nat := 4983230072969 + 3 ^ 40 * 2615226 * 2
def baseEnd_2615226 : Nat := 895245305423526766631867

theorem tailTrace_2615226 : CollatzResearch.WordTrace tailWord_2615226 prefixEnd_2615226 895245305423526766631867 := by
  unfold tailWord_2615226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846282105872580471670383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63590085615660214591121021 23846282105872580471670383)
  ·
    refine ⟨35769423158808870707505575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846282105872580471670383 35769423158808870707505575)
    ·
      refine ⟨53654134738213306061258363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35769423158808870707505575 53654134738213306061258363)
      ·
        refine ⟨80481202107319959091887545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53654134738213306061258363 80481202107319959091887545)
        ·
          refine ⟨60360901580489969318915659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80481202107319959091887545 60360901580489969318915659)
          ·
            refine ⟨90541352370734953978373489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60360901580489969318915659 90541352370734953978373489)
            ·
              refine ⟨67906014278051215483780117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90541352370734953978373489 67906014278051215483780117)
              ·
                refine ⟨3183094419283650725802193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67906014278051215483780117 3183094419283650725802193)
                ·
                  refine ⟨2387320814462738044351645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183094419283650725802193 2387320814462738044351645)
                  ·
                    refine ⟨895245305423526766631867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387320814462738044351645 895245305423526766631867)
                    ·
                      rfl

theorem cell22_2615226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_2615226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615226 prefixEnd_2615226 := by exact prefixLift 2615226
  have htrace : WordTrace (prefixWord ++ tailWord_2615226) baseStart_2615226 baseEnd_2615226 := by
    simpa [prefixWord, tailWord_2615226, baseEnd_2615226] using wordTrace_append hprefix tailTrace_2615226
  have hstable : (prefixWord ++ tailWord_2615226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615226).length < 2 ^ (prefixWord ++ tailWord_2615226).sum := by decide
  have hdescent : baseEnd_2615226 < baseStart_2615226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615228 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_2615228 : Nat := 118140960795 + 2615228 * 2 ^ 59
def prefixEnd_2615228 : Nat := 4983230072969 + 3 ^ 40 * 2615228 * 2
def baseEnd_2615228 : Nat := 298415330021466476027287

theorem tailTrace_2615228 : CollatzResearch.WordTrace tailWord_2615228 prefixEnd_2615228 298415330021466476027287 := by
  unfold tailWord_2615228
  simp only [CollatzResearch.WordTrace]
  refine ⟨47692600684741538114127169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63590134246322050818836225 47692600684741538114127169)
  ·
    refine ⟨35769450513556153585595377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47692600684741538114127169 35769450513556153585595377)
    ·
      refine ⟨26827087885167115189196533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35769450513556153585595377 26827087885167115189196533)
      ·
        refine ⟨2515039489234417048987175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26827087885167115189196533 2515039489234417048987175)
        ·
          refine ⟨3772559233851625573480763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515039489234417048987175 3772559233851625573480763)
          ·
            refine ⟨5658838850777438360221145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772559233851625573480763 5658838850777438360221145)
            ·
              refine ⟨4244129138083078770165859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658838850777438360221145 4244129138083078770165859)
              ·
                refine ⟨6366193707124618155248789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244129138083078770165859 6366193707124618155248789)
                ·
                  refine ⟨298415330021466476027287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6366193707124618155248789 298415330021466476027287)
                  ·
                    rfl

theorem cell22_2615228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_2615228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615228 prefixEnd_2615228 := by exact prefixLift 2615228
  have htrace : WordTrace (prefixWord ++ tailWord_2615228) baseStart_2615228 baseEnd_2615228 := by
    simpa [prefixWord, tailWord_2615228, baseEnd_2615228] using wordTrace_append hprefix tailTrace_2615228
  have hstable : (prefixWord ++ tailWord_2615228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615228).length < 2 ^ (prefixWord ++ tailWord_2615228).sum := by decide
  have hdescent : baseEnd_2615228 < baseStart_2615228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615243 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 2, 3]
def baseStart_2615243 : Nat := 118140960795 + 2615243 * 2 ^ 59
def prefixEnd_2615243 : Nat := 4983230072969 + 3 ^ 40 * 2615243 * 2
def baseEnd_2615243 : Nat := 895251124870944388956815

theorem tailTrace_2615243 : CollatzResearch.WordTrace tailWord_2615243 prefixEnd_2615243 895251124870944388956815 := by
  unfold tailWord_2615243
  simp only [CollatzResearch.WordTrace]
  refine ⟨95385748464428733790050383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63590498976285822526700255 95385748464428733790050383)
  ·
    refine ⟨143078622696643100685075575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95385748464428733790050383 143078622696643100685075575)
    ·
      refine ⟨214617934044964651027613363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143078622696643100685075575 214617934044964651027613363)
      ·
        refine ⟨321926901067446976541420045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214617934044964651027613363 321926901067446976541420045)
        ·
          refine ⟨120722587900292616203032517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321926901067446976541420045 120722587900292616203032517)
          ·
            refine ⟨22635485231304865538068597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120722587900292616203032517 22635485231304865538068597)
            ·
              refine ⟨2122076740434831144193931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22635485231304865538068597 2122076740434831144193931)
              ·
                refine ⟨3183115110652246716290897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122076740434831144193931 3183115110652246716290897)
                ·
                  refine ⟨2387336332989185037218173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183115110652246716290897 2387336332989185037218173)
                  ·
                    refine ⟨895251124870944388956815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387336332989185037218173 895251124870944388956815)
                    ·
                      rfl

theorem cell22_2615243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 3].length) (baseStart_2615243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615243 prefixEnd_2615243 := by exact prefixLift 2615243
  have htrace : WordTrace (prefixWord ++ tailWord_2615243) baseStart_2615243 baseEnd_2615243 := by
    simpa [prefixWord, tailWord_2615243, baseEnd_2615243] using wordTrace_append hprefix tailTrace_2615243
  have hstable : (prefixWord ++ tailWord_2615243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615243).length < 2 ^ (prefixWord ++ tailWord_2615243).sum := by decide
  have hdescent : baseEnd_2615243 < baseStart_2615243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615288 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_2615288 : Nat := 118140960795 + 2615288 * 2 ^ 59
def prefixEnd_2615288 : Nat := 4983230072969 + 3 ^ 40 * 2615288 * 2
def baseEnd_2615288 : Nat := 895266529290579271581677

theorem tailTrace_2615288 : CollatzResearch.WordTrace tailWord_2615288 prefixEnd_2615288 895266529290579271581677 := by
  unfold tailWord_2615288
  simp only [CollatzResearch.WordTrace]
  refine ⟨47693694874632853237719259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63591593166177137650292345 47693694874632853237719259)
  ·
    refine ⟨71540542311949279856578889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47693694874632853237719259 71540542311949279856578889)
    ·
      refine ⟨53655406733961959892434167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71540542311949279856578889 53655406733961959892434167)
      ·
        refine ⟨80483110100942939838651251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53655406733961959892434167 80483110100942939838651251)
        ·
          refine ⟨120724665151414409757976877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80483110100942939838651251 120724665151414409757976877)
          ·
            refine ⟨45271749431780403659241329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120724665151414409757976877 45271749431780403659241329)
            ·
              refine ⟨33953812073835302744430997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45271749431780403659241329 33953812073835302744430997)
              ·
                refine ⟨1591584940961029816145203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33953812073835302744430997 1591584940961029816145203)
                ·
                  refine ⟨2387377411441544724217805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591584940961029816145203 2387377411441544724217805)
                  ·
                    refine ⟨895266529290579271581677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387377411441544724217805 895266529290579271581677)
                    ·
                      rfl

theorem cell22_2615288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_2615288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615288 prefixEnd_2615288 := by exact prefixLift 2615288
  have htrace : WordTrace (prefixWord ++ tailWord_2615288) baseStart_2615288 baseEnd_2615288 := by
    simpa [prefixWord, tailWord_2615288, baseEnd_2615288] using wordTrace_append hprefix tailTrace_2615288
  have hstable : (prefixWord ++ tailWord_2615288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615288).length < 2 ^ (prefixWord ++ tailWord_2615288).sum := by decide
  have hdescent : baseEnd_2615288 < baseStart_2615288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615299 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_2615299 : Nat := 118140960795 + 2615299 * 2 ^ 59
def prefixEnd_2615299 : Nat := 4983230072969 + 3 ^ 40 * 2615299 * 2
def baseEnd_2615299 : Nat := 895270294815378909556643

theorem tailTrace_2615299 : CollatzResearch.WordTrace tailWord_2615299 prefixEnd_2615299 895270294815378909556643 := by
  unfold tailWord_2615299
  simp only [CollatzResearch.WordTrace]
  refine ⟨95387790952225855354088951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63591860634817236902725967 95387790952225855354088951)
  ·
    refine ⟨143081686428338783031133427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95387790952225855354088951 143081686428338783031133427)
    ·
      refine ⟨214622529642508174546700141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143081686428338783031133427 214622529642508174546700141)
      ·
        refine ⟨80483448615940565455012553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214622529642508174546700141 80483448615940565455012553)
        ·
          refine ⟨60362586461955424091259415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80483448615940565455012553 60362586461955424091259415)
          ·
            refine ⟨90543879692933136136889123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60362586461955424091259415 90543879692933136136889123)
            ·
              refine ⟨135815819539399704205333685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90543879692933136136889123 135815819539399704205333685)
              ·
                refine ⟨12732733081818722269250033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135815819539399704205333685 12732733081818722269250033)
                ·
                  refine ⟨9549549811364041701937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12732733081818722269250033 9549549811364041701937525)
                  ·
                    refine ⟨895270294815378909556643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9549549811364041701937525 895270294815378909556643)
                    ·
                      rfl

theorem cell22_2615299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_2615299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615299 prefixEnd_2615299 := by exact prefixLift 2615299
  have htrace : WordTrace (prefixWord ++ tailWord_2615299) baseStart_2615299 baseEnd_2615299 := by
    simpa [prefixWord, tailWord_2615299, baseEnd_2615299] using wordTrace_append hprefix tailTrace_2615299
  have hstable : (prefixWord ++ tailWord_2615299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615299).length < 2 ^ (prefixWord ++ tailWord_2615299).sum := by decide
  have hdescent : baseEnd_2615299 < baseStart_2615299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615301 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 5]
def baseStart_2615301 : Nat := 118140960795 + 2615301 * 2 ^ 59
def prefixEnd_2615301 : Nat := 4983230072969 + 3 ^ 40 * 2615301 * 2
def baseEnd_2615301 : Nat := 298423659818750523668879

theorem tailTrace_2615301 : CollatzResearch.WordTrace tailWord_2615301 prefixEnd_2615301 298423659818750523668879 := by
  unfold tailWord_2615301
  simp only [CollatzResearch.WordTrace]
  refine ⟨95387863898218609695661757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63591909265479073130441171 95387863898218609695661757)
  ·
    refine ⟨35770448961831978635873159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95387863898218609695661757 35770448961831978635873159)
    ·
      refine ⟨53655673442747967953809739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35770448961831978635873159 53655673442747967953809739)
      ·
        refine ⟨80483510164121951930714609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53655673442747967953809739 80483510164121951930714609)
        ·
          refine ⟨60362632623091463948035957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80483510164121951930714609 60362632623091463948035957)
          ·
            refine ⟨5658996808414824745128371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60362632623091463948035957 5658996808414824745128371)
            ·
              refine ⟨8488495212622237117692557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658996808414824745128371 8488495212622237117692557)
              ·
                refine ⟨3183185704733338919134709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8488495212622237117692557 3183185704733338919134709)
                ·
                  refine ⟨298423659818750523668879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3183185704733338919134709 298423659818750523668879)
                  ·
                    rfl

theorem cell22_2615301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_2615301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615301 prefixEnd_2615301 := by exact prefixLift 2615301
  have htrace : WordTrace (prefixWord ++ tailWord_2615301) baseStart_2615301 baseEnd_2615301 := by
    simpa [prefixWord, tailWord_2615301, baseEnd_2615301] using wordTrace_append hprefix tailTrace_2615301
  have hstable : (prefixWord ++ tailWord_2615301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615301).length < 2 ^ (prefixWord ++ tailWord_2615301).sum := by decide
  have hdescent : baseEnd_2615301 < baseStart_2615301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615335 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 5]
def baseStart_2615335 : Nat := 118140960795 + 2615335 * 2 ^ 59
def prefixEnd_2615335 : Nat := 4983230072969 + 3 ^ 40 * 2615335 * 2
def baseEnd_2615335 : Nat := 298427539450362271885511

theorem tailTrace_2615335 : CollatzResearch.WordTrace tailWord_2615335 prefixEnd_2615335 298427539450362271885511 := by
  unfold tailWord_2615335
  simp only [CollatzResearch.WordTrace]
  refine ⟨95389103980095433502399459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63592735986730289001599639 95389103980095433502399459)
  ·
    refine ⟨143083655970143150253599189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95389103980095433502399459 143083655970143150253599189)
    ·
      refine ⟨3353523186800230084068731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 143083655970143150253599189 3353523186800230084068731)
      ·
        refine ⟨5030284780200345126103097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353523186800230084068731 5030284780200345126103097)
        ·
          refine ⟨3772713585150258844577323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5030284780200345126103097 3772713585150258844577323)
          ·
            refine ⟨5659070377725388266865985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772713585150258844577323 5659070377725388266865985)
            ·
              refine ⟨4244302783294041200149489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659070377725388266865985 4244302783294041200149489)
              ·
                refine ⟨3183227087470530900112117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244302783294041200149489 3183227087470530900112117)
                ·
                  refine ⟨298427539450362271885511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3183227087470530900112117 298427539450362271885511)
                  ·
                    rfl

theorem cell22_2615335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].length) (baseStart_2615335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615335 prefixEnd_2615335 := by exact prefixLift 2615335
  have htrace : WordTrace (prefixWord ++ tailWord_2615335) baseStart_2615335 baseEnd_2615335 := by
    simpa [prefixWord, tailWord_2615335, baseEnd_2615335] using wordTrace_append hprefix tailTrace_2615335
  have hstable : (prefixWord ++ tailWord_2615335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615335).length < 2 ^ (prefixWord ++ tailWord_2615335).sum := by decide
  have hdescent : baseEnd_2615335 < baseStart_2615335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615382 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2615382 : Nat := 118140960795 + 2615382 * 2 ^ 59
def prefixEnd_2615382 : Nat := 4983230072969 + 3 ^ 40 * 2615382 * 2
def baseEnd_2615382 : Nat := 895298707411594359731389

theorem tailTrace_2615382 : CollatzResearch.WordTrace tailWord_2615382 prefixEnd_2615382 895298707411594359731389 := by
  unfold tailWord_2615382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961926138182822533085025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63593878807283440352906933 5961926138182822533085025)
  ·
    refine ⟨4471444603637116899813769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5961926138182822533085025 4471444603637116899813769)
    ·
      refine ⟨3353583452727837674860327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4471444603637116899813769 3353583452727837674860327)
      ·
        refine ⟨5030375179091756512290491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353583452727837674860327 5030375179091756512290491)
        ·
          refine ⟨7545562768637634768435737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030375179091756512290491 7545562768637634768435737)
          ·
            refine ⟨5659172076478226076326803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545562768637634768435737 5659172076478226076326803)
            ·
              refine ⟨8488758114717339114490205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659172076478226076326803 8488758114717339114490205)
              ·
                refine ⟨3183284293019002167933827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8488758114717339114490205 3183284293019002167933827)
                ·
                  refine ⟨4774926439528503251900741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183284293019002167933827 4774926439528503251900741)
                  ·
                    refine ⟨895298707411594359731389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4774926439528503251900741 895298707411594359731389)
                    ·
                      rfl

theorem cell22_2615382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2615382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615382 prefixEnd_2615382 := by exact prefixLift 2615382
  have htrace : WordTrace (prefixWord ++ tailWord_2615382) baseStart_2615382 baseEnd_2615382 := by
    simpa [prefixWord, tailWord_2615382, baseEnd_2615382] using wordTrace_append hprefix tailTrace_2615382
  have hstable : (prefixWord ++ tailWord_2615382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615382).length < 2 ^ (prefixWord ++ tailWord_2615382).sum := by decide
  have hdescent : baseEnd_2615382 < baseStart_2615382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615425 : List Nat := [1, 2, 4, 2, 3, 2, 2, 6]
def baseStart_2615425 : Nat := 118140960795 + 2615425 * 2 ^ 59
def prefixEnd_2615425 : Nat := 4983230072969 + 3 ^ 40 * 2615425 * 2
def baseEnd_2615425 : Nat := 99479269687817397878473

theorem tailTrace_2615425 : CollatzResearch.WordTrace tailWord_2615425 prefixEnd_2615425 99479269687817397878473 := by
  unfold tailWord_2615425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95392386549769378873175729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63594924366512919248783819 95392386549769378873175729)
  ·
    refine ⟨71544289912327034154881797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95392386549769378873175729 71544289912327034154881797)
    ·
      refine ⟨13414554358561318904040337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71544289912327034154881797 13414554358561318904040337)
      ·
        refine ⟨10060915768920989178030253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13414554358561318904040337 10060915768920989178030253)
        ·
          refine ⟨3772843413345370941761345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10060915768920989178030253 3772843413345370941761345)
          ·
            refine ⟨2829632560009028206321009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772843413345370941761345 2829632560009028206321009)
            ·
              refine ⟨2122224420006771154740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829632560009028206321009 2122224420006771154740757)
              ·
                refine ⟨99479269687817397878473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2122224420006771154740757 99479269687817397878473)
                ·
                  rfl

theorem cell22_2615425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 6].length) (baseStart_2615425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615425 prefixEnd_2615425 := by exact prefixLift 2615425
  have htrace : WordTrace (prefixWord ++ tailWord_2615425) baseStart_2615425 baseEnd_2615425 := by
    simpa [prefixWord, tailWord_2615425, baseEnd_2615425] using wordTrace_append hprefix tailTrace_2615425
  have hstable : (prefixWord ++ tailWord_2615425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615425).length < 2 ^ (prefixWord ++ tailWord_2615425).sum := by decide
  have hdescent : baseEnd_2615425 < baseStart_2615425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615481 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 8]
def baseStart_2615481 : Nat := 118140960795 + 2615481 * 2 ^ 59
def prefixEnd_2615481 : Nat := 4983230072969 + 3 ^ 40 * 2615481 * 2
def baseEnd_2615481 : Nat := 298444199044930367168695

theorem tailTrace_2615481 : CollatzResearch.WordTrace tailWord_2615481 prefixEnd_2615481 298444199044930367168695 := by
  unfold tailWord_2615481
  simp only [CollatzResearch.WordTrace]
  refine ⟨95394429037566500437214297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63596286025044333624809531 95394429037566500437214297)
  ·
    refine ⟨71545821778174875327910723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95394429037566500437214297 71545821778174875327910723)
    ·
      refine ⟨107318732667262312991866085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71545821778174875327910723 107318732667262312991866085)
      ·
        refine ⟨20122262375111683685974891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107318732667262312991866085 20122262375111683685974891)
        ·
          refine ⟨30183393562667525528962337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20122262375111683685974891 30183393562667525528962337)
          ·
            refine ⟨22637545172000644146721753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30183393562667525528962337 22637545172000644146721753)
            ·
              refine ⟨16978158879000483110041315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22637545172000644146721753 16978158879000483110041315)
              ·
                refine ⟨25467238318500724665061973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16978158879000483110041315 25467238318500724665061973)
                ·
                  refine ⟨298444199044930367168695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25467238318500724665061973 298444199044930367168695)
                  ·
                    rfl

theorem cell22_2615481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_2615481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615481 prefixEnd_2615481 := by exact prefixLift 2615481
  have htrace : WordTrace (prefixWord ++ tailWord_2615481) baseStart_2615481 baseEnd_2615481 := by
    simpa [prefixWord, tailWord_2615481, baseEnd_2615481] using wordTrace_append hprefix tailTrace_2615481
  have hstable : (prefixWord ++ tailWord_2615481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615481).length < 2 ^ (prefixWord ++ tailWord_2615481).sum := by decide
  have hdescent : baseEnd_2615481 < baseStart_2615481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615511 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2615511 : Nat := 118140960795 + 2615511 * 2 ^ 59
def prefixEnd_2615511 : Nat := 4983230072969 + 3 ^ 40 * 2615511 * 2
def baseEnd_2615511 : Nat := 895342866747881023255993

theorem tailTrace_2615511 : CollatzResearch.WordTrace tailWord_2615511 prefixEnd_2615511 895342866747881023255993 := by
  unfold tailWord_2615511
  simp only [CollatzResearch.WordTrace]
  refine ⟨95395523227457815560806387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63597015484971877040537591 95395523227457815560806387)
  ·
    refine ⟨143093284841186723341209581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95395523227457815560806387 143093284841186723341209581)
    ·
      refine ⟨53659981815445021252953593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143093284841186723341209581 53659981815445021252953593)
      ·
        refine ⟨40244986361583765939715195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53659981815445021252953593 40244986361583765939715195)
        ·
          refine ⟨60367479542375648909572793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40244986361583765939715195 60367479542375648909572793)
          ·
            refine ⟨45275609656781736682179595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60367479542375648909572793 45275609656781736682179595)
            ·
              refine ⟨67913414485172605023269393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45275609656781736682179595 67913414485172605023269393)
              ·
                refine ⟨50935060863879453767452045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67913414485172605023269393 50935060863879453767452045)
                ·
                  refine ⟨19100647823954795162794517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50935060863879453767452045 19100647823954795162794517)
                  ·
                    refine ⟨895342866747881023255993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19100647823954795162794517 895342866747881023255993)
                    ·
                      rfl

theorem cell22_2615511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2615511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615511 prefixEnd_2615511 := by exact prefixLift 2615511
  have htrace : WordTrace (prefixWord ++ tailWord_2615511) baseStart_2615511 baseEnd_2615511 := by
    simpa [prefixWord, tailWord_2615511, baseEnd_2615511] using wordTrace_append hprefix tailTrace_2615511
  have hstable : (prefixWord ++ tailWord_2615511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615511).length < 2 ^ (prefixWord ++ tailWord_2615511).sum := by decide
  have hdescent : baseEnd_2615511 < baseStart_2615511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615513 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_2615513 : Nat := 118140960795 + 2615513 * 2 ^ 59
def prefixEnd_2615513 : Nat := 4983230072969 + 3 ^ 40 * 2615513 * 2
def baseEnd_2615513 : Nat := 895343551388753684705987

theorem tailTrace_2615513 : CollatzResearch.WordTrace tailWord_2615513 prefixEnd_2615513 895343551388753684705987 := by
  unfold tailWord_2615513
  simp only [CollatzResearch.WordTrace]
  refine ⟨95395596173450569902379193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63597064115633713268252795 95395596173450569902379193)
  ·
    refine ⟨71546697130087927426784395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95395596173450569902379193 71546697130087927426784395)
    ·
      refine ⟨107320045695131891140176593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71546697130087927426784395 107320045695131891140176593)
      ·
        refine ⟨80490034271348918355132445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107320045695131891140176593 80490034271348918355132445)
        ·
          refine ⟨30183762851755844383174667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80490034271348918355132445 30183762851755844383174667)
          ·
            refine ⟨45275644277633766574762001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30183762851755844383174667 45275644277633766574762001)
            ·
              refine ⟨33956733208225324931071501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45275644277633766574762001 33956733208225324931071501)
              ·
                refine ⟨12733774953084496849151813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33956733208225324931071501 12733774953084496849151813)
                ·
                  refine ⟨2387582803703343159215965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12733774953084496849151813 2387582803703343159215965)
                  ·
                    refine ⟨895343551388753684705987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387582803703343159215965 895343551388753684705987)
                    ·
                      rfl

theorem cell22_2615513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_2615513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615513 prefixEnd_2615513 := by exact prefixLift 2615513
  have htrace : WordTrace (prefixWord ++ tailWord_2615513) baseStart_2615513 baseEnd_2615513 := by
    simpa [prefixWord, tailWord_2615513, baseEnd_2615513] using wordTrace_append hprefix tailTrace_2615513
  have hstable : (prefixWord ++ tailWord_2615513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615513).length < 2 ^ (prefixWord ++ tailWord_2615513).sum := by decide
  have hdescent : baseEnd_2615513 < baseStart_2615513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615530 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2615530 : Nat := 118140960795 + 2615530 * 2 ^ 59
def prefixEnd_2615530 : Nat := 4983230072969 + 3 ^ 40 * 2615530 * 2
def baseEnd_2615530 : Nat := 895349370836171307030935

theorem tailTrace_2615530 : CollatzResearch.WordTrace tailWord_2615530 prefixEnd_2615530 895349370836171307030935 := by
  unfold tailWord_2615530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849054053597245451437011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63597477476259321203832029 23849054053597245451437011)
  ·
    refine ⟨35773581080395868177155517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23849054053597245451437011 35773581080395868177155517)
    ·
      refine ⟨13415092905148450566433319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35773581080395868177155517 13415092905148450566433319)
      ·
        refine ⟨20122639357722675849649979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13415092905148450566433319 20122639357722675849649979)
        ·
          refine ⟨30183959036584013774474969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20122639357722675849649979 30183959036584013774474969)
          ·
            refine ⟨22637969277438010330856227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30183959036584013774474969 22637969277438010330856227)
            ·
              refine ⟨33956953916157015496284341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22637969277438010330856227 33956953916157015496284341)
              ·
                refine ⟨3183464429639720202776657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33956953916157015496284341 3183464429639720202776657)
                ·
                  refine ⟨2387598322229790152082493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183464429639720202776657 2387598322229790152082493)
                  ·
                    refine ⟨895349370836171307030935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387598322229790152082493 895349370836171307030935)
                    ·
                      rfl

theorem cell22_2615530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2615530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615530 prefixEnd_2615530 := by exact prefixLift 2615530
  have htrace : WordTrace (prefixWord ++ tailWord_2615530) baseStart_2615530 baseEnd_2615530 := by
    simpa [prefixWord, tailWord_2615530, baseEnd_2615530] using wordTrace_append hprefix tailTrace_2615530
  have hstable : (prefixWord ++ tailWord_2615530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615530).length < 2 ^ (prefixWord ++ tailWord_2615530).sum := by decide
  have hdescent : baseEnd_2615530 < baseStart_2615530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615575 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2615575 : Nat := 118140960795 + 2615575 * 2 ^ 59
def prefixEnd_2615575 : Nat := 4983230072969 + 3 ^ 40 * 2615575 * 2
def baseEnd_2615575 : Nat := 895364775255806189655797

theorem tailTrace_2615575 : CollatzResearch.WordTrace tailWord_2615575 prefixEnd_2615575 895364775255806189655797 := by
  unfold tailWord_2615575
  simp only [CollatzResearch.WordTrace]
  refine ⟨95397857499225954491136179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63598571666150636327424119 95397857499225954491136179)
  ·
    refine ⟨143096786248838931736704269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95397857499225954491136179 143096786248838931736704269)
    ·
      refine ⟨53661294843314599401264101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143096786248838931736704269 53661294843314599401264101)
      ·
        refine ⟨10061492783121487387737019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53661294843314599401264101 10061492783121487387737019)
        ·
          refine ⟨15092239174682231081605529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061492783121487387737019 15092239174682231081605529)
          ·
            refine ⟨11319179381011673311204147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15092239174682231081605529 11319179381011673311204147)
            ·
              refine ⟨16978769071517509966806221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11319179381011673311204147 16978769071517509966806221)
              ·
                refine ⟨6367038401819066237552333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16978769071517509966806221 6367038401819066237552333)
                ·
                  refine ⟨2387639400682149839082125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367038401819066237552333 2387639400682149839082125)
                  ·
                    refine ⟨895364775255806189655797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387639400682149839082125 895364775255806189655797)
                    ·
                      rfl

theorem cell22_2615575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2615575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615575 prefixEnd_2615575 := by exact prefixLift 2615575
  have htrace : WordTrace (prefixWord ++ tailWord_2615575) baseStart_2615575 baseEnd_2615575 := by
    simpa [prefixWord, tailWord_2615575, baseEnd_2615575] using wordTrace_append hprefix tailTrace_2615575
  have hstable : (prefixWord ++ tailWord_2615575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615575).length < 2 ^ (prefixWord ++ tailWord_2615575).sum := by decide
  have hdescent : baseEnd_2615575 < baseStart_2615575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615594 : List Nat := [3, 1, 4, 2, 3, 1, 2, 6]
def baseStart_2615594 : Nat := 118140960795 + 2615594 * 2 ^ 59
def prefixEnd_2615594 : Nat := 4983230072969 + 3 ^ 40 * 2615594 * 2
def baseEnd_2615594 : Nat := 99485697704899608158971

theorem tailTrace_2615594 : CollatzResearch.WordTrace tailWord_2615594 prefixEnd_2615594 99485697704899608158971 := by
  unfold tailWord_2615594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23849637621539280184019459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63599033657438080490718557 23849637621539280184019459)
  ·
    refine ⟨35774456432308920276029189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23849637621539280184019459 35774456432308920276029189)
    ·
      refine ⟨6707710581057922551755473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35774456432308920276029189 6707710581057922551755473)
      ·
        refine ⟨5030782935793441913816605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6707710581057922551755473 5030782935793441913816605)
        ·
          refine ⟨1886543600922540717681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5030782935793441913816605 1886543600922540717681227)
          ·
            refine ⟨2829815401383811076521841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886543600922540717681227 2829815401383811076521841)
            ·
              refine ⟨2122361551037858307391381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829815401383811076521841 2122361551037858307391381)
              ·
                refine ⟨99485697704899608158971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2122361551037858307391381 99485697704899608158971)
                ·
                  rfl

theorem cell22_2615594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_2615594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615594 prefixEnd_2615594 := by exact prefixLift 2615594
  have htrace : WordTrace (prefixWord ++ tailWord_2615594) baseStart_2615594 baseEnd_2615594 := by
    simpa [prefixWord, tailWord_2615594, baseEnd_2615594] using wordTrace_append hprefix tailTrace_2615594
  have hstable : (prefixWord ++ tailWord_2615594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615594).length < 2 ^ (prefixWord ++ tailWord_2615594).sum := by decide
  have hdescent : baseEnd_2615594 < baseStart_2615594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615609 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 1, 3]
def baseStart_2615609 : Nat := 118140960795 + 2615609 * 2 ^ 59
def prefixEnd_2615609 : Nat := 4983230072969 + 3 ^ 40 * 2615609 * 2
def baseEnd_2615609 : Nat := 895376414150641434305693

theorem tailTrace_2615609 : CollatzResearch.WordTrace tailWord_2615609 prefixEnd_2615609 895376414150641434305693 := by
  unfold tailWord_2615609
  simp only [CollatzResearch.WordTrace]
  refine ⟨95399097581102778297873881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63599398387401852198582587 95399097581102778297873881)
  ·
    refine ⟨71549323185827083723405411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95399097581102778297873881 71549323185827083723405411)
    ·
      refine ⟨107323984778740625585108117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71549323185827083723405411 107323984778740625585108117)
      ·
        refine ⟨5030811786503466824301943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107323984778740625585108117 5030811786503466824301943)
        ·
          refine ⟨7546217679755200236452915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030811786503466824301943 7546217679755200236452915)
          ·
            refine ⟨11319326519632800354679373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546217679755200236452915 11319326519632800354679373)
            ·
              refine ⟨4244747444862300133004765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11319326519632800354679373 4244747444862300133004765)
              ·
                refine ⟨1591780291823362549876787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4244747444862300133004765 1591780291823362549876787)
                ·
                  refine ⟨2387670437735043824815181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591780291823362549876787 2387670437735043824815181)
                  ·
                    refine ⟨895376414150641434305693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387670437735043824815181 895376414150641434305693)
                    ·
                      rfl

theorem cell22_2615609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 3].length) (baseStart_2615609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615609 prefixEnd_2615609 := by exact prefixLift 2615609
  have htrace : WordTrace (prefixWord ++ tailWord_2615609) baseStart_2615609 baseEnd_2615609 := by
    simpa [prefixWord, tailWord_2615609, baseEnd_2615609] using wordTrace_append hprefix tailTrace_2615609
  have hstable : (prefixWord ++ tailWord_2615609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615609).length < 2 ^ (prefixWord ++ tailWord_2615609).sum := by decide
  have hdescent : baseEnd_2615609 < baseStart_2615609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615669 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2615669 : Nat := 118140960795 + 2615669 * 2 ^ 59
def prefixEnd_2615669 : Nat := 4983230072969 + 3 ^ 40 * 2615669 * 2
def baseEnd_2615669 : Nat := 895396953376821277805509

theorem tailTrace_2615669 : CollatzResearch.WordTrace tailWord_2615669 prefixEnd_2615669 895396953376821277805509 := by
  unfold tailWord_2615669
  simp only [CollatzResearch.WordTrace]
  refine ⟨95401285960885408545058061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63600857307256939030038707 95401285960885408545058061)
  ·
    refine ⟨35775482235332028204396773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95401285960885408545058061 35775482235332028204396773)
    ·
      refine ⟨6707902919124755288324395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35775482235332028204396773 6707902919124755288324395)
      ·
        refine ⟨10061854378687132932486593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707902919124755288324395 10061854378687132932486593)
        ·
          refine ⟨7546390784015349699364945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10061854378687132932486593 7546390784015349699364945)
          ·
            refine ⟨5659793088011512274523709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546390784015349699364945 5659793088011512274523709)
            ·
              refine ⟨2122422408004317102946391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5659793088011512274523709 2122422408004317102946391)
              ·
                refine ⟨3183633612006475654419587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122422408004317102946391 3183633612006475654419587)
                ·
                  refine ⟨4775450418009713481629381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183633612006475654419587 4775450418009713481629381)
                  ·
                    refine ⟨895396953376821277805509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775450418009713481629381 895396953376821277805509)
                    ·
                      rfl

theorem cell22_2615669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2615669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615669 prefixEnd_2615669 := by exact prefixLift 2615669
  have htrace : WordTrace (prefixWord ++ tailWord_2615669) baseStart_2615669 baseEnd_2615669 := by
    simpa [prefixWord, tailWord_2615669, baseEnd_2615669] using wordTrace_append hprefix tailTrace_2615669
  have hstable : (prefixWord ++ tailWord_2615669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615669).length < 2 ^ (prefixWord ++ tailWord_2615669).sum := by decide
  have hdescent : baseEnd_2615669 < baseStart_2615669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615821 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2615821 : Nat := 118140960795 + 2615821 * 2 ^ 59
def prefixEnd_2615821 : Nat := 4983230072969 + 3 ^ 40 * 2615821 * 2
def baseEnd_2615821 : Nat := 895448986083143548005043

theorem tailTrace_2615821 : CollatzResearch.WordTrace tailWord_2615821 prefixEnd_2615821 895448986083143548005043 := by
  unfold tailWord_2615821
  simp only [CollatzResearch.WordTrace]
  refine ⟨95406829856334738504591317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63604553237556492336394211 95406829856334738504591317)
  ·
    refine ⟨2236097574757845433701359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 95406829856334738504591317 2236097574757845433701359)
    ·
      refine ⟨3354146362136768150552039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236097574757845433701359 3354146362136768150552039)
      ·
        refine ⟨5031219543205152225828059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354146362136768150552039 5031219543205152225828059)
        ·
          refine ⟨7546829314807728338742089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031219543205152225828059 7546829314807728338742089)
          ·
            refine ⟨5660121986105796254056567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546829314807728338742089 5660121986105796254056567)
            ·
              refine ⟨8490182979158694381084851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660121986105796254056567 8490182979158694381084851)
              ·
                refine ⟨12735274468738041571627277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8490182979158694381084851 12735274468738041571627277)
                ·
                  refine ⟨4775727925776765589360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12735274468738041571627277 4775727925776765589360229)
                  ·
                    refine ⟨895448986083143548005043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775727925776765589360229 895448986083143548005043)
                    ·
                      rfl

theorem cell22_2615821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2615821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615821 prefixEnd_2615821 := by exact prefixLift 2615821
  have htrace : WordTrace (prefixWord ++ tailWord_2615821) baseStart_2615821 baseEnd_2615821 := by
    simpa [prefixWord, tailWord_2615821, baseEnd_2615821] using wordTrace_append hprefix tailTrace_2615821
  have hstable : (prefixWord ++ tailWord_2615821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615821).length < 2 ^ (prefixWord ++ tailWord_2615821).sum := by decide
  have hdescent : baseEnd_2615821 < baseStart_2615821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615832 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_2615832 : Nat := 118140960795 + 2615832 * 2 ^ 59
def prefixEnd_2615832 : Nat := 4983230072969 + 3 ^ 40 * 2615832 * 2
def baseEnd_2615832 : Nat := 895452751607943185980009

theorem tailTrace_2615832 : CollatzResearch.WordTrace tailWord_2615832 prefixEnd_2615832 895452751607943185980009 := by
  unfold tailWord_2615832
  simp only [CollatzResearch.WordTrace]
  refine ⟨47703615529647443691620875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63604820706196591588827833 47703615529647443691620875)
  ·
    refine ⟨71555423294471165537431313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47703615529647443691620875 71555423294471165537431313)
    ·
      refine ⟨53666567470853374153073485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71555423294471165537431313 53666567470853374153073485)
      ·
        refine ⟨20124962801570015307402557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53666567470853374153073485 20124962801570015307402557)
        ·
          refine ⟨7546861050588755740275959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20124962801570015307402557 7546861050588755740275959)
          ·
            refine ⟨11320291575883133610413939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546861050588755740275959 11320291575883133610413939)
            ·
              refine ⟨16980437363824700415620909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11320291575883133610413939 16980437363824700415620909)
              ·
                refine ⟨6367664011434262655857841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16980437363824700415620909 6367664011434262655857841)
                ·
                  refine ⟨4775748008575696991893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6367664011434262655857841 4775748008575696991893381)
                  ·
                    refine ⟨895452751607943185980009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775748008575696991893381 895452751607943185980009)
                    ·
                      rfl

theorem cell22_2615832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_2615832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615832 prefixEnd_2615832 := by exact prefixLift 2615832
  have htrace : WordTrace (prefixWord ++ tailWord_2615832) baseStart_2615832 baseEnd_2615832 := by
    simpa [prefixWord, tailWord_2615832, baseEnd_2615832] using wordTrace_append hprefix tailTrace_2615832
  have hstable : (prefixWord ++ tailWord_2615832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615832).length < 2 ^ (prefixWord ++ tailWord_2615832).sum := by decide
  have hdescent : baseEnd_2615832 < baseStart_2615832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615847 : List Nat := [1, 1, 7, 2, 11]
def baseStart_2615847 : Nat := 118140960795 + 2615847 * 2 ^ 59
def prefixEnd_2615847 : Nat := 4983230072969 + 3 ^ 40 * 2615847 * 2
def baseEnd_2615847 : Nat := 3685011878248922415041

theorem tailTrace_2615847 : CollatzResearch.WordTrace tailWord_2615847 prefixEnd_2615847 3685011878248922415041 := by
  unfold tailWord_2615847
  simp only [CollatzResearch.WordTrace]
  refine ⟨95407778154240544945037795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63605185436160363296691863 95407778154240544945037795)
  ·
    refine ⟨143111667231360817417556693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95407778154240544945037795 143111667231360817417556693)
    ·
      refine ⟨3354179700735019158223985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 143111667231360817417556693 3354179700735019158223985)
      ·
        refine ⟨2515634775551264368667989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354179700735019158223985 2515634775551264368667989)
        ·
          refine ⟨3685011878248922415041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2515634775551264368667989 3685011878248922415041)
          ·
            rfl

theorem cell22_2615847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 11].length) (baseStart_2615847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615847 prefixEnd_2615847 := by exact prefixLift 2615847
  have htrace : WordTrace (prefixWord ++ tailWord_2615847) baseStart_2615847 baseEnd_2615847 := by
    simpa [prefixWord, tailWord_2615847, baseEnd_2615847] using wordTrace_append hprefix tailTrace_2615847
  have hstable : (prefixWord ++ tailWord_2615847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615847).length < 2 ^ (prefixWord ++ tailWord_2615847).sum := by decide
  have hdescent : baseEnd_2615847 < baseStart_2615847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615879 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2615879 : Nat := 118140960795 + 2615879 * 2 ^ 59
def prefixEnd_2615879 : Nat := 4983230072969 + 3 ^ 40 * 2615879 * 2
def baseEnd_2615879 : Nat := 895468840668450730054865

theorem tailTrace_2615879 : CollatzResearch.WordTrace tailWord_2615879 prefixEnd_2615879 895468840668450730054865 := by
  unfold tailWord_2615879
  simp only [CollatzResearch.WordTrace]
  refine ⟨95408945290124614410202691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63605963526749742940135127 95408945290124614410202691)
  ·
    refine ⟨143113417935186921615304037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95408945290124614410202691 143113417935186921615304037)
    ·
      refine ⟨26833765862847547802869507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143113417935186921615304037 26833765862847547802869507)
      ·
        refine ⟨40250648794271321704304261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26833765862847547802869507 40250648794271321704304261)
        ·
          refine ⟨7546996648925872819557049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40250648794271321704304261 7546996648925872819557049)
          ·
            refine ⟨5660247486694404614667787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7546996648925872819557049 5660247486694404614667787)
            ·
              refine ⟨8490371230041606922001681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660247486694404614667787 8490371230041606922001681)
              ·
                refine ⟨6367778422531205191501261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8490371230041606922001681 6367778422531205191501261)
                ·
                  refine ⟨2387916908449201946812973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367778422531205191501261 2387916908449201946812973)
                  ·
                    refine ⟨895468840668450730054865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387916908449201946812973 895468840668450730054865)
                    ·
                      rfl

theorem cell22_2615879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2615879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615879 prefixEnd_2615879 := by exact prefixLift 2615879
  have htrace : WordTrace (prefixWord ++ tailWord_2615879) baseStart_2615879 baseEnd_2615879 := by
    simpa [prefixWord, tailWord_2615879, baseEnd_2615879] using wordTrace_append hprefix tailTrace_2615879
  have hstable : (prefixWord ++ tailWord_2615879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615879).length < 2 ^ (prefixWord ++ tailWord_2615879).sum := by decide
  have hdescent : baseEnd_2615879 < baseStart_2615879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615902 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2615902 : Nat := 118140960795 + 2615902 * 2 ^ 59
def prefixEnd_2615902 : Nat := 4983230072969 + 3 ^ 40 * 2615902 * 2
def baseEnd_2615902 : Nat := 895476714038486336729795

theorem tailTrace_2615902 : CollatzResearch.WordTrace tailWord_2615902 prefixEnd_2615902 895476714038486336729795 := by
  unfold tailWord_2615902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926223021130161167286245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63606522779360859558859973 11926223021130161167286245)
  ·
    refine ⟨2236166816461905218866171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11926223021130161167286245 2236166816461905218866171)
    ·
      refine ⟨3354250224692857828299257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236166816461905218866171 3354250224692857828299257)
      ·
        refine ⟨2515687668519643371224443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354250224692857828299257 2515687668519643371224443)
        ·
          refine ⟨3773531502779465056836665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515687668519643371224443 3773531502779465056836665)
          ·
            refine ⟨2830148627084598792627499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773531502779465056836665 2830148627084598792627499)
            ·
              refine ⟨4245222940626898188941249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830148627084598792627499 4245222940626898188941249)
              ·
                refine ⟨3183917205470173641705937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245222940626898188941249 3183917205470173641705937)
                ·
                  refine ⟨2387937904102630231279453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183917205470173641705937 2387937904102630231279453)
                  ·
                    refine ⟨895476714038486336729795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2387937904102630231279453 895476714038486336729795)
                    ·
                      rfl

theorem cell22_2615902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2615902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615902 prefixEnd_2615902 := by exact prefixLift 2615902
  have htrace : WordTrace (prefixWord ++ tailWord_2615902) baseStart_2615902 baseEnd_2615902 := by
    simpa [prefixWord, tailWord_2615902, baseEnd_2615902] using wordTrace_append hprefix tailTrace_2615902
  have hstable : (prefixWord ++ tailWord_2615902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615902).length < 2 ^ (prefixWord ++ tailWord_2615902).sum := by decide
  have hdescent : baseEnd_2615902 < baseStart_2615902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615937 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 6]
def baseStart_2615937 : Nat := 118140960795 + 2615937 * 2 ^ 59
def prefixEnd_2615937 : Nat := 4983230072969 + 3 ^ 40 * 2615937 * 2
def baseEnd_2615937 : Nat := 298496231751252637368229

theorem tailTrace_2615937 : CollatzResearch.WordTrace tailWord_2615937 prefixEnd_2615937 298496231751252637368229 := by
  unfold tailWord_2615937
  simp only [CollatzResearch.WordTrace]
  refine ⟨95411060723914490315814065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63607373815942993543876043 95411060723914490315814065)
  ·
    refine ⟨71558295542935867736860549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95411060723914490315814065 71558295542935867736860549)
    ·
      refine ⟨13417180414300475200661353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71558295542935867736860549 13417180414300475200661353)
      ·
        refine ⟨10062885310725356400496015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13417180414300475200661353 10062885310725356400496015)
        ·
          refine ⟨15094327966088034600744023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10062885310725356400496015 15094327966088034600744023)
          ·
            refine ⟨22641491949132051901116035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15094327966088034600744023 22641491949132051901116035)
            ·
              refine ⟨33962237923698077851674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22641491949132051901116035 33962237923698077851674053)
              ·
                refine ⟨6367919610693389597188885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33962237923698077851674053 6367919610693389597188885)
                ·
                  refine ⟨298496231751252637368229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6367919610693389597188885 298496231751252637368229)
                  ·
                    rfl

theorem cell22_2615937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_2615937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615937 prefixEnd_2615937 := by exact prefixLift 2615937
  have htrace : WordTrace (prefixWord ++ tailWord_2615937) baseStart_2615937 baseEnd_2615937 := by
    simpa [prefixWord, tailWord_2615937, baseEnd_2615937] using wordTrace_append hprefix tailTrace_2615937
  have hstable : (prefixWord ++ tailWord_2615937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615937).length < 2 ^ (prefixWord ++ tailWord_2615937).sum := by decide
  have hdescent : baseEnd_2615937 < baseStart_2615937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615956 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2615956 : Nat := 118140960795 + 2615956 * 2 ^ 59
def prefixEnd_2615956 : Nat := 4983230072969 + 3 ^ 40 * 2615956 * 2
def baseEnd_2615956 : Nat := 895495199342048195879629

theorem tailTrace_2615956 : CollatzResearch.WordTrace tailWord_2615956 prefixEnd_2615956 895495199342048195879629 := by
  unfold tailWord_2615956
  simp only [CollatzResearch.WordTrace]
  refine ⟨47705876855422828280377861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63607835807230437707170481 47705876855422828280377861)
  ·
    refine ⟨8944851910391780302570849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47705876855422828280377861 8944851910391780302570849)
    ·
      refine ⟨6708638932793835226928137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8944851910391780302570849 6708638932793835226928137)
      ·
        refine ⟨5031479199595376420196103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6708638932793835226928137 5031479199595376420196103)
        ·
          refine ⟨7547218799393064630294155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031479199595376420196103 7547218799393064630294155)
          ·
            refine ⟨11320828199089596945441233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7547218799393064630294155 11320828199089596945441233)
            ·
              refine ⟨8490621149317197709080925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11320828199089596945441233 8490621149317197709080925)
              ·
                refine ⟨3183982930993949140905347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8490621149317197709080925 3183982930993949140905347)
                ·
                  refine ⟨4775974396490923711358021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183982930993949140905347 4775974396490923711358021)
                  ·
                    refine ⟨895495199342048195879629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4775974396490923711358021 895495199342048195879629)
                    ·
                      rfl

theorem cell22_2615956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2615956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615956 prefixEnd_2615956 := by exact prefixLift 2615956
  have htrace : WordTrace (prefixWord ++ tailWord_2615956) baseStart_2615956 baseEnd_2615956 := by
    simpa [prefixWord, tailWord_2615956, baseEnd_2615956] using wordTrace_append hprefix tailTrace_2615956
  have hstable : (prefixWord ++ tailWord_2615956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615956).length < 2 ^ (prefixWord ++ tailWord_2615956).sum := by decide
  have hdescent : baseEnd_2615956 < baseStart_2615956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615990 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2615990 : Nat := 118140960795 + 2615990 * 2 ^ 59
def prefixEnd_2615990 : Nat := 4983230072969 + 3 ^ 40 * 2615990 * 2
def baseEnd_2615990 : Nat := 895506838236883440529525

theorem tailTrace_2615990 : CollatzResearch.WordTrace tailWord_2615990 prefixEnd_2615990 895506838236883440529525 := by
  unfold tailWord_2615990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963312112045155022968339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63608662528481653578328949 5963312112045155022968339)
  ·
    refine ⟨8944968168067732534452509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5963312112045155022968339 8944968168067732534452509)
    ·
      refine ⟨3354363063025399700419691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8944968168067732534452509 3354363063025399700419691)
      ·
        refine ⟨5031544594538099550629537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354363063025399700419691 5031544594538099550629537)
        ·
          refine ⟨3773658445903574662972153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031544594538099550629537 3773658445903574662972153)
          ·
            refine ⟨2830243834427680997229115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773658445903574662972153 2830243834427680997229115)
            ·
              refine ⟨4245365751641521495843673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830243834427680997229115 4245365751641521495843673)
              ·
                refine ⟨3184024313731141121882755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245365751641521495843673 3184024313731141121882755)
                ·
                  refine ⟨4776036470596711682824133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184024313731141121882755 4776036470596711682824133)
                  ·
                    refine ⟨895506838236883440529525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776036470596711682824133 895506838236883440529525)
                    ·
                      rfl

theorem cell22_2615990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2615990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2615990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2615990 prefixEnd_2615990 := by exact prefixLift 2615990
  have htrace : WordTrace (prefixWord ++ tailWord_2615990) baseStart_2615990 baseEnd_2615990 := by
    simpa [prefixWord, tailWord_2615990, baseEnd_2615990] using wordTrace_append hprefix tailTrace_2615990
  have hstable : (prefixWord ++ tailWord_2615990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615990).length < 2 ^ (prefixWord ++ tailWord_2615990).sum := by decide
  have hdescent : baseEnd_2615990 < baseStart_2615990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616052 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2616052 : Nat := 118140960795 + 2616052 * 2 ^ 59
def prefixEnd_2616052 : Nat := 4983230072969 + 3 ^ 40 * 2616052 * 2
def baseEnd_2616052 : Nat := 895528062103935945479335

theorem tailTrace_2616052 : CollatzResearch.WordTrace tailWord_2616052 prefixEnd_2616052 895528062103935945479335 := by
  unfold tailWord_2616052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47707627559248932478125205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63610170078998576637500273 47707627559248932478125205)
  ·
    refine ⟨2236295041839793709912119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47707627559248932478125205 2236295041839793709912119)
    ·
      refine ⟨3354442562759690564868179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236295041839793709912119 3354442562759690564868179)
      ·
        refine ⟨5031663844139535847302269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354442562759690564868179 5031663844139535847302269)
        ·
          refine ⟨1886873941552325942738351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5031663844139535847302269 1886873941552325942738351)
          ·
            refine ⟨2830310912328488914107527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886873941552325942738351 2830310912328488914107527)
            ·
              refine ⟨4245466368492733371161291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830310912328488914107527 4245466368492733371161291)
              ·
                refine ⟨6368199552739100056741937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245466368492733371161291 6368199552739100056741937)
                ·
                  refine ⟨4776149664554325042556453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368199552739100056741937 4776149664554325042556453)
                  ·
                    refine ⟨895528062103935945479335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776149664554325042556453 895528062103935945479335)
                    ·
                      rfl

theorem cell22_2616052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2616052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616052 prefixEnd_2616052 := by exact prefixLift 2616052
  have htrace : WordTrace (prefixWord ++ tailWord_2616052) baseStart_2616052 baseEnd_2616052 := by
    simpa [prefixWord, tailWord_2616052, baseEnd_2616052] using wordTrace_append hprefix tailTrace_2616052
  have hstable : (prefixWord ++ tailWord_2616052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616052).length < 2 ^ (prefixWord ++ tailWord_2616052).sum := by decide
  have hdescent : baseEnd_2616052 < baseStart_2616052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616119 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2616119 : Nat := 118140960795 + 2616119 * 2 ^ 59
def prefixEnd_2616119 : Nat := 4983230072969 + 3 ^ 40 * 2616119 * 2
def baseEnd_2616119 : Nat := 895550997573170104054129

theorem tailTrace_2616119 : CollatzResearch.WordTrace tailWord_2616119 prefixEnd_2616119 895550997573170104054129 := by
  unfold tailWord_2616119
  simp only [CollatzResearch.WordTrace]
  refine ⟨95417698809255135398939411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63611799206170090265959607 95417698809255135398939411)
  ·
    refine ⟨143126548213882703098409117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95417698809255135398939411 143126548213882703098409117)
    ·
      refine ⟨53672455580206013661903419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143126548213882703098409117 53672455580206013661903419)
      ·
        refine ⟨80508683370309020492855129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53672455580206013661903419 80508683370309020492855129)
        ·
          refine ⟨60381512527731765369641347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80508683370309020492855129 60381512527731765369641347)
          ·
            refine ⟨90572268791597648054462021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60381512527731765369641347 90572268791597648054462021)
            ·
              refine ⟨16982300398424559010211629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90572268791597648054462021 16982300398424559010211629)
              ·
                refine ⟨6368362649409209628829361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16982300398424559010211629 6368362649409209628829361)
                ·
                  refine ⟨4776271987056907221622021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368362649409209628829361 4776271987056907221622021)
                  ·
                    refine ⟨895550997573170104054129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776271987056907221622021 895550997573170104054129)
                    ·
                      rfl

theorem cell22_2616119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2616119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616119 prefixEnd_2616119 := by exact prefixLift 2616119
  have htrace : WordTrace (prefixWord ++ tailWord_2616119) baseStart_2616119 baseEnd_2616119 := by
    simpa [prefixWord, tailWord_2616119, baseEnd_2616119] using wordTrace_append hprefix tailTrace_2616119
  have hstable : (prefixWord ++ tailWord_2616119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616119).length < 2 ^ (prefixWord ++ tailWord_2616119).sum := by decide
  have hdescent : baseEnd_2616119 < baseStart_2616119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616200 : List Nat := [2, 1, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_2616200 : Nat := 118140960795 + 2616200 * 2 ^ 59
def prefixEnd_2616200 : Nat := 4983230072969 + 3 ^ 40 * 2616200 * 2
def baseEnd_2616200 : Nat := 895578725528512892778881

theorem tailTrace_2616200 : CollatzResearch.WordTrace tailWord_2616200 prefixEnd_2616200 895578725528512892778881 := by
  unfold tailWord_2616200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47710326560980843116319027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63613768747974457488425369 47710326560980843116319027)
  ·
    refine ⟨71565489841471264674478541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47710326560980843116319027 71565489841471264674478541)
    ·
      refine ⟨26837058690551724252929453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71565489841471264674478541 26837058690551724252929453)
      ·
        refine ⟨10063897008956896594848545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26837058690551724252929453 10063897008956896594848545)
        ·
          refine ⟨7547922756717672446136409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10063897008956896594848545 7547922756717672446136409)
          ·
            refine ⟨5660942067538254334602307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7547922756717672446136409 5660942067538254334602307)
            ·
              refine ⟨8491413101307381501903461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660942067538254334602307 8491413101307381501903461)
              ·
                refine ⟨1592139956495134031606899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8491413101307381501903461 1592139956495134031606899)
                ·
                  refine ⟨2388209934742701047410349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592139956495134031606899 2388209934742701047410349)
                  ·
                    refine ⟨895578725528512892778881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388209934742701047410349 895578725528512892778881)
                    ·
                      rfl

theorem cell22_2616200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_2616200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616200 prefixEnd_2616200 := by exact prefixLift 2616200
  have htrace : WordTrace (prefixWord ++ tailWord_2616200) baseStart_2616200 baseEnd_2616200 := by
    simpa [prefixWord, tailWord_2616200, baseEnd_2616200] using wordTrace_append hprefix tailTrace_2616200
  have hstable : (prefixWord ++ tailWord_2616200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616200).length < 2 ^ (prefixWord ++ tailWord_2616200).sum := by decide
  have hdescent : baseEnd_2616200 < baseStart_2616200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616224 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_2616224 : Nat := 118140960795 + 2616224 * 2 ^ 59
def prefixEnd_2616224 : Nat := 4983230072969 + 3 ^ 40 * 2616224 * 2
def baseEnd_2616224 : Nat := 298528980406328276726269

theorem tailTrace_2616224 : CollatzResearch.WordTrace tailWord_2616224 prefixEnd_2616224 298528980406328276726269 := by
  unfold tailWord_2616224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47710764236937369165755863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63614352315916492221007817 47710764236937369165755863)
  ·
    refine ⟨71566146355406053748633795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47710764236937369165755863 71566146355406053748633795)
    ·
      refine ⟨107349219533109080622950693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71566146355406053748633795 107349219533109080622950693)
      ·
        refine ⟨20127978662457952616803255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107349219533109080622950693 20127978662457952616803255)
        ·
          refine ⟨30191967993686928925204883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20127978662457952616803255 30191967993686928925204883)
          ·
            refine ⟨45287951990530393387807325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30191967993686928925204883 45287951990530393387807325)
            ·
              refine ⟨16982981996448897520427747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45287951990530393387807325 16982981996448897520427747)
              ·
                refine ⟨25474472994673346280641621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16982981996448897520427747 25474472994673346280641621)
                ·
                  refine ⟨298528980406328276726269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25474472994673346280641621 298528980406328276726269)
                  ·
                    rfl

theorem cell22_2616224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_2616224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616224 prefixEnd_2616224 := by exact prefixLift 2616224
  have htrace : WordTrace (prefixWord ++ tailWord_2616224) baseStart_2616224 baseEnd_2616224 := by
    simpa [prefixWord, tailWord_2616224, baseEnd_2616224] using wordTrace_append hprefix tailTrace_2616224
  have hstable : (prefixWord ++ tailWord_2616224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616224).length < 2 ^ (prefixWord ++ tailWord_2616224).sum := by decide
  have hdescent : baseEnd_2616224 < baseStart_2616224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616239 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2616239 : Nat := 118140960795 + 2616239 * 2 ^ 59
def prefixEnd_2616239 : Nat := 4983230072969 + 3 ^ 40 * 2616239 * 2
def baseEnd_2616239 : Nat := 895592076025529791053761

theorem tailTrace_2616239 : CollatzResearch.WordTrace tailWord_2616239 prefixEnd_2616239 895592076025529791053761 := by
  unfold tailWord_2616239
  simp only [CollatzResearch.WordTrace]
  refine ⟨95422075568820395893307771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63614717045880263928871847 95422075568820395893307771)
  ·
    refine ⟨143133113353230593839961657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95422075568820395893307771 143133113353230593839961657)
    ·
      refine ⟨107349835014922945379971243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143133113353230593839961657 107349835014922945379971243)
      ·
        refine ⟨161024752522384418069956865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107349835014922945379971243 161024752522384418069956865)
        ·
          refine ⟨120768564391788313552467649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161024752522384418069956865 120768564391788313552467649)
          ·
            refine ⟨90576423293841235164350737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120768564391788313552467649 90576423293841235164350737)
            ·
              refine ⟨67932317470380926373263053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90576423293841235164350737 67932317470380926373263053)
              ·
                refine ⟨25474619051392847389973645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67932317470380926373263053 25474619051392847389973645)
                ·
                  refine ⟨9552982144272317771240117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25474619051392847389973645 9552982144272317771240117)
                  ·
                    refine ⟨895592076025529791053761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9552982144272317771240117 895592076025529791053761)
                    ·
                      rfl

theorem cell22_2616239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2616239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616239 prefixEnd_2616239 := by exact prefixLift 2616239
  have htrace : WordTrace (prefixWord ++ tailWord_2616239) baseStart_2616239 baseEnd_2616239 := by
    simpa [prefixWord, tailWord_2616239, baseEnd_2616239] using wordTrace_append hprefix tailTrace_2616239
  have hstable : (prefixWord ++ tailWord_2616239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616239).length < 2 ^ (prefixWord ++ tailWord_2616239).sum := by decide
  have hdescent : baseEnd_2616239 < baseStart_2616239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616290 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2616290 : Nat := 118140960795 + 2616290 * 2 ^ 59
def prefixEnd_2616290 : Nat := 4983230072969 + 3 ^ 40 * 2616290 * 2
def baseEnd_2616290 : Nat := 895609534367782658028605

theorem tailTrace_2616290 : CollatzResearch.WordTrace tailWord_2616290 prefixEnd_2616290 895609534367782658028605 := by
  unfold tailWord_2616290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855983922908907900853581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63615957127757087735609549 23855983922908907900853581)
  ·
    refine ⟨8945993971090840462820093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23855983922908907900853581 8945993971090840462820093)
    ·
      refine ⟨3354747739159065173557535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8945993971090840462820093 3354747739159065173557535)
      ·
        refine ⟨5032121608738597760336303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354747739159065173557535 5032121608738597760336303)
        ·
          refine ⟨7548182413107896640504455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032121608738597760336303 7548182413107896640504455)
          ·
            refine ⟨11322273619661844960756683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548182413107896640504455 11322273619661844960756683)
            ·
              refine ⟨16983410429492767441135025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322273619661844960756683 16983410429492767441135025)
              ·
                refine ⟨12737557822119575580851269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16983410429492767441135025 12737557822119575580851269)
                ·
                  refine ⟨2388292091647420421409613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12737557822119575580851269 2388292091647420421409613)
                  ·
                    refine ⟨895609534367782658028605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388292091647420421409613 895609534367782658028605)
                    ·
                      rfl

theorem cell22_2616290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2616290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616290 prefixEnd_2616290 := by exact prefixLift 2616290
  have htrace : WordTrace (prefixWord ++ tailWord_2616290) baseStart_2616290 baseEnd_2616290 := by
    simpa [prefixWord, tailWord_2616290, baseEnd_2616290] using wordTrace_append hprefix tailTrace_2616290
  have hstable : (prefixWord ++ tailWord_2616290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616290).length < 2 ^ (prefixWord ++ tailWord_2616290).sum := by decide
  have hdescent : baseEnd_2616290 < baseStart_2616290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616299 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_2616299 : Nat := 118140960795 + 2616299 * 2 ^ 59
def prefixEnd_2616299 : Nat := 4983230072969 + 3 ^ 40 * 2616299 * 2
def baseEnd_2616299 : Nat := 895612615251709634553577

theorem tailTrace_2616299 : CollatzResearch.WordTrace tailWord_2616299 prefixEnd_2616299 895612615251709634553577 := by
  unfold tailWord_2616299
  simp only [CollatzResearch.WordTrace]
  refine ⟨95424263948603026140491951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63616175965735350760327967 95424263948603026140491951)
  ·
    refine ⟨143136395922904539210737927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95424263948603026140491951 143136395922904539210737927)
    ·
      refine ⟨214704593884356808816106891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143136395922904539210737927 214704593884356808816106891)
      ·
        refine ⟨322056890826535213224160337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214704593884356808816106891 322056890826535213224160337)
        ·
          refine ⟨241542668119901409918120253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322056890826535213224160337 241542668119901409918120253)
          ·
            refine ⟨90578500544963028719295095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241542668119901409918120253 90578500544963028719295095)
            ·
              refine ⟨135867750817444543078942643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90578500544963028719295095 135867750817444543078942643)
              ·
                refine ⟨203801626226166814618413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135867750817444543078942643 203801626226166814618413965)
                ·
                  refine ⟨76425609834812555481905237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203801626226166814618413965 76425609834812555481905237)
                  ·
                    refine ⟨895612615251709634553577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76425609834812555481905237 895612615251709634553577)
                    ·
                      rfl

theorem cell22_2616299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_2616299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616299 prefixEnd_2616299 := by exact prefixLift 2616299
  have htrace : WordTrace (prefixWord ++ tailWord_2616299) baseStart_2616299 baseEnd_2616299 := by
    simpa [prefixWord, tailWord_2616299, baseEnd_2616299] using wordTrace_append hprefix tailTrace_2616299
  have hstable : (prefixWord ++ tailWord_2616299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616299).length < 2 ^ (prefixWord ++ tailWord_2616299).sum := by decide
  have hdescent : baseEnd_2616299 < baseStart_2616299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616309 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 4]
def baseStart_2616309 : Nat := 118140960795 + 2616309 * 2 ^ 59
def prefixEnd_2616309 : Nat := 4983230072969 + 3 ^ 40 * 2616309 * 2
def baseEnd_2616309 : Nat := 298538679485357647267849

theorem tailTrace_2616309 : CollatzResearch.WordTrace tailWord_2616309 prefixEnd_2616309 298538679485357647267849 := by
  unfold tailWord_2616309
  simp only [CollatzResearch.WordTrace]
  refine ⟨95424628678566797848355981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63616419119044531898903987 95424628678566797848355981)
  ·
    refine ⟨35784235754462549193133493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95424628678566797848355981 35784235754462549193133493)
    ·
      refine ⟨3354772101980863986856265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35784235754462549193133493 3354772101980863986856265)
      ·
        refine ⟨2516079076485647990142199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354772101980863986856265 2516079076485647990142199)
        ·
          refine ⟨3774118614728471985213299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516079076485647990142199 3774118614728471985213299)
          ·
            refine ⟨5661177922092707977819949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774118614728471985213299 5661177922092707977819949)
            ·
              refine ⟨2122941720784765491682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661177922092707977819949 2122941720784765491682481)
              ·
                refine ⟨1592206290588574118761861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122941720784765491682481 1592206290588574118761861)
                ·
                  refine ⟨298538679485357647267849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592206290588574118761861 298538679485357647267849)
                  ·
                    rfl

theorem cell22_2616309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_2616309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616309 prefixEnd_2616309 := by exact prefixLift 2616309
  have htrace : WordTrace (prefixWord ++ tailWord_2616309) baseStart_2616309 baseEnd_2616309 := by
    simpa [prefixWord, tailWord_2616309, baseEnd_2616309] using wordTrace_append hprefix tailTrace_2616309
  have hstable : (prefixWord ++ tailWord_2616309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616309).length < 2 ^ (prefixWord ++ tailWord_2616309).sum := by decide
  have hdescent : baseEnd_2616309 < baseStart_2616309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616408 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_2616408 : Nat := 118140960795 + 2616408 * 2 ^ 59
def prefixEnd_2616408 : Nat := 4983230072969 + 3 ^ 40 * 2616408 * 2
def baseEnd_2616408 : Nat := 895649928179269683578243

theorem tailTrace_2616408 : CollatzResearch.WordTrace tailWord_2616408 prefixEnd_2616408 895649928179269683578243 := by
  unfold tailWord_2616408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47714119752604068878104939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63618826336805425170806585 47714119752604068878104939)
  ·
    refine ⟨71571179628906103317157409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47714119752604068878104939 71571179628906103317157409)
    ·
      refine ⟨53678384721679577487868057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71571179628906103317157409 53678384721679577487868057)
      ·
        refine ⟨40258788541259683115901043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53678384721679577487868057 40258788541259683115901043)
        ·
          refine ⟨60388182811889524673851565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40258788541259683115901043 60388182811889524673851565)
          ·
            refine ⟨22645568554458571752694337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60388182811889524673851565 22645568554458571752694337)
            ·
              refine ⟨16984176415843928814520753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22645568554458571752694337 16984176415843928814520753)
              ·
                refine ⟨12738132311882946610890565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16984176415843928814520753 12738132311882946610890565)
                ·
                  refine ⟨2388399808478052489541981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12738132311882946610890565 2388399808478052489541981)
                  ·
                    refine ⟨895649928179269683578243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388399808478052489541981 895649928179269683578243)
                    ·
                      rfl

theorem cell22_2616408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_2616408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616408 prefixEnd_2616408 := by exact prefixLift 2616408
  have htrace : WordTrace (prefixWord ++ tailWord_2616408) baseStart_2616408 baseEnd_2616408 := by
    simpa [prefixWord, tailWord_2616408, baseEnd_2616408] using wordTrace_append hprefix tailTrace_2616408
  have hstable : (prefixWord ++ tailWord_2616408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616408).length < 2 ^ (prefixWord ++ tailWord_2616408).sum := by decide
  have hdescent : baseEnd_2616408 < baseStart_2616408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616421 : List Nat := [1, 3, 1, 3, 2, 1, 11]
def baseStart_2616421 : Nat := 118140960795 + 2616421 * 2 ^ 59
def prefixEnd_2616421 : Nat := 4983230072969 + 3 ^ 40 * 2616421 * 2
def baseEnd_2616421 : Nat := 33172384383145999370489

theorem tailTrace_2616421 : CollatzResearch.WordTrace tailWord_2616421 prefixEnd_2616421 33172384383145999370489 := by
  unfold tailWord_2616421
  simp only [CollatzResearch.WordTrace]
  refine ⟨95428713654161040976433117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63619142436107360650955411 95428713654161040976433117)
  ·
    refine ⟨35785767620310390366162419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95428713654161040976433117 35785767620310390366162419)
    ·
      refine ⟨53678651430465585549243629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35785767620310390366162419 53678651430465585549243629)
      ·
        refine ⟨20129494286424594580966361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53678651430465585549243629 20129494286424594580966361)
        ·
          refine ⟨15097120714818445935724771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20129494286424594580966361 15097120714818445935724771)
          ·
            refine ⟨22645681072227668903587157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15097120714818445935724771 22645681072227668903587157)
            ·
              refine ⟨33172384383145999370489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22645681072227668903587157 33172384383145999370489)
              ·
                rfl

theorem cell22_2616421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 11].length) (baseStart_2616421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616421 prefixEnd_2616421 := by exact prefixLift 2616421
  have htrace : WordTrace (prefixWord ++ tailWord_2616421) baseStart_2616421 baseEnd_2616421 := by
    simpa [prefixWord, tailWord_2616421, baseEnd_2616421] using wordTrace_append hprefix tailTrace_2616421
  have hstable : (prefixWord ++ tailWord_2616421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616421).length < 2 ^ (prefixWord ++ tailWord_2616421).sum := by decide
  have hdescent : baseEnd_2616421 < baseStart_2616421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616425 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_2616425 : Nat := 118140960795 + 2616425 * 2 ^ 59
def prefixEnd_2616425 : Nat := 4983230072969 + 3 ^ 40 * 2616425 * 2
def baseEnd_2616425 : Nat := 895655747626687305903191

theorem tailTrace_2616425 : CollatzResearch.WordTrace tailWord_2616425 prefixEnd_2616425 895655747626687305903191 := by
  unfold tailWord_2616425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95428859546146549659578729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63619239697431033106385819 95428859546146549659578729)
  ·
    refine ⟨71571644659609912244684047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95428859546146549659578729 71571644659609912244684047)
    ·
      refine ⟨107357466989414868367026071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71571644659609912244684047 107357466989414868367026071)
      ·
        refine ⟨161036200484122302550539107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107357466989414868367026071 161036200484122302550539107)
        ·
          refine ⟨241554300726183453825808661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161036200484122302550539107 241554300726183453825808661)
          ·
            refine ⟨11322857846539849398084781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 241554300726183453825808661 11322857846539849398084781)
            ·
              refine ⟨4246071692452443524281793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11322857846539849398084781 4246071692452443524281793)
              ·
                refine ⟨3184553769339332643211345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246071692452443524281793 3184553769339332643211345)
                ·
                  refine ⟨2388415327004499482408509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184553769339332643211345 2388415327004499482408509)
                  ·
                    refine ⟨895655747626687305903191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388415327004499482408509 895655747626687305903191)
                    ·
                      rfl

theorem cell22_2616425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_2616425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616425 prefixEnd_2616425 := by exact prefixLift 2616425
  have htrace : WordTrace (prefixWord ++ tailWord_2616425) baseStart_2616425 baseEnd_2616425 := by
    simpa [prefixWord, tailWord_2616425, baseEnd_2616425] using wordTrace_append hprefix tailTrace_2616425
  have hstable : (prefixWord ++ tailWord_2616425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616425).length < 2 ^ (prefixWord ++ tailWord_2616425).sum := by decide
  have hdescent : baseEnd_2616425 < baseStart_2616425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616438 : List Nat := [5, 1, 1, 2, 1, 1, 2, 9]
def baseStart_2616438 : Nat := 118140960795 + 2616438 * 2 ^ 59
def prefixEnd_2616438 : Nat := 4983230072969 + 3 ^ 40 * 2616438 * 2
def baseEnd_2616438 : Nat := 99517799754706622814239

theorem tailTrace_2616438 : CollatzResearch.WordTrace tailWord_2616438 prefixEnd_2616438 99517799754706622814239 := by
  unfold tailWord_2616438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964333355943715804987623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63619555796732968586534645 5964333355943715804987623)
  ·
    refine ⟨8946500033915573707481435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964333355943715804987623 8946500033915573707481435)
    ·
      refine ⟨13419750050873360561222153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946500033915573707481435 13419750050873360561222153)
      ·
        refine ⟨10064812538155020420916615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13419750050873360561222153 10064812538155020420916615)
        ·
          refine ⟨15097218807232530631374923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064812538155020420916615 15097218807232530631374923)
          ·
            refine ⟨22645828210848795947062385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15097218807232530631374923 22645828210848795947062385)
            ·
              refine ⟨16984371158136596960296789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22645828210848795947062385 16984371158136596960296789)
              ·
                refine ⟨99517799754706622814239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16984371158136596960296789 99517799754706622814239)
                ·
                  rfl

theorem cell22_2616438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_2616438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616438 prefixEnd_2616438 := by exact prefixLift 2616438
  have htrace : WordTrace (prefixWord ++ tailWord_2616438) baseStart_2616438 baseEnd_2616438 := by
    simpa [prefixWord, tailWord_2616438, baseEnd_2616438] using wordTrace_append hprefix tailTrace_2616438
  have hstable : (prefixWord ++ tailWord_2616438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616438).length < 2 ^ (prefixWord ++ tailWord_2616438).sum := by decide
  have hdescent : baseEnd_2616438 < baseStart_2616438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616446 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2616446 : Nat := 118140960795 + 2616446 * 2 ^ 59
def prefixEnd_2616446 : Nat := 4983230072969 + 3 ^ 40 * 2616446 * 2
def baseEnd_2616446 : Nat := 895662936355850251128127

theorem tailTrace_2616446 : CollatzResearch.WordTrace tailWord_2616446 prefixEnd_2616446 895662936355850251128127 := by
  unfold tailWord_2616446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928703184883808780761649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63619750319380313497395461 11928703184883808780761649)
  ·
    refine ⟨8946527388662856585571237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11928703184883808780761649 8946527388662856585571237)
    ·
      refine ⟨1677473885374285609794607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8946527388662856585571237 1677473885374285609794607)
      ·
        refine ⟨2516210828061428414691911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677473885374285609794607 2516210828061428414691911)
        ·
          refine ⟨3774316242092142622037867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516210828061428414691911 3774316242092142622037867)
          ·
            refine ⟨5661474363138213933056801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774316242092142622037867 5661474363138213933056801)
            ·
              refine ⟨4246105772353660449792601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661474363138213933056801 4246105772353660449792601)
              ·
                refine ⟨3184579329265245337344451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246105772353660449792601 3184579329265245337344451)
                ·
                  refine ⟨4776868993897868006016677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184579329265245337344451 4776868993897868006016677)
                  ·
                    refine ⟨895662936355850251128127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776868993897868006016677 895662936355850251128127)
                    ·
                      rfl

theorem cell22_2616446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2616446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616446 prefixEnd_2616446 := by exact prefixLift 2616446
  have htrace : WordTrace (prefixWord ++ tailWord_2616446) baseStart_2616446 baseEnd_2616446 := by
    simpa [prefixWord, tailWord_2616446, baseEnd_2616446] using wordTrace_append hprefix tailTrace_2616446
  have hstable : (prefixWord ++ tailWord_2616446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616446).length < 2 ^ (prefixWord ++ tailWord_2616446).sum := by decide
  have hdescent : baseEnd_2616446 < baseStart_2616446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616487 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2616487 : Nat := 118140960795 + 2616487 * 2 ^ 59
def prefixEnd_2616487 : Nat := 4983230072969 + 3 ^ 40 * 2616487 * 2
def baseEnd_2616487 : Nat := 895676971493739810853001

theorem tailTrace_2616487 : CollatzResearch.WordTrace tailWord_2616487 prefixEnd_2616487 895676971493739810853001 := by
  unfold tailWord_2616487
  simp only [CollatzResearch.WordTrace]
  refine ⟨95431120871921934248335715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63620747247947956165557143 95431120871921934248335715)
  ·
    refine ⟨143146681307882901372503573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95431120871921934248335715 143146681307882901372503573)
    ·
      refine ⟨6710000686307011001836105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143146681307882901372503573 6710000686307011001836105)
      ·
        refine ⟨5032500514730258251377079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6710000686307011001836105 5032500514730258251377079)
        ·
          refine ⟨7548750772095387377065619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032500514730258251377079 7548750772095387377065619)
          ·
            refine ⟨11323126158143081065598429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548750772095387377065619 11323126158143081065598429)
            ·
              refine ⟨4246172309303655399599411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11323126158143081065598429 4246172309303655399599411)
              ·
                refine ⟨6369258463955483099399117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246172309303655399599411 6369258463955483099399117)
                ·
                  refine ⟨2388471923983306162274669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6369258463955483099399117 2388471923983306162274669)
                  ·
                    refine ⟨895676971493739810853001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388471923983306162274669 895676971493739810853001)
                    ·
                      rfl

theorem cell22_2616487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2616487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616487 prefixEnd_2616487 := by exact prefixLift 2616487
  have htrace : WordTrace (prefixWord ++ tailWord_2616487) baseStart_2616487 baseEnd_2616487 := by
    simpa [prefixWord, tailWord_2616487, baseEnd_2616487] using wordTrace_append hprefix tailTrace_2616487
  have hstable : (prefixWord ++ tailWord_2616487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616487).length < 2 ^ (prefixWord ++ tailWord_2616487).sum := by decide
  have hdescent : baseEnd_2616487 < baseStart_2616487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616534 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2616534 : Nat := 118140960795 + 2616534 * 2 ^ 59
def prefixEnd_2616534 : Nat := 4983230072969 + 3 ^ 40 * 2616534 * 2
def baseEnd_2616534 : Nat := 298564353518082451642619

theorem tailTrace_2616534 : CollatzResearch.WordTrace tailWord_2616534 prefixEnd_2616534 298564353518082451642619 := by
  unfold tailWord_2616534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964552193921978829706041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63621890068501107516864437 5964552193921978829706041)
  ·
    refine ⟨4473414145441484122279531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5964552193921978829706041 4473414145441484122279531)
    ·
      refine ⟨6710121218162226183419297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473414145441484122279531 6710121218162226183419297)
      ·
        refine ⟨5032590913621669637564473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6710121218162226183419297 5032590913621669637564473)
        ·
          refine ⟨3774443185216252228173355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032590913621669637564473 3774443185216252228173355)
          ·
            refine ⟨5661664777824378342260033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774443185216252228173355 5661664777824378342260033)
            ·
              refine ⟨4246248583368283756695025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661664777824378342260033 4246248583368283756695025)
              ·
                refine ⟨3184686437526212817521269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246248583368283756695025 3184686437526212817521269)
                ·
                  refine ⟨298564353518082451642619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3184686437526212817521269 298564353518082451642619)
                  ·
                    rfl

theorem cell22_2616534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2616534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616534 prefixEnd_2616534 := by exact prefixLift 2616534
  have htrace : WordTrace (prefixWord ++ tailWord_2616534) baseStart_2616534 baseEnd_2616534 := by
    simpa [prefixWord, tailWord_2616534, baseEnd_2616534] using wordTrace_append hprefix tailTrace_2616534
  have hstable : (prefixWord ++ tailWord_2616534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616534).length < 2 ^ (prefixWord ++ tailWord_2616534).sum := by decide
  have hdescent : baseEnd_2616534 < baseStart_2616534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616575 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_2616575 : Nat := 118140960795 + 2616575 * 2 ^ 59
def prefixEnd_2616575 : Nat := 4983230072969 + 3 ^ 40 * 2616575 * 2
def baseEnd_2616575 : Nat := 895707095692136914652731

theorem tailTrace_2616575 : CollatzResearch.WordTrace tailWord_2616575 prefixEnd_2616575 895707095692136914652731 := by
  unfold tailWord_2616575
  simp only [CollatzResearch.WordTrace]
  refine ⟨95434330495603125277539179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63622886997068750185026119 95434330495603125277539179)
  ·
    refine ⟨143151495743404687916308769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95434330495603125277539179 143151495743404687916308769)
    ·
      refine ⟨107363621807553515937231577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143151495743404687916308769 107363621807553515937231577)
      ·
        refine ⟨80522716355665136952923683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107363621807553515937231577 80522716355665136952923683)
        ·
          refine ⟨120784074533497705429385525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80522716355665136952923683 120784074533497705429385525)
          ·
            refine ⟨11323506987515409884004893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120784074533497705429385525 11323506987515409884004893)
            ·
              refine ⟨4246315120318278706501835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11323506987515409884004893 4246315120318278706501835)
              ·
                refine ⟨6369472680477418059752753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246315120318278706501835 6369472680477418059752753)
                ·
                  refine ⟨4777104510358063544814565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369472680477418059752753 4777104510358063544814565)
                  ·
                    refine ⟨895707095692136914652731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777104510358063544814565 895707095692136914652731)
                    ·
                      rfl

theorem cell22_2616575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_2616575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616575 prefixEnd_2616575 := by exact prefixLift 2616575
  have htrace : WordTrace (prefixWord ++ tailWord_2616575) baseStart_2616575 baseEnd_2616575 := by
    simpa [prefixWord, tailWord_2616575, baseEnd_2616575] using wordTrace_append hprefix tailTrace_2616575
  have hstable : (prefixWord ++ tailWord_2616575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616575).length < 2 ^ (prefixWord ++ tailWord_2616575).sum := by decide
  have hdescent : baseEnd_2616575 < baseStart_2616575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616639 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 1, 3]
def baseStart_2616639 : Nat := 118140960795 + 2616639 * 2 ^ 59
def prefixEnd_2616639 : Nat := 4983230072969 + 3 ^ 40 * 2616639 * 2
def baseEnd_2616639 : Nat := 895729004200062081052535

theorem tailTrace_2616639 : CollatzResearch.WordTrace tailWord_2616639 prefixEnd_2616639 895729004200062081052535 := by
  unfold tailWord_2616639
  simp only [CollatzResearch.WordTrace]
  refine ⟨95436664767371264207868971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63624443178247509471912647 95436664767371264207868971)
  ·
    refine ⟨143154997151056896311803457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95436664767371264207868971 143154997151056896311803457)
    ·
      refine ⟨107366247863292672233852593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143154997151056896311803457 107366247863292672233852593)
      ·
        refine ⟨80524685897469504175389445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107366247863292672233852593 80524685897469504175389445)
        ·
          refine ⟨15098378605775532032885521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80524685897469504175389445 15098378605775532032885521)
          ·
            refine ⟨11323783954331649024664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15098378605775532032885521 11323783954331649024664141)
            ·
              refine ⟨4246418982874368384249053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11323783954331649024664141 4246418982874368384249053)
              ·
                refine ⟨1592407118577888144093395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4246418982874368384249053 1592407118577888144093395)
                ·
                  refine ⟨2388610677866832216140093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592407118577888144093395 2388610677866832216140093)
                  ·
                    refine ⟨895729004200062081052535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388610677866832216140093 895729004200062081052535)
                    ·
                      rfl

theorem cell22_2616639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_2616639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616639 prefixEnd_2616639 := by exact prefixLift 2616639
  have htrace : WordTrace (prefixWord ++ tailWord_2616639) baseStart_2616639 baseEnd_2616639 := by
    simpa [prefixWord, tailWord_2616639, baseEnd_2616639] using wordTrace_append hprefix tailTrace_2616639
  have hstable : (prefixWord ++ tailWord_2616639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616639).length < 2 ^ (prefixWord ++ tailWord_2616639).sum := by decide
  have hdescent : baseEnd_2616639 < baseStart_2616639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616662 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2616662 : Nat := 118140960795 + 2616662 * 2 ^ 59
def prefixEnd_2616662 : Nat := 4983230072969 + 3 ^ 40 * 2616662 * 2
def baseEnd_2616662 : Nat := 895736877570097687727465

theorem tailTrace_2616662 : CollatzResearch.WordTrace tailWord_2616662 prefixEnd_2616662 895736877570097687727465 := by
  unfold tailWord_2616662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964843977892996195997265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63625002430858626090637493 5964843977892996195997265)
  ·
    refine ⟨4473632983419747146997949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5964843977892996195997265 4473632983419747146997949)
    ·
      refine ⟨1677612368782405180124231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4473632983419747146997949 1677612368782405180124231)
      ·
        refine ⟨2516418553173607770186347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677612368782405180124231 2516418553173607770186347)
        ·
          refine ⟨3774627829760411655279521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516418553173607770186347 3774627829760411655279521)
          ·
            refine ⟨2830970872320308741459641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774627829760411655279521 2830970872320308741459641)
            ·
              refine ⟨2123228154240231556094731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830970872320308741459641 2123228154240231556094731)
              ·
                refine ⟨3184842231360347334142097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123228154240231556094731 3184842231360347334142097)
                ·
                  refine ⟨2388631673520260500606573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184842231360347334142097 2388631673520260500606573)
                  ·
                    refine ⟨895736877570097687727465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388631673520260500606573 895736877570097687727465)
                    ·
                      rfl

theorem cell22_2616662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2616662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616662 prefixEnd_2616662 := by exact prefixLift 2616662
  have htrace : WordTrace (prefixWord ++ tailWord_2616662) baseStart_2616662 baseEnd_2616662 := by
    simpa [prefixWord, tailWord_2616662, baseEnd_2616662] using wordTrace_append hprefix tailTrace_2616662
  have hstable : (prefixWord ++ tailWord_2616662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616662).length < 2 ^ (prefixWord ++ tailWord_2616662).sum := by decide
  have hdescent : baseEnd_2616662 < baseStart_2616662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616695 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2616695 : Nat := 118140960795 + 2616695 * 2 ^ 59
def prefixEnd_2616695 : Nat := 4983230072969 + 3 ^ 40 * 2616695 * 2
def baseEnd_2616695 : Nat := 895748174144496601652363

theorem tailTrace_2616695 : CollatzResearch.WordTrace tailWord_2616695 prefixEnd_2616695 895748174144496601652363 := by
  unfold tailWord_2616695
  simp only [CollatzResearch.WordTrace]
  refine ⟨95438707255168385771907539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63625804836778923847938359 95438707255168385771907539)
  ·
    refine ⟨143158060882752578657861309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95438707255168385771907539 143158060882752578657861309)
    ·
      refine ⟨53684272831032216996697991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143158060882752578657861309 53684272831032216996697991)
      ·
        refine ⟨80526409246548325495046987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53684272831032216996697991 80526409246548325495046987)
        ·
          refine ⟨120789613869822488242570481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80526409246548325495046987 120789613869822488242570481)
          ·
            refine ⟨90592210402366866181927861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120789613869822488242570481 90592210402366866181927861)
            ·
              refine ⟨8493019725221893704555737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90592210402366866181927861 8493019725221893704555737)
              ·
                refine ⟨6369764793916420278416803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493019725221893704555737 6369764793916420278416803)
                ·
                  refine ⟨9554647190874630417625205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369764793916420278416803 9554647190874630417625205)
                  ·
                    refine ⟨895748174144496601652363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9554647190874630417625205 895748174144496601652363)
                    ·
                      rfl

theorem cell22_2616695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2616695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616695 prefixEnd_2616695 := by exact prefixLift 2616695
  have htrace : WordTrace (prefixWord ++ tailWord_2616695) baseStart_2616695 baseEnd_2616695 := by
    simpa [prefixWord, tailWord_2616695, baseEnd_2616695] using wordTrace_append hprefix tailTrace_2616695
  have hstable : (prefixWord ++ tailWord_2616695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616695).length < 2 ^ (prefixWord ++ tailWord_2616695).sum := by decide
  have hdescent : baseEnd_2616695 < baseStart_2616695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616725 : List Nat := [1, 3, 2, 1, 1, 2, 5, 7]
def baseStart_2616725 : Nat := 118140960795 + 2616725 * 2 ^ 59
def prefixEnd_2616725 : Nat := 4983230072969 + 3 ^ 40 * 2616725 * 2
def baseEnd_2616725 : Nat := 99528715973065169266919

theorem tailTrace_2616725 : CollatzResearch.WordTrace tailWord_2616725 prefixEnd_2616725 99528715973065169266919 := by
  unfold tailWord_2616725
  simp only [CollatzResearch.WordTrace]
  refine ⟨95439801445059700895499629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63626534296706467263666419 95439801445059700895499629)
  ·
    refine ⟨35789925541897387835812361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95439801445059700895499629 35789925541897387835812361)
    ·
      refine ⟨26842444156423040876859271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35789925541897387835812361 26842444156423040876859271)
      ·
        refine ⟨40263666234634561315288907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26842444156423040876859271 40263666234634561315288907)
        ·
          refine ⟨60395499351951841972933361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40263666234634561315288907 60395499351951841972933361)
          ·
            refine ⟨45296624513963881479700021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60395499351951841972933361 45296624513963881479700021)
            ·
              refine ⟨4246558548184113888721877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45296624513963881479700021 4246558548184113888721877)
              ·
                refine ⟨99528715973065169266919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4246558548184113888721877 99528715973065169266919)
                ·
                  rfl

theorem cell22_2616725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 7].length) (baseStart_2616725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616725 prefixEnd_2616725 := by exact prefixLift 2616725
  have htrace : WordTrace (prefixWord ++ tailWord_2616725) baseStart_2616725 baseEnd_2616725 := by
    simpa [prefixWord, tailWord_2616725, baseEnd_2616725] using wordTrace_append hprefix tailTrace_2616725
  have hstable : (prefixWord ++ tailWord_2616725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616725).length < 2 ^ (prefixWord ++ tailWord_2616725).sum := by decide
  have hdescent : baseEnd_2616725 < baseStart_2616725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616744 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2616744 : Nat := 118140960795 + 2616744 * 2 ^ 59
def prefixEnd_2616744 : Nat := 4983230072969 + 3 ^ 40 * 2616744 * 2
def baseEnd_2616744 : Nat := 895764947845876807177213

theorem tailTrace_2616744 : CollatzResearch.WordTrace tailWord_2616744 prefixEnd_2616744 895764947845876807177213 := by
  unfold tailWord_2616744
  simp only [CollatzResearch.WordTrace]
  refine ⟨47720247215995433570220643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63626996287993911426960857 47720247215995433570220643)
  ·
    refine ⟨71580370823993150355330965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47720247215995433570220643 71580370823993150355330965)
    ·
      refine ⟨3355329882374678922906139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71580370823993150355330965 3355329882374678922906139)
      ·
        refine ⟨5032994823562018384359209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355329882374678922906139 5032994823562018384359209)
        ·
          refine ⟨3774746117671513788269407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032994823562018384359209 3774746117671513788269407)
          ·
            refine ⟨5662119176507270682404111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774746117671513788269407 5662119176507270682404111)
            ·
              refine ⟨8493178764760906023606167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662119176507270682404111 8493178764760906023606167)
              ·
                refine ⟨12739768147141359035409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8493178764760906023606167 12739768147141359035409251)
                ·
                  refine ⟨19109652220712038553113877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12739768147141359035409251 19109652220712038553113877)
                  ·
                    refine ⟨895764947845876807177213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19109652220712038553113877 895764947845876807177213)
                    ·
                      rfl

theorem cell22_2616744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2616744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616744 prefixEnd_2616744 := by exact prefixLift 2616744
  have htrace : WordTrace (prefixWord ++ tailWord_2616744) baseStart_2616744 baseEnd_2616744 := by
    simpa [prefixWord, tailWord_2616744, baseEnd_2616744] using wordTrace_append hprefix tailTrace_2616744
  have hstable : (prefixWord ++ tailWord_2616744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616744).length < 2 ^ (prefixWord ++ tailWord_2616744).sum := by decide
  have hdescent : baseEnd_2616744 < baseStart_2616744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616815 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 8]
def baseStart_2616815 : Nat := 118140960795 + 2616815 * 2 ^ 59
def prefixEnd_2616815 : Nat := 4983230072969 + 3 ^ 40 * 2616815 * 2
def baseEnd_2616815 : Nat := 298596417532285429550665

theorem tailTrace_2616815 : CollatzResearch.WordTrace tailWord_2616815 prefixEnd_2616815 298596417532285429550665 := by
  unfold tailWord_2616815
  simp only [CollatzResearch.WordTrace]
  refine ⟨95443084014733646266275899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63628722676489097510850599 95443084014733646266275899)
  ·
    refine ⟨143164626022100469399413849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95443084014733646266275899 143164626022100469399413849)
    ·
      refine ⟨107373469516575352049560387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143164626022100469399413849 107373469516575352049560387)
      ·
        refine ⟨161060204274863028074340581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107373469516575352049560387 161060204274863028074340581)
        ·
          refine ⟨30198788301536817763938859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161060204274863028074340581 30198788301536817763938859)
          ·
            refine ⟨45298182452305226645908289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30198788301536817763938859 45298182452305226645908289)
            ·
              refine ⟨33973636839228919984431217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45298182452305226645908289 33973636839228919984431217)
              ·
                refine ⟨25480227629421689988323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33973636839228919984431217 25480227629421689988323413)
                ·
                  refine ⟨298596417532285429550665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25480227629421689988323413 298596417532285429550665)
                  ·
                    rfl

theorem cell22_2616815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_2616815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616815 prefixEnd_2616815 := by exact prefixLift 2616815
  have htrace : WordTrace (prefixWord ++ tailWord_2616815) baseStart_2616815 baseEnd_2616815 := by
    simpa [prefixWord, tailWord_2616815, baseEnd_2616815] using wordTrace_append hprefix tailTrace_2616815
  have hstable : (prefixWord ++ tailWord_2616815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616815).length < 2 ^ (prefixWord ++ tailWord_2616815).sum := by decide
  have hdescent : baseEnd_2616815 < baseStart_2616815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616864 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_2616864 : Nat := 118140960795 + 2616864 * 2 ^ 59
def prefixEnd_2616864 : Nat := 4983230072969 + 3 ^ 40 * 2616864 * 2
def baseEnd_2616864 : Nat := 895806026298236494176845

theorem tailTrace_2616864 : CollatzResearch.WordTrace tailWord_2616864 prefixEnd_2616864 895806026298236494176845 := by
  unfold tailWord_2616864
  simp only [CollatzResearch.WordTrace]
  refine ⟨47722435595778063817404823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63629914127704085089873097 47722435595778063817404823)
  ·
    refine ⟨71583653393667095726107235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47722435595778063817404823 71583653393667095726107235)
    ·
      refine ⟨107375480090500643589160853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71583653393667095726107235 107375480090500643589160853)
      ·
        refine ⟨5033225629242217668241915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107375480090500643589160853 5033225629242217668241915)
        ·
          refine ⟨7549838443863326502362873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033225629242217668241915 7549838443863326502362873)
          ·
            refine ⟨5662378832897494876772155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549838443863326502362873 5662378832897494876772155)
            ·
              refine ⟨8493568249346242315158233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662378832897494876772155 8493568249346242315158233)
              ·
                refine ⟨6370176187009681736368675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493568249346242315158233 6370176187009681736368675)
                ·
                  refine ⟨9555264280514522604553013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370176187009681736368675 9555264280514522604553013)
                  ·
                    refine ⟨895806026298236494176845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9555264280514522604553013 895806026298236494176845)
                    ·
                      rfl

theorem cell22_2616864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_2616864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616864 prefixEnd_2616864 := by exact prefixLift 2616864
  have htrace : WordTrace (prefixWord ++ tailWord_2616864) baseStart_2616864 baseEnd_2616864 := by
    simpa [prefixWord, tailWord_2616864, baseEnd_2616864] using wordTrace_append hprefix tailTrace_2616864
  have hstable : (prefixWord ++ tailWord_2616864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616864).length < 2 ^ (prefixWord ++ tailWord_2616864).sum := by decide
  have hdescent : baseEnd_2616864 < baseStart_2616864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616937 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_2616937 : Nat := 118140960795 + 2616937 * 2 ^ 59
def prefixEnd_2616937 : Nat := 4983230072969 + 3 ^ 40 * 2616937 * 2
def baseEnd_2616937 : Nat := 895831015690088637101621

theorem tailTrace_2616937 : CollatzResearch.WordTrace tailWord_2616937 prefixEnd_2616937 895831015690088637101621 := by
  unfold tailWord_2616937
  simp only [CollatzResearch.WordTrace]
  refine ⟨95447533720291661102217065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63631689146861107401478043 95447533720291661102217065)
  ·
    refine ⟨71585650290218745826662799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95447533720291661102217065 71585650290218745826662799)
    ·
      refine ⟨107378475435328118739994199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71585650290218745826662799 107378475435328118739994199)
      ·
        refine ⟨161067713152992178109991299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107378475435328118739994199 161067713152992178109991299)
        ·
          refine ⟨241601569729488267164986949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161067713152992178109991299 241601569729488267164986949)
          ·
            refine ⟨45300294324279050093435053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241601569729488267164986949 45300294324279050093435053)
            ·
              refine ⟨16987610371604643785038145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45300294324279050093435053 16987610371604643785038145)
              ·
                refine ⟨12740707778703482838778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16987610371604643785038145 12740707778703482838778609)
                ·
                  refine ⟨9555530834027612129083957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12740707778703482838778609 9555530834027612129083957)
                  ·
                    refine ⟨895831015690088637101621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9555530834027612129083957 895831015690088637101621)
                    ·
                      rfl

theorem cell22_2616937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_2616937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616937 prefixEnd_2616937 := by exact prefixLift 2616937
  have htrace : WordTrace (prefixWord ++ tailWord_2616937) baseStart_2616937 baseEnd_2616937 := by
    simpa [prefixWord, tailWord_2616937, baseEnd_2616937] using wordTrace_append hprefix tailTrace_2616937
  have hstable : (prefixWord ++ tailWord_2616937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616937).length < 2 ^ (prefixWord ++ tailWord_2616937).sum := by decide
  have hdescent : baseEnd_2616937 < baseStart_2616937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616969 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_2616969 : Nat := 118140960795 + 2616969 * 2 ^ 59
def prefixEnd_2616969 : Nat := 4983230072969 + 3 ^ 40 * 2616969 * 2
def baseEnd_2616969 : Nat := 895841969944051220301523

theorem tailTrace_2616969 : CollatzResearch.WordTrace tailWord_2616969 prefixEnd_2616969 895841969944051220301523 := by
  unfold tailWord_2616969
  simp only [CollatzResearch.WordTrace]
  refine ⟨95448700856175730567381961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63632467237450487044921307 95448700856175730567381961)
  ·
    refine ⟨71586525642131797925536471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95448700856175730567381961 71586525642131797925536471)
    ·
      refine ⟨107379788463197696888304707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71586525642131797925536471 107379788463197696888304707)
      ·
        refine ⟨161069682694796545332457061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107379788463197696888304707 161069682694796545332457061)
        ·
          refine ⟨30200565505274352249835699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161069682694796545332457061 30200565505274352249835699)
          ·
            refine ⟨45300848257911528374753549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30200565505274352249835699 45300848257911528374753549)
            ·
              refine ⟨16987818096716823140532581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45300848257911528374753549 16987818096716823140532581)
              ·
                refine ⟨3185215893134404338849859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16987818096716823140532581 3185215893134404338849859)
                ·
                  refine ⟨4777823839701606508274789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185215893134404338849859 4777823839701606508274789)
                  ·
                    refine ⟨895841969944051220301523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777823839701606508274789 895841969944051220301523)
                    ·
                      rfl

theorem cell22_2616969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_2616969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2616969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2616969 prefixEnd_2616969 := by exact prefixLift 2616969
  have htrace : WordTrace (prefixWord ++ tailWord_2616969) baseStart_2616969 baseEnd_2616969 := by
    simpa [prefixWord, tailWord_2616969, baseEnd_2616969] using wordTrace_append hprefix tailTrace_2616969
  have hstable : (prefixWord ++ tailWord_2616969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616969).length < 2 ^ (prefixWord ++ tailWord_2616969).sum := by decide
  have hdescent : baseEnd_2616969 < baseStart_2616969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617046 : List Nat := [5, 2, 1, 3, 11]
def baseStart_2617046 : Nat := 118140960795 + 2617046 * 2 ^ 59
def prefixEnd_2617046 : Nat := 4983230072969 + 3 ^ 40 * 2617046 * 2
def baseEnd_2617046 : Nat := 3686700940813369078709

theorem tailTrace_2617046 : CollatzResearch.WordTrace tailWord_2617046 prefixEnd_2617046 3686700940813369078709 := by
  unfold tailWord_2617046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965719329806048294870937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63634339517931181811956661 5965719329806048294870937)
  ·
    refine ⟨4474289497354536221153203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5965719329806048294870937 4474289497354536221153203)
    ·
      refine ⟨6711434246031804331729805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474289497354536221153203 6711434246031804331729805)
      ·
        refine ⟨2516787842261926624398677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6711434246031804331729805 2516787842261926624398677)
        ·
          refine ⟨3686700940813369078709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2516787842261926624398677 3686700940813369078709)
          ·
            rfl

theorem cell22_2617046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 11].length) (baseStart_2617046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617046 prefixEnd_2617046 := by exact prefixLift 2617046
  have htrace : WordTrace (prefixWord ++ tailWord_2617046) baseStart_2617046 baseEnd_2617046 := by
    simpa [prefixWord, tailWord_2617046, baseEnd_2617046] using wordTrace_append hprefix tailTrace_2617046
  have hstable : (prefixWord ++ tailWord_2617046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617046).length < 2 ^ (prefixWord ++ tailWord_2617046).sum := by decide
  have hdescent : baseEnd_2617046 < baseStart_2617046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617052 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_2617052 : Nat := 118140960795 + 2617052 * 2 ^ 59
def prefixEnd_2617052 : Nat := 4983230072969 + 3 ^ 40 * 2617052 * 2
def baseEnd_2617052 : Nat := 298623460846755556825423

theorem tailTrace_2617052 : CollatzResearch.WordTrace tailWord_2617052 prefixEnd_2617052 298623460846755556825423 := by
  unfold tailWord_2617052
  simp only [CollatzResearch.WordTrace]
  refine ⟨47725864057437517871326705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63634485409916690495102273 47725864057437517871326705)
  ·
    refine ⟨35794398043078138403495029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47725864057437517871326705 35794398043078138403495029)
    ·
      refine ⟨3355724816538575475327659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35794398043078138403495029 3355724816538575475327659)
      ·
        refine ⟨5033587224807863212991489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355724816538575475327659 5033587224807863212991489)
        ·
          refine ⟨3775190418605897409743617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5033587224807863212991489 3775190418605897409743617)
          ·
            refine ⟨2831392813954423057307713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775190418605897409743617 2831392813954423057307713)
            ·
              refine ⟨2123544610465817292980785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831392813954423057307713 2123544610465817292980785)
              ·
                refine ⟨1592658457849362969735589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123544610465817292980785 1592658457849362969735589)
                ·
                  refine ⟨298623460846755556825423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592658457849362969735589 298623460846755556825423)
                  ·
                    rfl

theorem cell22_2617052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_2617052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617052 prefixEnd_2617052 := by exact prefixLift 2617052
  have htrace : WordTrace (prefixWord ++ tailWord_2617052) baseStart_2617052 baseEnd_2617052 := by
    simpa [prefixWord, tailWord_2617052, baseEnd_2617052] using wordTrace_append hprefix tailTrace_2617052
  have hstable : (prefixWord ++ tailWord_2617052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617052).length < 2 ^ (prefixWord ++ tailWord_2617052).sum := by decide
  have hdescent : baseEnd_2617052 < baseStart_2617052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617061 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_2617061 : Nat := 118140960795 + 2617061 * 2 ^ 59
def prefixEnd_2617061 : Nat := 4983230072969 + 3 ^ 40 * 2617061 * 2
def baseEnd_2617061 : Nat := 895873463424193647001241

theorem tailTrace_2617061 : CollatzResearch.WordTrace tailWord_2617061 prefixEnd_2617061 895873463424193647001241 := by
  unfold tailWord_2617061
  simp only [CollatzResearch.WordTrace]
  refine ⟨95452056371842430279731037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63634704247894953519820691 95452056371842430279731037)
  ·
    refine ⟨35794521139440911354899139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95452056371842430279731037 35794521139440911354899139)
    ·
      refine ⟨53691781709161367032348709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35794521139440911354899139 53691781709161367032348709)
      ·
        refine ⟨10067209070467756318565383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53691781709161367032348709 10067209070467756318565383)
        ·
          refine ⟨15100813605701634477848075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10067209070467756318565383 15100813605701634477848075)
          ·
            refine ⟨22651220408552451716772113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15100813605701634477848075 22651220408552451716772113)
            ·
              refine ⟨16988415306414338787579085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22651220408552451716772113 16988415306414338787579085)
              ·
                refine ⟨6370655739905377045342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16988415306414338787579085 6370655739905377045342157)
                ·
                  refine ⟨2388995902464516392003309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6370655739905377045342157 2388995902464516392003309)
                  ·
                    refine ⟨895873463424193647001241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2388995902464516392003309 895873463424193647001241)
                    ·
                      rfl

theorem cell22_2617061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_2617061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617061 prefixEnd_2617061 := by exact prefixLift 2617061
  have htrace : WordTrace (prefixWord ++ tailWord_2617061) baseStart_2617061 baseEnd_2617061 := by
    simpa [prefixWord, tailWord_2617061, baseEnd_2617061] using wordTrace_append hprefix tailTrace_2617061
  have hstable : (prefixWord ++ tailWord_2617061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617061).length < 2 ^ (prefixWord ++ tailWord_2617061).sum := by decide
  have hdescent : baseEnd_2617061 < baseStart_2617061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617063 : List Nat := [1, 1, 5, 4, 1, 2, 1, 7]
def baseStart_2617063 : Nat := 118140960795 + 2617063 * 2 ^ 59
def prefixEnd_2617063 : Nat := 4983230072969 + 3 ^ 40 * 2617063 * 2
def baseEnd_2617063 : Nat := 99541572007229589827915

theorem tailTrace_2617063 : CollatzResearch.WordTrace tailWord_2617063 prefixEnd_2617063 99541572007229589827915 := by
  unfold tailWord_2617063
  simp only [CollatzResearch.WordTrace]
  refine ⟨95452129317835184621303843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63634752878556789747535895 95452129317835184621303843)
  ·
    refine ⟨143178193976752776931955765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95452129317835184621303843 143178193976752776931955765)
    ·
      refine ⟨13422955685320572837370853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143178193976752776931955765 13422955685320572837370853)
      ·
        refine ⟨2516804190997607407007035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13422955685320572837370853 2516804190997607407007035)
        ·
          refine ⟨3775206286496411110510553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516804190997607407007035 3775206286496411110510553)
          ·
            refine ⟨2831404714872308332882915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775206286496411110510553 2831404714872308332882915)
            ·
              refine ⟨4247107072308462499324373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831404714872308332882915 4247107072308462499324373)
              ·
                refine ⟨99541572007229589827915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4247107072308462499324373 99541572007229589827915)
                ·
                  rfl

theorem cell22_2617063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 7].length) (baseStart_2617063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617063 prefixEnd_2617063 := by exact prefixLift 2617063
  have htrace : WordTrace (prefixWord ++ tailWord_2617063) baseStart_2617063 baseEnd_2617063 := by
    simpa [prefixWord, tailWord_2617063, baseEnd_2617063] using wordTrace_append hprefix tailTrace_2617063
  have hstable : (prefixWord ++ tailWord_2617063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617063).length < 2 ^ (prefixWord ++ tailWord_2617063).sum := by decide
  have hdescent : baseEnd_2617063 < baseStart_2617063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617078 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2617078 : Nat := 118140960795 + 2617078 * 2 ^ 59
def prefixEnd_2617078 : Nat := 4983230072969 + 3 ^ 40 * 2617078 * 2
def baseEnd_2617078 : Nat := 895879282871611269326189

theorem tailTrace_2617078 : CollatzResearch.WordTrace tailWord_2617078 prefixEnd_2617078 895879282871611269326189 := by
  unfold tailWord_2617078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965792275798802636443743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63635117608520561455399925 5965792275798802636443743)
  ·
    refine ⟨8948688413698203954665615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5965792275798802636443743 8948688413698203954665615)
    ·
      refine ⟨13423032620547305931998423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8948688413698203954665615 13423032620547305931998423)
      ·
        refine ⟨20134548930820958897997635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423032620547305931998423 20134548930820958897997635)
        ·
          refine ⟨30201823396231438346996453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20134548930820958897997635 30201823396231438346996453)
          ·
            refine ⟨5662841886793394690061835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30201823396231438346996453 5662841886793394690061835)
            ·
              refine ⟨8494262830190092035092753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662841886793394690061835 8494262830190092035092753)
              ·
                refine ⟨6370697122642569026319565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8494262830190092035092753 6370697122642569026319565)
                ·
                  refine ⟨2389011420990963384869837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6370697122642569026319565 2389011420990963384869837)
                  ·
                    refine ⟨895879282871611269326189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389011420990963384869837 895879282871611269326189)
                    ·
                      rfl

theorem cell22_2617078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2617078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617078 prefixEnd_2617078 := by exact prefixLift 2617078
  have htrace : WordTrace (prefixWord ++ tailWord_2617078) baseStart_2617078 baseEnd_2617078 := by
    simpa [prefixWord, tailWord_2617078, baseEnd_2617078] using wordTrace_append hprefix tailTrace_2617078
  have hstable : (prefixWord ++ tailWord_2617078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617078).length < 2 ^ (prefixWord ++ tailWord_2617078).sum := by decide
  have hdescent : baseEnd_2617078 < baseStart_2617078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617101 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2617101 : Nat := 118140960795 + 2617101 * 2 ^ 59
def prefixEnd_2617101 : Nat := 4983230072969 + 3 ^ 40 * 2617101 * 2
def baseEnd_2617101 : Nat := 895887156241646876001119

theorem tailTrace_2617101 : CollatzResearch.WordTrace tailWord_2617101 prefixEnd_2617101 895887156241646876001119 := by
  unfold tailWord_2617101
  simp only [CollatzResearch.WordTrace]
  refine ⟨95453515291697517111187157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63635676861131678074124771 95453515291697517111187157)
  ·
    refine ⟨2237191764649160557293449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 95453515291697517111187157 2237191764649160557293449)
    ·
      refine ⟨1677893823486870417970087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237191764649160557293449 1677893823486870417970087)
      ·
        refine ⟨2516840735230305626955131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677893823486870417970087 2516840735230305626955131)
        ·
          refine ⟨3775261102845458440432697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516840735230305626955131 3775261102845458440432697)
          ·
            refine ⟨2831445827134093830324523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775261102845458440432697 2831445827134093830324523)
            ·
              refine ⟨4247168740701140745486785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831445827134093830324523 4247168740701140745486785)
              ·
                refine ⟨3185376555525855559115089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247168740701140745486785 3185376555525855559115089)
                ·
                  refine ⟨2389032416644391669336317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185376555525855559115089 2389032416644391669336317)
                  ·
                    refine ⟨895887156241646876001119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389032416644391669336317 895887156241646876001119)
                    ·
                      rfl

theorem cell22_2617101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2617101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617101 prefixEnd_2617101 := by exact prefixLift 2617101
  have htrace : WordTrace (prefixWord ++ tailWord_2617101) baseStart_2617101 baseEnd_2617101 := by
    simpa [prefixWord, tailWord_2617101, baseEnd_2617101] using wordTrace_append hprefix tailTrace_2617101
  have hstable : (prefixWord ++ tailWord_2617101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617101).length < 2 ^ (prefixWord ++ tailWord_2617101).sum := by decide
  have hdescent : baseEnd_2617101 < baseStart_2617101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617138 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2617138 : Nat := 118140960795 + 2617138 * 2 ^ 59
def prefixEnd_2617138 : Nat := 4983230072969 + 3 ^ 40 * 2617138 * 2
def baseEnd_2617138 : Nat := 895899822097791112826005

theorem tailTrace_2617138 : CollatzResearch.WordTrace tailWord_2617138 prefixEnd_2617138 895899822097791112826005 := by
  unfold tailWord_2617138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23863716198140868107571017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63636576528375648286856045 23863716198140868107571017)
  ·
    refine ⟨17897787148605651080678263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23863716198140868107571017 17897787148605651080678263)
    ·
      refine ⟨26846680722908476621017395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897787148605651080678263 26846680722908476621017395)
      ·
        refine ⟨40270021084362714931526093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846680722908476621017395 40270021084362714931526093)
        ·
          refine ⟨15101257906636018099322285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40270021084362714931526093 15101257906636018099322285)
          ·
            refine ⟨5662971714988506787245857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15101257906636018099322285 5662971714988506787245857)
            ·
              refine ⟨4247228786241380090434393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662971714988506787245857 4247228786241380090434393)
              ·
                refine ⟨3185421589681035067825795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247228786241380090434393 3185421589681035067825795)
                ·
                  refine ⟨4778132384521552601738693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185421589681035067825795 4778132384521552601738693)
                  ·
                    refine ⟨895899822097791112826005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778132384521552601738693 895899822097791112826005)
                    ·
                      rfl

theorem cell22_2617138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2617138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617138 prefixEnd_2617138 := by exact prefixLift 2617138
  have htrace : WordTrace (prefixWord ++ tailWord_2617138) baseStart_2617138 baseEnd_2617138 := by
    simpa [prefixWord, tailWord_2617138, baseEnd_2617138] using wordTrace_append hprefix tailTrace_2617138
  have hstable : (prefixWord ++ tailWord_2617138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617138).length < 2 ^ (prefixWord ++ tailWord_2617138).sum := by decide
  have hdescent : baseEnd_2617138 < baseStart_2617138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617170 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2617170 : Nat := 118140960795 + 2617170 * 2 ^ 59
def prefixEnd_2617170 : Nat := 4983230072969 + 3 ^ 40 * 2617170 * 2
def baseEnd_2617170 : Nat := 298636925450584565341969

theorem tailTrace_2617170 : CollatzResearch.WordTrace tailWord_2617170 prefixEnd_2617170 298636925450584565341969 := by
  unfold tailWord_2617170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23864007982111885473862241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63637354618965027930299309 23864007982111885473862241)
  ·
    refine ⟨17898005986583914105396681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23864007982111885473862241 17898005986583914105396681)
    ·
      refine ⟨13423504489937935579047511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17898005986583914105396681 13423504489937935579047511)
      ·
        refine ⟨20135256734906903368571267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423504489937935579047511 20135256734906903368571267)
        ·
          refine ⟨30202885102360355052856901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20135256734906903368571267 30202885102360355052856901)
          ·
            refine ⟨5663040956692566572410669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30202885102360355052856901 5663040956692566572410669)
            ·
              refine ⟨2123640358759712464654001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5663040956692566572410669 2123640358759712464654001)
              ·
                refine ⟨1592730269069784348490501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123640358759712464654001 1592730269069784348490501)
                ·
                  refine ⟨298636925450584565341969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592730269069784348490501 298636925450584565341969)
                  ·
                    rfl

theorem cell22_2617170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2617170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617170 prefixEnd_2617170 := by exact prefixLift 2617170
  have htrace : WordTrace (prefixWord ++ tailWord_2617170) baseStart_2617170 baseEnd_2617170 := by
    simpa [prefixWord, tailWord_2617170, baseEnd_2617170] using wordTrace_append hprefix tailTrace_2617170
  have hstable : (prefixWord ++ tailWord_2617170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617170).length < 2 ^ (prefixWord ++ tailWord_2617170).sum := by decide
  have hdescent : baseEnd_2617170 < baseStart_2617170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617273 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_2617273 : Nat := 118140960795 + 2617273 * 2 ^ 59
def prefixEnd_2617273 : Nat := 4983230072969 + 3 ^ 40 * 2617273 * 2
def baseEnd_2617273 : Nat := 895946035356695760700591

theorem tailTrace_2617273 : CollatzResearch.WordTrace tailWord_2617273 prefixEnd_2617273 895946035356695760700591 := by
  unfold tailWord_2617273
  simp only [CollatzResearch.WordTrace]
  refine ⟨95459788647074390486448473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63639859098049593657632315 95459788647074390486448473)
  ·
    refine ⟨71594841485305792864836355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95459788647074390486448473 71594841485305792864836355)
    ·
      refine ⟨107392262227958689297254533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71594841485305792864836355 107392262227958689297254533)
      ·
        refine ⟨20136049167742254243235225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107392262227958689297254533 20136049167742254243235225)
        ·
          refine ⟨15102036875806690682426419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20136049167742254243235225 15102036875806690682426419)
          ·
            refine ⟨22653055313710036023639629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15102036875806690682426419 22653055313710036023639629)
            ·
              refine ⟨8494895742641263508864861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22653055313710036023639629 8494895742641263508864861)
              ·
                refine ⟨3185585903490473815824323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8494895742641263508864861 3185585903490473815824323)
                ·
                  refine ⟨4778378855235710723736485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185585903490473815824323 4778378855235710723736485)
                  ·
                    refine ⟨895946035356695760700591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778378855235710723736485 895946035356695760700591)
                    ·
                      rfl

theorem cell22_2617273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_2617273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617273 prefixEnd_2617273 := by exact prefixLift 2617273
  have htrace : WordTrace (prefixWord ++ tailWord_2617273) baseStart_2617273 baseEnd_2617273 := by
    simpa [prefixWord, tailWord_2617273, baseEnd_2617273] using wordTrace_append hprefix tailTrace_2617273
  have hstable : (prefixWord ++ tailWord_2617273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617273).length < 2 ^ (prefixWord ++ tailWord_2617273).sum := by decide
  have hdescent : baseEnd_2617273 < baseStart_2617273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617288 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_2617288 : Nat := 118140960795 + 2617288 * 2 ^ 59
def prefixEnd_2617288 : Nat := 4983230072969 + 3 ^ 40 * 2617288 * 2
def baseEnd_2617288 : Nat := 298650390054413573858515

theorem tailTrace_2617288 : CollatzResearch.WordTrace tailWord_2617288 prefixEnd_2617288 298650390054413573858515 := by
  unfold tailWord_2617288
  simp only [CollatzResearch.WordTrace]
  refine ⟨47730167871010024024122259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63640223828013365365496345 47730167871010024024122259)
  ·
    refine ⟨71595251806515036036183389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47730167871010024024122259 71595251806515036036183389)
    ·
      refine ⟨26848219427443138513568771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71595251806515036036183389 26848219427443138513568771)
      ·
        refine ⟨40272329141164707770353157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26848219427443138513568771 40272329141164707770353157)
        ·
          refine ⟨7551061713968382706941217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40272329141164707770353157 7551061713968382706941217)
          ·
            refine ⟨5663296285476287030205913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7551061713968382706941217 5663296285476287030205913)
            ·
              refine ⟨4247472214107215272654435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663296285476287030205913 4247472214107215272654435)
              ·
                refine ⟨6371208321160822908981653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247472214107215272654435 6371208321160822908981653)
                ·
                  refine ⟨298650390054413573858515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6371208321160822908981653 298650390054413573858515)
                  ·
                    rfl

theorem cell22_2617288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_2617288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617288 prefixEnd_2617288 := by exact prefixLift 2617288
  have htrace : WordTrace (prefixWord ++ tailWord_2617288) baseStart_2617288 baseEnd_2617288 := by
    simpa [prefixWord, tailWord_2617288, baseEnd_2617288] using wordTrace_append hprefix tailTrace_2617288
  have hstable : (prefixWord ++ tailWord_2617288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617288).length < 2 ^ (prefixWord ++ tailWord_2617288).sum := by decide
  have hdescent : baseEnd_2617288 < baseStart_2617288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617316 : List Nat := [2, 3, 1, 1, 1, 1, 5, 8]
def baseStart_2617316 : Nat := 118140960795 + 2617316 * 2 ^ 59
def prefixEnd_2617316 : Nat := 4983230072969 + 3 ^ 40 * 2617316 * 2
def baseEnd_2617316 : Nat := 99551195015050886875051

theorem tailTrace_2617316 : CollatzResearch.WordTrace tailWord_2617316 prefixEnd_2617316 99551195015050886875051 := by
  unfold tailWord_2617316
  simp only [CollatzResearch.WordTrace]
  refine ⟨47730678492959304415131901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63640904657279072553509201 47730678492959304415131901)
  ·
    refine ⟨17899004434859739155674463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47730678492959304415131901 17899004434859739155674463)
    ·
      refine ⟨26848506652289608733511695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17899004434859739155674463 26848506652289608733511695)
      ·
        refine ⟨40272759978434413100267543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26848506652289608733511695 40272759978434413100267543)
        ·
          refine ⟨60409139967651619650401315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40272759978434413100267543 60409139967651619650401315)
          ·
            refine ⟨90613709951477429475601973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60409139967651619650401315 90613709951477429475601973)
            ·
              refine ⟨8495035307951009013337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90613709951477429475601973 8495035307951009013337685)
              ·
                refine ⟨99551195015050886875051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8495035307951009013337685 99551195015050886875051)
                ·
                  rfl

theorem cell22_2617316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_2617316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617316 prefixEnd_2617316 := by exact prefixLift 2617316
  have htrace : WordTrace (prefixWord ++ tailWord_2617316) baseStart_2617316 baseEnd_2617316 := by
    simpa [prefixWord, tailWord_2617316, baseEnd_2617316] using wordTrace_append hprefix tailTrace_2617316
  have hstable : (prefixWord ++ tailWord_2617316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617316).length < 2 ^ (prefixWord ++ tailWord_2617316).sum := by decide
  have hdescent : baseEnd_2617316 < baseStart_2617316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617354 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2617354 : Nat := 118140960795 + 2617354 * 2 ^ 59
def prefixEnd_2617354 : Nat := 4983230072969 + 3 ^ 40 * 2617354 * 2
def baseEnd_2617354 : Nat := 895973763312038549425343

theorem tailTrace_2617354 : CollatzResearch.WordTrace tailWord_2617354 prefixEnd_2617354 895973763312038549425343 := by
  unfold tailWord_2617354
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865685739945235330036779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63641828639853960880098077 23865685739945235330036779)
  ·
    refine ⟨35798528609917852995055169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23865685739945235330036779 35798528609917852995055169)
    ·
      refine ⟨26848896457438389746291377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35798528609917852995055169 26848896457438389746291377)
      ·
        refine ⟨20136672343078792309718533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26848896457438389746291377 20136672343078792309718533)
        ·
          refine ⟨3775626064327273558072225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20136672343078792309718533 3775626064327273558072225)
          ·
            refine ⟨2831719548245455168554169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775626064327273558072225 2831719548245455168554169)
            ·
              refine ⟨2123789661184091376415627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831719548245455168554169 2123789661184091376415627)
              ·
                refine ⟨3185684491776137064623441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123789661184091376415627 3185684491776137064623441)
                ·
                  refine ⟨2389263368832102798467581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185684491776137064623441 2389263368832102798467581)
                  ·
                    refine ⟨895973763312038549425343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389263368832102798467581 895973763312038549425343)
                    ·
                      rfl

theorem cell22_2617354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2617354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617354 prefixEnd_2617354 := by exact prefixLift 2617354
  have htrace : WordTrace (prefixWord ++ tailWord_2617354) baseStart_2617354 baseEnd_2617354 := by
    simpa [prefixWord, tailWord_2617354, baseEnd_2617354] using wordTrace_append hprefix tailTrace_2617354
  have hstable : (prefixWord ++ tailWord_2617354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617354).length < 2 ^ (prefixWord ++ tailWord_2617354).sum := by decide
  have hdescent : baseEnd_2617354 < baseStart_2617354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617408 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_2617408 : Nat := 118140960795 + 2617408 * 2 ^ 59
def prefixEnd_2617408 : Nat := 4983230072969 + 3 ^ 40 * 2617408 * 2
def baseEnd_2617408 : Nat := 895992248615600408575177

theorem tailTrace_2617408 : CollatzResearch.WordTrace tailWord_2617408 prefixEnd_2617408 895992248615600408575177 := by
  unfold tailWord_2617408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47732356250792654271306439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63643141667723539028408585 47732356250792654271306439)
  ·
    refine ⟨71598534376188981406959659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47732356250792654271306439 71598534376188981406959659)
    ·
      refine ⟨107397801564283472110439489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71598534376188981406959659 107397801564283472110439489)
      ·
        refine ⟨80548351173212604082829617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107397801564283472110439489 80548351173212604082829617)
        ·
          refine ⟨60411263379909453062122213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80548351173212604082829617 60411263379909453062122213)
          ·
            refine ⟨11327111883733022449147915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60411263379909453062122213 11327111883733022449147915)
            ·
              refine ⟨16990667825599533673721873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11327111883733022449147915 16990667825599533673721873)
              ·
                refine ⟨12743000869199650255291405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16990667825599533673721873 12743000869199650255291405)
                ·
                  refine ⟨4778625325949868845734277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12743000869199650255291405 4778625325949868845734277)
                  ·
                    refine ⟨895992248615600408575177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778625325949868845734277 895992248615600408575177)
                    ·
                      rfl

theorem cell22_2617408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_2617408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617408 prefixEnd_2617408 := by exact prefixLift 2617408
  have htrace : WordTrace (prefixWord ++ tailWord_2617408) baseStart_2617408 baseEnd_2617408 := by
    simpa [prefixWord, tailWord_2617408, baseEnd_2617408] using wordTrace_append hprefix tailTrace_2617408
  have hstable : (prefixWord ++ tailWord_2617408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617408).length < 2 ^ (prefixWord ++ tailWord_2617408).sum := by decide
  have hdescent : baseEnd_2617408 < baseStart_2617408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617440 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_2617440 : Nat := 118140960795 + 2617440 * 2 ^ 59
def prefixEnd_2617440 : Nat := 4983230072969 + 3 ^ 40 * 2617440 * 2
def baseEnd_2617440 : Nat := 298667734289854330591693

theorem tailTrace_2617440 : CollatzResearch.WordTrace tailWord_2617440 prefixEnd_2617440 298667734289854330591693 := by
  unfold tailWord_2617440
  simp only [CollatzResearch.WordTrace]
  refine ⟨47732939818734689003888887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63643919758312918671851849 47732939818734689003888887)
  ·
    refine ⟨71599409728102033505833331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47732939818734689003888887 71599409728102033505833331)
    ·
      refine ⟨107399114592153050258749997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71599409728102033505833331 107399114592153050258749997)
      ·
        refine ⟨40274667972057393847031249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107399114592153050258749997 40274667972057393847031249)
        ·
          refine ⟨30206000979043045385273437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40274667972057393847031249 30206000979043045385273437)
          ·
            refine ⟨11327250367141142019477539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30206000979043045385273437 11327250367141142019477539)
            ·
              refine ⟨16990875550711713029216309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11327250367141142019477539 16990875550711713029216309)
              ·
                refine ⟨1592894582879223096489029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16990875550711713029216309 1592894582879223096489029)
                ·
                  refine ⟨298667734289854330591693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592894582879223096489029 298667734289854330591693)
                  ·
                    rfl

theorem cell22_2617440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_2617440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617440 prefixEnd_2617440 := by exact prefixLift 2617440
  have htrace : WordTrace (prefixWord ++ tailWord_2617440) baseStart_2617440 baseEnd_2617440 := by
    simpa [prefixWord, tailWord_2617440, baseEnd_2617440] using wordTrace_append hprefix tailTrace_2617440
  have hstable : (prefixWord ++ tailWord_2617440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617440).length < 2 ^ (prefixWord ++ tailWord_2617440).sum := by decide
  have hdescent : baseEnd_2617440 < baseStart_2617440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617455 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 4, 3]
def baseStart_2617455 : Nat := 118140960795 + 2617455 * 2 ^ 59
def prefixEnd_2617455 : Nat := 4983230072969 + 3 ^ 40 * 2617455 * 2
def baseEnd_2617455 : Nat := 896008337676107952650033

theorem tailTrace_2617455 : CollatzResearch.WordTrace tailWord_2617455 prefixEnd_2617455 896008337676107952650033 := by
  unfold tailWord_2617455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95466426732415035569573819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63644284488276690379715879 95466426732415035569573819)
  ·
    refine ⟨143199640098622553354360729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95466426732415035569573819 143199640098622553354360729)
    ·
      refine ⟨107399730073966915015770547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143199640098622553354360729 107399730073966915015770547)
      ·
        refine ⟨161099595110950372523655821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107399730073966915015770547 161099595110950372523655821)
        ·
          refine ⟨60412348166606389696370933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161099595110950372523655821 60412348166606389696370933)
          ·
            refine ⟨5663657640619349034034775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60412348166606389696370933 5663657640619349034034775)
            ·
              refine ⟨8495486460929023551052163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663657640619349034034775 8495486460929023551052163)
              ·
                refine ⟨12743229691393535326578245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495486460929023551052163 12743229691393535326578245)
                ·
                  refine ⟨2389355567136287873733421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12743229691393535326578245 2389355567136287873733421)
                  ·
                    refine ⟨896008337676107952650033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389355567136287873733421 896008337676107952650033)
                    ·
                      rfl

theorem cell22_2617455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_2617455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617455 prefixEnd_2617455 := by exact prefixLift 2617455
  have htrace : WordTrace (prefixWord ++ tailWord_2617455) baseStart_2617455 baseEnd_2617455 := by
    simpa [prefixWord, tailWord_2617455, baseEnd_2617455] using wordTrace_append hprefix tailTrace_2617455
  have hstable : (prefixWord ++ tailWord_2617455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617455).length < 2 ^ (prefixWord ++ tailWord_2617455).sum := by decide
  have hdescent : baseEnd_2617455 < baseStart_2617455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617502 : List Nat := [4, 3, 1, 1, 3, 2, 8]
def baseStart_2617502 : Nat := 118140960795 + 2617502 * 2 ^ 59
def prefixEnd_2617502 : Nat := 4983230072969 + 3 ^ 40 * 2617502 * 2
def baseEnd_2617502 : Nat := 33186089879133907286107

theorem tailTrace_2617502 : CollatzResearch.WordTrace tailWord_2617502 prefixEnd_2617502 33186089879133907286107 := by
  unfold tailWord_2617502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933517620405595324566845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63645427308829841731023173 11933517620405595324566845)
  ·
    refine ⟨4475069107652098246712567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11933517620405595324566845 4475069107652098246712567)
    ·
      refine ⟨6712603661478147370068851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475069107652098246712567 6712603661478147370068851)
      ·
        refine ⟨10068905492217221055103277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712603661478147370068851 10068905492217221055103277)
        ·
          refine ⟨3775839559581457895663729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10068905492217221055103277 3775839559581457895663729)
          ·
            refine ⟨2831879669686093421747797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3775839559581457895663729 2831879669686093421747797)
            ·
              refine ⟨33186089879133907286107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2831879669686093421747797 33186089879133907286107)
              ·
                rfl

theorem cell22_2617502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 8].length) (baseStart_2617502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617502 prefixEnd_2617502 := by exact prefixLift 2617502
  have htrace : WordTrace (prefixWord ++ tailWord_2617502) baseStart_2617502 baseEnd_2617502 := by
    simpa [prefixWord, tailWord_2617502, baseEnd_2617502] using wordTrace_append hprefix tailTrace_2617502
  have hstable : (prefixWord ++ tailWord_2617502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617502).length < 2 ^ (prefixWord ++ tailWord_2617502).sum := by decide
  have hdescent : baseEnd_2617502 < baseStart_2617502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617528 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_2617528 : Nat := 118140960795 + 2617528 * 2 ^ 59
def prefixEnd_2617528 : Nat := 4983230072969 + 3 ^ 40 * 2617528 * 2
def baseEnd_2617528 : Nat := 896033327067960095574809

theorem tailTrace_2617528 : CollatzResearch.WordTrace tailWord_2617528 prefixEnd_2617528 896033327067960095574809 := by
  unfold tailWord_2617528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47734544630575284518490619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63646059507433712691320825 47734544630575284518490619)
  ·
    refine ⟨71601816945862926777735929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47734544630575284518490619 71601816945862926777735929)
    ·
      refine ⟨53701362709397195083301947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71601816945862926777735929 53701362709397195083301947)
      ·
        refine ⟨80552044064095792624952921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53701362709397195083301947 80552044064095792624952921)
        ·
          refine ⟨60414033048071844468714691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80552044064095792624952921 60414033048071844468714691)
          ·
            refine ⟨90621049572107766703072037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60414033048071844468714691 90621049572107766703072037)
            ·
              refine ⟨16991446794770206256826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90621049572107766703072037 16991446794770206256826007)
              ·
                refine ⟨25487170192155309385239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16991446794770206256826007 25487170192155309385239011)
                ·
                  refine ⟨38230755288232964077858517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25487170192155309385239011 38230755288232964077858517)
                  ·
                    refine ⟨896033327067960095574809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38230755288232964077858517 896033327067960095574809)
                    ·
                      rfl

theorem cell22_2617528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_2617528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617528 prefixEnd_2617528 := by exact prefixLift 2617528
  have htrace : WordTrace (prefixWord ++ tailWord_2617528) baseStart_2617528 baseEnd_2617528 := by
    simpa [prefixWord, tailWord_2617528, baseEnd_2617528] using wordTrace_append hprefix tailTrace_2617528
  have hstable : (prefixWord ++ tailWord_2617528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617528).length < 2 ^ (prefixWord ++ tailWord_2617528).sum := by decide
  have hdescent : baseEnd_2617528 < baseStart_2617528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617605 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2617605 : Nat := 118140960795 + 2617605 * 2 ^ 59
def prefixEnd_2617605 : Nat := 4983230072969 + 3 ^ 40 * 2617605 * 2
def baseEnd_2617605 : Nat := 896059685741557561399573

theorem tailTrace_2617605 : CollatzResearch.WordTrace tailWord_2617605 prefixEnd_2617605 896059685741557561399573 := by
  unfold tailWord_2617605
  simp only [CollatzResearch.WordTrace]
  refine ⟨95471897681871611187534269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63647931787914407458356179 95471897681871611187534269)
  ·
    refine ⟨35801961630701854195325351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95471897681871611187534269 35801961630701854195325351)
    ·
      refine ⟨53702942446052781292988027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35801961630701854195325351 53702942446052781292988027)
      ·
        refine ⟨80554413669079171939482041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53702942446052781292988027 80554413669079171939482041)
        ·
          refine ⟨60415810251809378954611531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80554413669079171939482041 60415810251809378954611531)
          ·
            refine ⟨90623715377714068431917297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60415810251809378954611531 90623715377714068431917297)
            ·
              refine ⟨67967786533285551323937973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90623715377714068431917297 67967786533285551323937973)
              ·
                refine ⟨6371979987495520436619185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67967786533285551323937973 6371979987495520436619185)
                ·
                  refine ⟨4778984990621640327464389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371979987495520436619185 4778984990621640327464389)
                  ·
                    refine ⟨896059685741557561399573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778984990621640327464389 896059685741557561399573)
                    ·
                      rfl

theorem cell22_2617605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2617605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617605 prefixEnd_2617605 := by exact prefixLift 2617605
  have htrace : WordTrace (prefixWord ++ tailWord_2617605) baseStart_2617605 baseEnd_2617605 := by
    simpa [prefixWord, tailWord_2617605, baseEnd_2617605] using wordTrace_append hprefix tailTrace_2617605
  have hstable : (prefixWord ++ tailWord_2617605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617605).length < 2 ^ (prefixWord ++ tailWord_2617605).sum := by decide
  have hdescent : baseEnd_2617605 < baseStart_2617605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617712 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_2617712 : Nat := 118140960795 + 2617712 * 2 ^ 59
def prefixEnd_2617712 : Nat := 4983230072969 + 3 ^ 40 * 2617712 * 2
def baseEnd_2617712 : Nat := 896096314028244948974245

theorem tailTrace_2617712 : CollatzResearch.WordTrace tailWord_2617712 prefixEnd_2617712 896096314028244948974245 := by
  unfold tailWord_2617712
  simp only [CollatzResearch.WordTrace]
  refine ⟨47737900146241984230839695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63650533528322645641119593 47737900146241984230839695)
  ·
    refine ⟨71606850219362976346259543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47737900146241984230839695 71606850219362976346259543)
    ·
      refine ⟨107410275329044464519389315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71606850219362976346259543 107410275329044464519389315)
      ·
        refine ⟨161115412993566696779083973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107410275329044464519389315 161115412993566696779083973)
        ·
          refine ⟨30209139936293755646078245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161115412993566696779083973 30209139936293755646078245)
          ·
            refine ⟨5664213738055079183639671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30209139936293755646078245 5664213738055079183639671)
            ·
              refine ⟨8496320607082618775459507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664213738055079183639671 8496320607082618775459507)
              ·
                refine ⟨12744480910623928163189261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496320607082618775459507 12744480910623928163189261)
                ·
                  refine ⟨4779180341483973061195973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744480910623928163189261 4779180341483973061195973)
                  ·
                    refine ⟨896096314028244948974245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779180341483973061195973 896096314028244948974245)
                    ·
                      rfl

theorem cell22_2617712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_2617712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617712 prefixEnd_2617712 := by exact prefixLift 2617712
  have htrace : WordTrace (prefixWord ++ tailWord_2617712) baseStart_2617712 baseEnd_2617712 := by
    simpa [prefixWord, tailWord_2617712, baseEnd_2617712] using wordTrace_append hprefix tailTrace_2617712
  have hstable : (prefixWord ++ tailWord_2617712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617712).length < 2 ^ (prefixWord ++ tailWord_2617712).sum := by decide
  have hdescent : baseEnd_2617712 < baseStart_2617712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617759 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 2, 3]
def baseStart_2617759 : Nat := 118140960795 + 2617759 * 2 ^ 59
def prefixEnd_2617759 : Nat := 4983230072969 + 3 ^ 40 * 2617759 * 2
def baseEnd_2617759 : Nat := 896112403088752493049101

theorem tailTrace_2617759 : CollatzResearch.WordTrace tailWord_2617759 prefixEnd_2617759 896112403088752493049101 := by
  unfold tailWord_2617759
  simp only [CollatzResearch.WordTrace]
  refine ⟨95477514523313695488640331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63651676348875796992426887 95477514523313695488640331)
  ·
    refine ⟨143216271784970543232960497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95477514523313695488640331 143216271784970543232960497)
    ·
      refine ⟨107412203838727907424720373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143216271784970543232960497 107412203838727907424720373)
      ·
        refine ⟨10069894109880741321067535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107412203838727907424720373 10069894109880741321067535)
        ·
          refine ⟨15104841164821111981601303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069894109880741321067535 15104841164821111981601303)
          ·
            refine ⟨22657261747231667972401955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15104841164821111981601303 22657261747231667972401955)
            ·
              refine ⟨33985892620847501958602933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22657261747231667972401955 33985892620847501958602933)
              ·
                refine ⟨3186177433204453308619025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33985892620847501958602933 3186177433204453308619025)
                ·
                  refine ⟨2389633074903339981464269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186177433204453308619025 2389633074903339981464269)
                  ·
                    refine ⟨896112403088752493049101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389633074903339981464269 896112403088752493049101)
                    ·
                      rfl

theorem cell22_2617759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_2617759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617759 prefixEnd_2617759 := by exact prefixLift 2617759
  have htrace : WordTrace (prefixWord ++ tailWord_2617759) baseStart_2617759 baseEnd_2617759 := by
    simpa [prefixWord, tailWord_2617759, baseEnd_2617759] using wordTrace_append hprefix tailTrace_2617759
  have hstable : (prefixWord ++ tailWord_2617759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617759).length < 2 ^ (prefixWord ++ tailWord_2617759).sum := by decide
  have hdescent : baseEnd_2617759 < baseStart_2617759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617810 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2617810 : Nat := 118140960795 + 2617810 * 2 ^ 59
def prefixEnd_2617810 : Nat := 4983230072969 + 3 ^ 40 * 2617810 * 2
def baseEnd_2617810 : Nat := 896129861431005360023945

theorem tailTrace_2617810 : CollatzResearch.WordTrace tailWord_2617810 prefixEnd_2617810 896129861431005360023945 := by
  unfold tailWord_2617810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23869843661532232799686721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63652916430752620799164589 23869843661532232799686721)
  ·
    refine ⟨17902382746149174599765041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23869843661532232799686721 17902382746149174599765041)
    ·
      refine ⟨13426787059611880949823781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17902382746149174599765041 13426787059611880949823781)
      ·
        refine ⟨2517522573677227678091959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13426787059611880949823781 2517522573677227678091959)
        ·
          refine ⟨3776283860515841517137939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517522573677227678091959 3776283860515841517137939)
          ·
            refine ⟨5664425790773762275706909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776283860515841517137939 5664425790773762275706909)
            ·
              refine ⟨2124159671540160853390091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664425790773762275706909 2124159671540160853390091)
              ·
                refine ⟨3186239507310241280085137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124159671540160853390091 3186239507310241280085137)
                ·
                  refine ⟨2389679630482680960063853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186239507310241280085137 2389679630482680960063853)
                  ·
                    refine ⟨896129861431005360023945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389679630482680960063853 896129861431005360023945)
                    ·
                      rfl

theorem cell22_2617810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2617810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617810 prefixEnd_2617810 := by exact prefixLift 2617810
  have htrace : WordTrace (prefixWord ++ tailWord_2617810) baseStart_2617810 baseEnd_2617810 := by
    simpa [prefixWord, tailWord_2617810, baseEnd_2617810] using wordTrace_append hprefix tailTrace_2617810
  have hstable : (prefixWord ++ tailWord_2617810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617810).length < 2 ^ (prefixWord ++ tailWord_2617810).sum := by decide
  have hdescent : baseEnd_2617810 < baseStart_2617810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617838 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2617838 : Nat := 118140960795 + 2617838 * 2 ^ 59
def prefixEnd_2617838 : Nat := 4983230072969 + 3 ^ 40 * 2617838 * 2
def baseEnd_2617838 : Nat := 896139446403222620323859

theorem tailTrace_2617838 : CollatzResearch.WordTrace tailWord_2617838 prefixEnd_2617838 896139446403222620323859 := by
  unfold tailWord_2617838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935049486253436497595771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63653597260018327987177445 11935049486253436497595771)
  ·
    refine ⟨17902574229380154746393657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11935049486253436497595771 17902574229380154746393657)
    ·
      refine ⟨13426930672035116059795243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17902574229380154746393657 13426930672035116059795243)
      ·
        refine ⟨20140396008052674089692865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13426930672035116059795243 20140396008052674089692865)
        ·
          refine ⟨15105297006039505567269649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20140396008052674089692865 15105297006039505567269649)
          ·
            refine ⟨11328972754529629175452237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15105297006039505567269649 11328972754529629175452237)
            ·
              refine ⟨4248364782948610940794589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11328972754529629175452237 4248364782948610940794589)
              ·
                refine ⟨1593136793605729102797971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4248364782948610940794589 1593136793605729102797971)
                ·
                  refine ⟨2389705190408593654196957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593136793605729102797971 2389705190408593654196957)
                  ·
                    refine ⟨896139446403222620323859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389705190408593654196957 896139446403222620323859)
                    ·
                      rfl

theorem cell22_2617838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2617838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617838 prefixEnd_2617838 := by exact prefixLift 2617838
  have htrace : WordTrace (prefixWord ++ tailWord_2617838) baseStart_2617838 baseEnd_2617838 := by
    simpa [prefixWord, tailWord_2617838, baseEnd_2617838] using wordTrace_append hprefix tailTrace_2617838
  have hstable : (prefixWord ++ tailWord_2617838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617838).length < 2 ^ (prefixWord ++ tailWord_2617838).sum := by decide
  have hdescent : baseEnd_2617838 < baseStart_2617838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617898 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2617898 : Nat := 118140960795 + 2617898 * 2 ^ 59
def prefixEnd_2617898 : Nat := 4983230072969 + 3 ^ 40 * 2617898 * 2
def baseEnd_2617898 : Nat := 896159985629402463823675

theorem tailTrace_2617898 : CollatzResearch.WordTrace tailWord_2617898 prefixEnd_2617898 896159985629402463823675 := by
  unfold tailWord_2617898
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870646067452530556987587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63655056179873414818633565 23870646067452530556987587)
  ·
    refine ⟨35805969101178795835481381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870646067452530556987587 35805969101178795835481381)
    ·
      refine ⟨6713619206471024219152759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35805969101178795835481381 6713619206471024219152759)
      ·
        refine ⟨10070428809706536328729139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713619206471024219152759 10070428809706536328729139)
        ·
          refine ⟨15105643214559804493093709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070428809706536328729139 15105643214559804493093709)
          ·
            refine ⟨5664616205459926684910141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15105643214559804493093709 5664616205459926684910141)
            ·
              refine ⟨2124231077047472506841303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664616205459926684910141 2124231077047472506841303)
              ·
                refine ⟨3186346615571208760261955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124231077047472506841303 3186346615571208760261955)
                ·
                  refine ⟨4779519923356813140392933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186346615571208760261955 4779519923356813140392933)
                  ·
                    refine ⟨896159985629402463823675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779519923356813140392933 896159985629402463823675)
                    ·
                      rfl

theorem cell22_2617898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2617898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617898 prefixEnd_2617898 := by exact prefixLift 2617898
  have htrace : WordTrace (prefixWord ++ tailWord_2617898) baseStart_2617898 baseEnd_2617898 := by
    simpa [prefixWord, tailWord_2617898, baseEnd_2617898] using wordTrace_append hprefix tailTrace_2617898
  have hstable : (prefixWord ++ tailWord_2617898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617898).length < 2 ^ (prefixWord ++ tailWord_2617898).sum := by decide
  have hdescent : baseEnd_2617898 < baseStart_2617898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617909 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2617909 : Nat := 118140960795 + 2617909 * 2 ^ 59
def prefixEnd_2617909 : Nat := 4983230072969 + 3 ^ 40 * 2617909 * 2
def baseEnd_2617909 : Nat := 896163751154202101798641

theorem tailTrace_2617909 : CollatzResearch.WordTrace tailWord_2617909 prefixEnd_2617909 896163751154202101798641 := by
  unfold tailWord_2617909
  simp only [CollatzResearch.WordTrace]
  refine ⟨95482985472770271106600781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63655323648513514071067187 95482985472770271106600781)
  ·
    refine ⟨35806119552288851664975293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95482985472770271106600781 35806119552288851664975293)
    ·
      refine ⟨13427294832108319374365735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35806119552288851664975293 13427294832108319374365735)
      ·
        refine ⟨20140942248162479061548603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427294832108319374365735 20140942248162479061548603)
        ·
          refine ⟨30211413372243718592322905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20140942248162479061548603 30211413372243718592322905)
          ·
            refine ⟨22658560029182788944242179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30211413372243718592322905 22658560029182788944242179)
            ·
              refine ⟨33987840043774183416363269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22658560029182788944242179 33987840043774183416363269)
              ·
                refine ⟨6372720008207659390568113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33987840043774183416363269 6372720008207659390568113)
                ·
                  refine ⟨4779540006155744542926085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372720008207659390568113 4779540006155744542926085)
                  ·
                    refine ⟨896163751154202101798641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779540006155744542926085 896163751154202101798641)
                    ·
                      rfl

theorem cell22_2617909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2617909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617909 prefixEnd_2617909 := by exact prefixLift 2617909
  have htrace : WordTrace (prefixWord ++ tailWord_2617909) baseStart_2617909 baseEnd_2617909 := by
    simpa [prefixWord, tailWord_2617909, baseEnd_2617909] using wordTrace_append hprefix tailTrace_2617909
  have hstable : (prefixWord ++ tailWord_2617909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617909).length < 2 ^ (prefixWord ++ tailWord_2617909).sum := by decide
  have hdescent : baseEnd_2617909 < baseStart_2617909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617911 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 2, 3]
def baseStart_2617911 : Nat := 118140960795 + 2617911 * 2 ^ 59
def prefixEnd_2617911 : Nat := 4983230072969 + 3 ^ 40 * 2617911 * 2
def baseEnd_2617911 : Nat := 896164435795074763248635

theorem tailTrace_2617911 : CollatzResearch.WordTrace tailWord_2617911 prefixEnd_2617911 896164435795074763248635 := by
  unfold tailWord_2617911
  simp only [CollatzResearch.WordTrace]
  refine ⟨95483058418763025448173587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63655372279175350298782391 95483058418763025448173587)
  ·
    refine ⟨143224587628144538172260381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95483058418763025448173587 143224587628144538172260381)
    ·
      refine ⟨53709220360554201814597643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143224587628144538172260381 53709220360554201814597643)
      ·
        refine ⟨80563830540831302721896465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53709220360554201814597643 80563830540831302721896465)
        ·
          refine ⟨60422872905623477041422349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80563830540831302721896465 60422872905623477041422349)
          ·
            refine ⟨22658577339608803890533381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60422872905623477041422349 22658577339608803890533381)
            ·
              refine ⟨4248483251176650729475009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22658577339608803890533381 4248483251176650729475009)
              ·
                refine ⟨3186362438382488047106257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248483251176650729475009 3186362438382488047106257)
                ·
                  refine ⟨2389771828786866035329693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186362438382488047106257 2389771828786866035329693)
                  ·
                    refine ⟨896164435795074763248635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389771828786866035329693 896164435795074763248635)
                    ·
                      rfl

theorem cell22_2617911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_2617911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617911 prefixEnd_2617911 := by exact prefixLift 2617911
  have htrace : WordTrace (prefixWord ++ tailWord_2617911) baseStart_2617911 baseEnd_2617911 := by
    simpa [prefixWord, tailWord_2617911, baseEnd_2617911] using wordTrace_append hprefix tailTrace_2617911
  have hstable : (prefixWord ++ tailWord_2617911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617911).length < 2 ^ (prefixWord ++ tailWord_2617911).sum := by decide
  have hdescent : baseEnd_2617911 < baseStart_2617911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617984 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_2617984 : Nat := 118140960795 + 2617984 * 2 ^ 59
def prefixEnd_2617984 : Nat := 4983230072969 + 3 ^ 40 * 2617984 * 2
def baseEnd_2617984 : Nat := 896189425186926906173411

theorem tailTrace_2617984 : CollatzResearch.WordTrace tailWord_2617984 prefixEnd_2617984 896189425186926906173411 := by
  unfold tailWord_2617984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742860473749279457790503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63657147298332372610387337 47742860473749279457790503)
  ·
    refine ⟨71614290710623919186685755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47742860473749279457790503 71614290710623919186685755)
    ·
      refine ⟨107421436065935878780028633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71614290710623919186685755 107421436065935878780028633)
      ·
        refine ⟨80566077049451909085021475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107421436065935878780028633 80566077049451909085021475)
        ·
          refine ⟨120849115574177863627532213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80566077049451909085021475 120849115574177863627532213)
          ·
            refine ⟨11329604585079174715081145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120849115574177863627532213 11329604585079174715081145)
            ·
              refine ⟨8497203438809381036310859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11329604585079174715081145 8497203438809381036310859)
              ·
                refine ⟨12745805158214071554466289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8497203438809381036310859 12745805158214071554466289)
                ·
                  refine ⟨9559353868660553665849717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12745805158214071554466289 9559353868660553665849717)
                  ·
                    refine ⟨896189425186926906173411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9559353868660553665849717 896189425186926906173411)
                    ·
                      rfl

theorem cell22_2617984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_2617984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2617984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2617984 prefixEnd_2617984 := by exact prefixLift 2617984
  have htrace : WordTrace (prefixWord ++ tailWord_2617984) baseStart_2617984 baseEnd_2617984 := by
    simpa [prefixWord, tailWord_2617984, baseEnd_2617984] using wordTrace_append hprefix tailTrace_2617984
  have hstable : (prefixWord ++ tailWord_2617984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617984).length < 2 ^ (prefixWord ++ tailWord_2617984).sum := by decide
  have hdescent : baseEnd_2617984 < baseStart_2617984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618031 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 6]
def baseStart_2618031 : Nat := 118140960795 + 2618031 * 2 ^ 59
def prefixEnd_2618031 : Nat := 4983230072969 + 3 ^ 40 * 2618031 * 2
def baseEnd_2618031 : Nat := 298735171415811483416089

theorem tailTrace_2618031 : CollatzResearch.WordTrace tailWord_2618031 prefixEnd_2618031 298735171415811483416089 := by
  unfold tailWord_2618031
  simp only [CollatzResearch.WordTrace]
  refine ⟨95487435178328285942541947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63658290118885523961694631 95487435178328285942541947)
  ·
    refine ⟨143231152767492428913812921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95487435178328285942541947 143231152767492428913812921)
    ·
      refine ⟨107423364575619321685359691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143231152767492428913812921 107423364575619321685359691)
      ·
        refine ⟨161135046863428982528039537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107423364575619321685359691 161135046863428982528039537)
        ·
          refine ⟨120851285147571736896029653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161135046863428982528039537 120851285147571736896029653)
          ·
            refine ⟨2832451995646212583500695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120851285147571736896029653 2832451995646212583500695)
            ·
              refine ⟨4248677993469318875251043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832451995646212583500695 4248677993469318875251043)
              ·
                refine ⟨6373016990203978312876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248677993469318875251043 6373016990203978312876565)
                ·
                  refine ⟨298735171415811483416089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6373016990203978312876565 298735171415811483416089)
                  ·
                    rfl

theorem cell22_2618031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].length) (baseStart_2618031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618031 prefixEnd_2618031 := by exact prefixLift 2618031
  have htrace : WordTrace (prefixWord ++ tailWord_2618031) baseStart_2618031 baseEnd_2618031 := by
    simpa [prefixWord, tailWord_2618031, baseEnd_2618031] using wordTrace_append hprefix tailTrace_2618031
  have hstable : (prefixWord ++ tailWord_2618031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618031).length < 2 ^ (prefixWord ++ tailWord_2618031).sum := by decide
  have hdescent : baseEnd_2618031 < baseStart_2618031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618046 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2618046 : Nat := 118140960795 + 2618046 * 2 ^ 59
def prefixEnd_2618046 : Nat := 4983230072969 + 3 ^ 40 * 2618046 * 2
def baseEnd_2618046 : Nat := 896210649053979411123221

theorem tailTrace_2618046 : CollatzResearch.WordTrace tailWord_2618046 prefixEnd_2618046 896210649053979411123221 := by
  unfold tailWord_2618046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935997784159242938042249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63658654848849295669558661 11935997784159242938042249)
  ·
    refine ⟨8951998338119432203531687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11935997784159242938042249 8951998338119432203531687)
    ·
      refine ⟨13427997507179148305297531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951998338119432203531687 13427997507179148305297531)
      ·
        refine ⟨20141996260768722457946297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427997507179148305297531 20141996260768722457946297)
        ·
          refine ⟨15106497195576541843459723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20141996260768722457946297 15106497195576541843459723)
          ·
            refine ⟨22659745793364812765189585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15106497195576541843459723 22659745793364812765189585)
            ·
              refine ⟨16994809345023609573892189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22659745793364812765189585 16994809345023609573892189)
              ·
                refine ⟨6373053504383853590209571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16994809345023609573892189 6373053504383853590209571)
                ·
                  refine ⟨9559580256575780385314357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373053504383853590209571 9559580256575780385314357)
                  ·
                    refine ⟨896210649053979411123221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9559580256575780385314357 896210649053979411123221)
                    ·
                      rfl

theorem cell22_2618046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2618046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618046 prefixEnd_2618046 := by exact prefixLift 2618046
  have htrace : WordTrace (prefixWord ++ tailWord_2618046) baseStart_2618046 baseEnd_2618046 := by
    simpa [prefixWord, tailWord_2618046, baseEnd_2618046] using wordTrace_append hprefix tailTrace_2618046
  have hstable : (prefixWord ++ tailWord_2618046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618046).length < 2 ^ (prefixWord ++ tailWord_2618046).sum := by decide
  have hdescent : baseEnd_2618046 < baseStart_2618046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618076 : List Nat := [2, 2, 5, 1, 1, 11]
def baseStart_2618076 : Nat := 118140960795 + 2618076 * 2 ^ 59
def prefixEnd_2618076 : Nat := 4983230072969 + 3 ^ 40 * 2618076 * 2
def baseEnd_2618076 : Nat := 11064455786013201640409

theorem tailTrace_2618076 : CollatzResearch.WordTrace tailWord_2618076 prefixEnd_2618076 11064455786013201640409 := by
  unfold tailWord_2618076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47744538231582629313965041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63659384308776839085286721 47744538231582629313965041)
  ·
    refine ⟨35808403673686971985473781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47744538231582629313965041 35808403673686971985473781)
    ·
      refine ⟨3357037844408153623638167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35808403673686971985473781 3357037844408153623638167)
      ·
        refine ⟨5035556766612230435457251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357037844408153623638167 5035556766612230435457251)
        ·
          refine ⟨7553335149918345653185877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035556766612230435457251 7553335149918345653185877)
          ·
            refine ⟨11064455786013201640409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7553335149918345653185877 11064455786013201640409)
            ·
              rfl

theorem cell22_2618076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 11].length) (baseStart_2618076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618076 prefixEnd_2618076 := by exact prefixLift 2618076
  have htrace : WordTrace (prefixWord ++ tailWord_2618076) baseStart_2618076 baseEnd_2618076 := by
    simpa [prefixWord, tailWord_2618076, baseEnd_2618076] using wordTrace_append hprefix tailTrace_2618076
  have hstable : (prefixWord ++ tailWord_2618076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618076).length < 2 ^ (prefixWord ++ tailWord_2618076).sum := by decide
  have hdescent : baseEnd_2618076 < baseStart_2618076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618089 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2618089 : Nat := 118140960795 + 2618089 * 2 ^ 59
def prefixEnd_2618089 : Nat := 4983230072969 + 3 ^ 40 * 2618089 * 2
def baseEnd_2618089 : Nat := 896225368832741632298089

theorem tailTrace_2618089 : CollatzResearch.WordTrace tailWord_2618089 prefixEnd_2618089 896225368832741632298089 := by
  unfold tailWord_2618089
  simp only [CollatzResearch.WordTrace]
  refine ⟨95489550612118161848153321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63659700408078774565435547 95489550612118161848153321)
  ·
    refine ⟨71617162959088621386114991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95489550612118161848153321 71617162959088621386114991)
    ·
      refine ⟨107425744438632932079172487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71617162959088621386114991 107425744438632932079172487)
      ·
        refine ⟨161138616657949398118758731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107425744438632932079172487 161138616657949398118758731)
        ·
          refine ⟨241707924986924097178138097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161138616657949398118758731 241707924986924097178138097)
          ·
            refine ⟨181280943740193072883603573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241707924986924097178138097 181280943740193072883603573)
            ·
              refine ⟨16995088475643100582837835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181280943740193072883603573 16995088475643100582837835)
              ·
                refine ⟨25492632713464650874256753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16995088475643100582837835 25492632713464650874256753)
                ·
                  refine ⟨19119474535098488155692565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25492632713464650874256753 19119474535098488155692565)
                  ·
                    refine ⟨896225368832741632298089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19119474535098488155692565 896225368832741632298089)
                    ·
                      rfl

theorem cell22_2618089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2618089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618089 prefixEnd_2618089 := by exact prefixLift 2618089
  have htrace : WordTrace (prefixWord ++ tailWord_2618089) baseStart_2618089 baseEnd_2618089 := by
    simpa [prefixWord, tailWord_2618089, baseEnd_2618089] using wordTrace_append hprefix tailTrace_2618089
  have hstable : (prefixWord ++ tailWord_2618089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618089).length < 2 ^ (prefixWord ++ tailWord_2618089).sum := by decide
  have hdescent : baseEnd_2618089 < baseStart_2618089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618091 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 3, 3]
def baseStart_2618091 : Nat := 118140960795 + 2618091 * 2 ^ 59
def prefixEnd_2618091 : Nat := 4983230072969 + 3 ^ 40 * 2618091 * 2
def baseEnd_2618091 : Nat := 896226053473614293748083

theorem tailTrace_2618091 : CollatzResearch.WordTrace tailWord_2618091 prefixEnd_2618091 896226053473614293748083 := by
  unfold tailWord_2618091
  simp only [CollatzResearch.WordTrace]
  refine ⟨95489623558110916189726127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63659749038740610793150751 95489623558110916189726127)
  ·
    refine ⟨143234435337166374284589191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95489623558110916189726127 143234435337166374284589191)
    ·
      refine ⟨214851653005749561426883787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143234435337166374284589191 214851653005749561426883787)
      ·
        refine ⟨322277479508624342140325681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214851653005749561426883787 322277479508624342140325681)
        ·
          refine ⟨241708109631468256605244261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322277479508624342140325681 241708109631468256605244261)
          ·
            refine ⟨45320270555900298113483299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241708109631468256605244261 45320270555900298113483299)
            ·
              refine ⟨67980405833850447170224949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45320270555900298113483299 67980405833850447170224949)
              ·
                refine ⟨6373163046923479422208589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67980405833850447170224949 6373163046923479422208589)
                ·
                  refine ⟨2389936142596304783328221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373163046923479422208589 2389936142596304783328221)
                  ·
                    refine ⟨896226053473614293748083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389936142596304783328221 896226053473614293748083)
                    ·
                      rfl

theorem cell22_2618091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].length) (baseStart_2618091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618091 prefixEnd_2618091 := by exact prefixLift 2618091
  have htrace : WordTrace (prefixWord ++ tailWord_2618091) baseStart_2618091 baseEnd_2618091 := by
    simpa [prefixWord, tailWord_2618091, baseEnd_2618091] using wordTrace_append hprefix tailTrace_2618091
  have hstable : (prefixWord ++ tailWord_2618091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618091).length < 2 ^ (prefixWord ++ tailWord_2618091).sum := by decide
  have hdescent : baseEnd_2618091 < baseStart_2618091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618108 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_2618108 : Nat := 118140960795 + 2618108 * 2 ^ 59
def prefixEnd_2618108 : Nat := 4983230072969 + 3 ^ 40 * 2618108 * 2
def baseEnd_2618108 : Nat := 896231872921031916073031

theorem tailTrace_2618108 : CollatzResearch.WordTrace tailWord_2618108 prefixEnd_2618108 896231872921031916073031 := by
  unfold tailWord_2618108
  simp only [CollatzResearch.WordTrace]
  refine ⟨47745121799524664046547489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63660162399366218728729985 47745121799524664046547489)
  ·
    refine ⟨35808841349643498034910617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47745121799524664046547489 35808841349643498034910617)
    ·
      refine ⟨26856631012232623526182963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35808841349643498034910617 26856631012232623526182963)
      ·
        refine ⟨40284946518348935289274445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26856631012232623526182963 40284946518348935289274445)
        ·
          refine ⟨15106854944380850733477917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40284946518348935289274445 15106854944380850733477917)
          ·
            refine ⟨5665070604142819025054219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15106854944380850733477917 5665070604142819025054219)
            ·
              refine ⟨8497605906214228537581329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665070604142819025054219 8497605906214228537581329)
              ·
                refine ⟨6373204429660671403185997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497605906214228537581329 6373204429660671403185997)
                ·
                  refine ⟨2389951661122751776194749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373204429660671403185997 2389951661122751776194749)
                  ·
                    refine ⟨896231872921031916073031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2389951661122751776194749 896231872921031916073031)
                    ·
                      rfl

theorem cell22_2618108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_2618108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618108 prefixEnd_2618108 := by exact prefixLift 2618108
  have htrace : WordTrace (prefixWord ++ tailWord_2618108) baseStart_2618108 baseEnd_2618108 := by
    simpa [prefixWord, tailWord_2618108, baseEnd_2618108] using wordTrace_append hprefix tailTrace_2618108
  have hstable : (prefixWord ++ tailWord_2618108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618108).length < 2 ^ (prefixWord ++ tailWord_2618108).sum := by decide
  have hdescent : baseEnd_2618108 < baseStart_2618108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618168 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_2618168 : Nat := 118140960795 + 2618168 * 2 ^ 59
def prefixEnd_2618168 : Nat := 4983230072969 + 3 ^ 40 * 2618168 * 2
def baseEnd_2618168 : Nat := 896252412147211759572847

theorem tailTrace_2618168 : CollatzResearch.WordTrace tailWord_2618168 prefixEnd_2618168 896252412147211759572847 := by
  unfold tailWord_2618168
  simp only [CollatzResearch.WordTrace]
  refine ⟨47746215989415979170139579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63661621319221305560186105 47746215989415979170139579)
  ·
    refine ⟨71619323984123968755209369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47746215989415979170139579 71619323984123968755209369)
    ·
      refine ⟨53714492988092976566407027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71619323984123968755209369 53714492988092976566407027)
      ·
        refine ⟨80571739482139464849610541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53714492988092976566407027 80571739482139464849610541)
        ·
          refine ⟨30214402305802299318603953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80571739482139464849610541 30214402305802299318603953)
          ·
            refine ⟨22660801729351724488952965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30214402305802299318603953 22660801729351724488952965)
            ·
              refine ⟨4248900324253448341678681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22660801729351724488952965 4248900324253448341678681)
              ·
                refine ⟨3186675243190086256259011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248900324253448341678681 3186675243190086256259011)
                ·
                  refine ⟨4780012864785129384388517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186675243190086256259011 4780012864785129384388517)
                  ·
                    refine ⟨896252412147211759572847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780012864785129384388517 896252412147211759572847)
                    ·
                      rfl

theorem cell22_2618168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_2618168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618168 prefixEnd_2618168 := by exact prefixLift 2618168
  have htrace : WordTrace (prefixWord ++ tailWord_2618168) baseStart_2618168 baseEnd_2618168 := by
    simpa [prefixWord, tailWord_2618168, baseEnd_2618168] using wordTrace_append hprefix tailTrace_2618168
  have hstable : (prefixWord ++ tailWord_2618168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618168).length < 2 ^ (prefixWord ++ tailWord_2618168).sum := by decide
  have hdescent : baseEnd_2618168 < baseStart_2618168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618211 : List Nat := [1, 1, 1, 5, 3, 1, 1, 9]
def baseStart_2618211 : Nat := 118140960795 + 2618211 * 2 ^ 59
def prefixEnd_2618211 : Nat := 4983230072969 + 3 ^ 40 * 2618211 * 2
def baseEnd_2618211 : Nat := 99585236880663775638635

theorem tailTrace_2618211 : CollatzResearch.WordTrace tailWord_2618211 prefixEnd_2618211 99585236880663775638635 := by
  unfold tailWord_2618211
  simp only [CollatzResearch.WordTrace]
  refine ⟨95494000317676176684094487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63662666878450784456062991 95494000317676176684094487)
  ·
    refine ⟨143241000476514265026141731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95494000317676176684094487 143241000476514265026141731)
    ·
      refine ⟨214861500714771397539212597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143241000476514265026141731 214861500714771397539212597)
      ·
        refine ⟨20143265692009818519301181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214861500714771397539212597 20143265692009818519301181)
        ·
          refine ⟨7553724634503681944737943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20143265692009818519301181 7553724634503681944737943)
          ·
            refine ⟨11330586951755522917106915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553724634503681944737943 11330586951755522917106915)
            ·
              refine ⟨16995880427633284375660373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11330586951755522917106915 16995880427633284375660373)
              ·
                refine ⟨99585236880663775638635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16995880427633284375660373 99585236880663775638635)
                ·
                  rfl

theorem cell22_2618211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_2618211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618211 prefixEnd_2618211 := by exact prefixLift 2618211
  have htrace : WordTrace (prefixWord ++ tailWord_2618211) baseStart_2618211 baseEnd_2618211 := by
    simpa [prefixWord, tailWord_2618211, baseEnd_2618211] using wordTrace_append hprefix tailTrace_2618211
  have hstable : (prefixWord ++ tailWord_2618211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618211).length < 2 ^ (prefixWord ++ tailWord_2618211).sum := by decide
  have hdescent : baseEnd_2618211 < baseStart_2618211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618215 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 2, 3]
def baseStart_2618215 : Nat := 118140960795 + 2618215 * 2 ^ 59
def prefixEnd_2618215 : Nat := 4983230072969 + 3 ^ 40 * 2618215 * 2
def baseEnd_2618215 : Nat := 896268501207719303647703

theorem tailTrace_2618215 : CollatzResearch.WordTrace tailWord_2618215 prefixEnd_2618215 896268501207719303647703 := by
  unfold tailWord_2618215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95494146209661685367240099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63662764139774456911493399 95494146209661685367240099)
  ·
    refine ⟨143241219314492528050860149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95494146209661685367240099 143241219314492528050860149)
    ·
      refine ⟨13428864310733674504768139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143241219314492528050860149 13428864310733674504768139)
      ·
        refine ⟨20143296466100511757152209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13428864310733674504768139 20143296466100511757152209)
        ·
          refine ⟨15107472349575383817864157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20143296466100511757152209 15107472349575383817864157)
          ·
            refine ⟨5665302131090768931699059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15107472349575383817864157 5665302131090768931699059)
            ·
              refine ⟨8497953196636153397548589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665302131090768931699059 8497953196636153397548589)
              ·
                refine ⟨3186732448738557524080721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8497953196636153397548589 3186732448738557524080721)
                ·
                  refine ⟨2390049336553918143060541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186732448738557524080721 2390049336553918143060541)
                  ·
                    refine ⟨896268501207719303647703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390049336553918143060541 896268501207719303647703)
                    ·
                      rfl

theorem cell22_2618215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_2618215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618215 prefixEnd_2618215 := by exact prefixLift 2618215
  have htrace : WordTrace (prefixWord ++ tailWord_2618215) baseStart_2618215 baseEnd_2618215 := by
    simpa [prefixWord, tailWord_2618215, baseEnd_2618215] using wordTrace_append hprefix tailTrace_2618215
  have hstable : (prefixWord ++ tailWord_2618215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618215).length < 2 ^ (prefixWord ++ tailWord_2618215).sum := by decide
  have hdescent : baseEnd_2618215 < baseStart_2618215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618226 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2618226 : Nat := 118140960795 + 2618226 * 2 ^ 59
def prefixEnd_2618226 : Nat := 4983230072969 + 3 ^ 40 * 2618226 * 2
def baseEnd_2618226 : Nat := 896272266732518941622669

theorem tailTrace_2618226 : CollatzResearch.WordTrace tailWord_2618226 prefixEnd_2618226 896272266732518941622669 := by
  unfold tailWord_2618226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23873636853155458561472633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63663031608414556163927021 23873636853155458561472633)
  ·
    refine ⟨17905227639866593921104475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23873636853155458561472633 17905227639866593921104475)
    ·
      refine ⟨26857841459799890881656713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17905227639866593921104475 26857841459799890881656713)
      ·
        refine ⟨20143381094849918161242535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26857841459799890881656713 20143381094849918161242535)
        ·
          refine ⟨30215071642274877241863803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143381094849918161242535 30215071642274877241863803)
          ·
            refine ⟨45322607463412315862795705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30215071642274877241863803 45322607463412315862795705)
            ·
              refine ⟨33991955597559236897096779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45322607463412315862795705 33991955597559236897096779)
              ·
                refine ⟨50987933396338855345645169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33991955597559236897096779 50987933396338855345645169)
                ·
                  refine ⟨38240950047254141509233877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50987933396338855345645169 38240950047254141509233877)
                  ·
                    refine ⟨896272266732518941622669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38240950047254141509233877 896272266732518941622669)
                    ·
                      rfl

theorem cell22_2618226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2618226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618226 prefixEnd_2618226 := by exact prefixLift 2618226
  have htrace : WordTrace (prefixWord ++ tailWord_2618226) baseStart_2618226 baseEnd_2618226 := by
    simpa [prefixWord, tailWord_2618226, baseEnd_2618226] using wordTrace_append hprefix tailTrace_2618226
  have hstable : (prefixWord ++ tailWord_2618226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618226).length < 2 ^ (prefixWord ++ tailWord_2618226).sum := by decide
  have hdescent : baseEnd_2618226 < baseStart_2618226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618230 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2618230 : Nat := 118140960795 + 2618230 * 2 ^ 59
def prefixEnd_2618230 : Nat := 4983230072969 + 3 ^ 40 * 2618230 * 2
def baseEnd_2618230 : Nat := 896273636014264264522657

theorem tailTrace_2618230 : CollatzResearch.WordTrace tailWord_2618230 prefixEnd_2618230 896273636014264264522657 := by
  unfold tailWord_2618230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968418331537958933064759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63663128869738228619357429 5968418331537958933064759)
  ·
    refine ⟨8952627497306938399597139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5968418331537958933064759 8952627497306938399597139)
    ·
      refine ⟨13428941245960407599395709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8952627497306938399597139 13428941245960407599395709)
      ·
        refine ⟨5035852967235152849773391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13428941245960407599395709 5035852967235152849773391)
        ·
          refine ⟨7553779450852729274660087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035852967235152849773391 7553779450852729274660087)
          ·
            refine ⟨11330669176279093911990131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553779450852729274660087 11330669176279093911990131)
            ·
              refine ⟨16996003764418640867985197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11330669176279093911990131 16996003764418640867985197)
              ·
                refine ⟨6373501411656990325494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16996003764418640867985197 6373501411656990325494449)
                ·
                  refine ⟨4780126058742742744120837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6373501411656990325494449 4780126058742742744120837)
                  ·
                    refine ⟨896273636014264264522657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780126058742742744120837 896273636014264264522657)
                    ·
                      rfl

theorem cell22_2618230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2618230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618230 prefixEnd_2618230 := by exact prefixLift 2618230
  have htrace : WordTrace (prefixWord ++ tailWord_2618230) baseStart_2618230 baseEnd_2618230 := by
    simpa [prefixWord, tailWord_2618230, baseEnd_2618230] using wordTrace_append hprefix tailTrace_2618230
  have hstable : (prefixWord ++ tailWord_2618230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618230).length < 2 ^ (prefixWord ++ tailWord_2618230).sum := by decide
  have hdescent : baseEnd_2618230 < baseStart_2618230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618260 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2618260 : Nat := 118140960795 + 2618260 * 2 ^ 59
def prefixEnd_2618260 : Nat := 4983230072969 + 3 ^ 40 * 2618260 * 2
def baseEnd_2618260 : Nat := 896283905627354186272565

theorem tailTrace_2618260 : CollatzResearch.WordTrace tailWord_2618260 prefixEnd_2618260 896283905627354186272565 := by
  unfold tailWord_2618260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47747893747249329026314117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63663858329665772035085489 47747893747249329026314117)
  ·
    refine ⟨8952730077609249192433897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47747893747249329026314117 8952730077609249192433897)
    ·
      refine ⟨6714547558206936894325423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8952730077609249192433897 6714547558206936894325423)
      ·
        refine ⟨10071821337310405341488135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714547558206936894325423 10071821337310405341488135)
        ·
          refine ⟨15107732005965608012232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071821337310405341488135 15107732005965608012232203)
          ·
            refine ⟨22661598008948412018348305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15107732005965608012232203 22661598008948412018348305)
            ·
              refine ⟨16996198506711309013761229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22661598008948412018348305 16996198506711309013761229)
              ·
                refine ⟨6373574440016740880160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16996198506711309013761229 6373574440016740880160461)
                ·
                  refine ⟨2390090415006277830060173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373574440016740880160461 2390090415006277830060173)
                  ·
                    refine ⟨896283905627354186272565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390090415006277830060173 896283905627354186272565)
                    ·
                      rfl

theorem cell22_2618260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2618260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618260 prefixEnd_2618260 := by exact prefixLift 2618260
  have htrace : WordTrace (prefixWord ++ tailWord_2618260) baseStart_2618260 baseEnd_2618260 := by
    simpa [prefixWord, tailWord_2618260, baseEnd_2618260] using wordTrace_append hprefix tailTrace_2618260
  have hstable : (prefixWord ++ tailWord_2618260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618260).length < 2 ^ (prefixWord ++ tailWord_2618260).sum := by decide
  have hdescent : baseEnd_2618260 < baseStart_2618260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618262 : List Nat := [5, 3, 1, 1, 1, 1, 3, 7]
def baseStart_2618262 : Nat := 118140960795 + 2618262 * 2 ^ 59
def prefixEnd_2618262 : Nat := 4983230072969 + 3 ^ 40 * 2618262 * 2
def baseEnd_2618262 : Nat := 99587176696469649746951

theorem tailTrace_2618262 : CollatzResearch.WordTrace tailWord_2618262 prefixEnd_2618262 99587176696469649746951 := by
  unfold tailWord_2618262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968491277530713274637565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63663906960327608262800693 5968491277530713274637565)
  ·
    refine ⟨2238184229074017477989087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5968491277530713274637565 2238184229074017477989087)
    ·
      refine ⟨3357276343611026216983631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238184229074017477989087 3357276343611026216983631)
      ·
        refine ⟨5035914515416539325475447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357276343611026216983631 5035914515416539325475447)
        ·
          refine ⟨7553871773124808988213171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035914515416539325475447 7553871773124808988213171)
          ·
            refine ⟨11330807659687213482319757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553871773124808988213171 11330807659687213482319757)
            ·
              refine ⟨4249052872382705055869909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11330807659687213482319757 4249052872382705055869909)
              ·
                refine ⟨99587176696469649746951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4249052872382705055869909 99587176696469649746951)
                ·
                  rfl

theorem cell22_2618262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_2618262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618262 prefixEnd_2618262 := by exact prefixLift 2618262
  have htrace : WordTrace (prefixWord ++ tailWord_2618262) baseStart_2618262 baseEnd_2618262 := by
    simpa [prefixWord, tailWord_2618262, baseEnd_2618262] using wordTrace_append hprefix tailTrace_2618262
  have hstable : (prefixWord ++ tailWord_2618262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618262).length < 2 ^ (prefixWord ++ tailWord_2618262).sum := by decide
  have hdescent : baseEnd_2618262 < baseStart_2618262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618318 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_2618318 : Nat := 118140960795 + 2618318 * 2 ^ 59
def prefixEnd_2618318 : Nat := 4983230072969 + 3 ^ 40 * 2618318 * 2
def baseEnd_2618318 : Nat := 298767920070887122774129

theorem tailTrace_2618318 : CollatzResearch.WordTrace tailWord_2618318 prefixEnd_2618318 298767920070887122774129 := by
  unfold tailWord_2618318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937237866036066744779951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63665268618859022638826405 11937237866036066744779951)
  ·
    refine ⟨17905856799054100117169927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937237866036066744779951 17905856799054100117169927)
    ·
      refine ⟨26858785198581150175754891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17905856799054100117169927 26858785198581150175754891)
      ·
        refine ⟨40288177797871725263632337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26858785198581150175754891 40288177797871725263632337)
        ·
          refine ⟨30216133348403793947724253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40288177797871725263632337 30216133348403793947724253)
          ·
            refine ⟨11331050005651422730396595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30216133348403793947724253 11331050005651422730396595)
            ·
              refine ⟨16996575008477134095594893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331050005651422730396595 16996575008477134095594893)
              ·
                refine ⟨6373715628178925285848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16996575008477134095594893 6373715628178925285848085)
                ·
                  refine ⟨298767920070887122774129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6373715628178925285848085 298767920070887122774129)
                  ·
                    rfl

theorem cell22_2618318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_2618318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618318 prefixEnd_2618318 := by exact prefixLift 2618318
  have htrace : WordTrace (prefixWord ++ tailWord_2618318) baseStart_2618318 baseEnd_2618318 := by
    simpa [prefixWord, tailWord_2618318, baseEnd_2618318] using wordTrace_append hprefix tailTrace_2618318
  have hstable : (prefixWord ++ tailWord_2618318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618318).length < 2 ^ (prefixWord ++ tailWord_2618318).sum := by decide
  have hdescent : baseEnd_2618318 < baseStart_2618318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618412 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_2618412 : Nat := 118140960795 + 2618412 * 2 ^ 59
def prefixEnd_2618412 : Nat := 4983230072969 + 3 ^ 40 * 2618412 * 2
def baseEnd_2618412 : Nat := 896335938333676456472099

theorem tailTrace_2618412 : CollatzResearch.WordTrace tailWord_2618412 prefixEnd_2618412 896335938333676456472099 := by
  unfold tailWord_2618412
  simp only [CollatzResearch.WordTrace]
  refine ⟨47750665694973994006080745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63667554259965325341440993 47750665694973994006080745)
  ·
    refine ⟨35812999271230495504560559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47750665694973994006080745 35812999271230495504560559)
    ·
      refine ⟨53719498906845743256840839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35812999271230495504560559 53719498906845743256840839)
      ·
        refine ⟨80579248360268614885261259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53719498906845743256840839 80579248360268614885261259)
        ·
          refine ⟨120868872540402922327891889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80579248360268614885261259 120868872540402922327891889)
          ·
            refine ⟨90651654405302191745918917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120868872540402922327891889 90651654405302191745918917)
            ·
              refine ⟨16997185200994160952359797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90651654405302191745918917 16997185200994160952359797)
              ·
                refine ⟨1593486112593202589283731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16997185200994160952359797 1593486112593202589283731)
                ·
                  refine ⟨2390229168889803883925597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593486112593202589283731 2390229168889803883925597)
                  ·
                    refine ⟨896335938333676456472099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390229168889803883925597 896335938333676456472099)
                    ·
                      rfl

theorem cell22_2618412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_2618412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618412 prefixEnd_2618412 := by exact prefixLift 2618412
  have htrace : WordTrace (prefixWord ++ tailWord_2618412) baseStart_2618412 baseEnd_2618412 := by
    simpa [prefixWord, tailWord_2618412, baseEnd_2618412] using wordTrace_append hprefix tailTrace_2618412
  have hstable : (prefixWord ++ tailWord_2618412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618412).length < 2 ^ (prefixWord ++ tailWord_2618412).sum := by decide
  have hdescent : baseEnd_2618412 < baseStart_2618412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618423 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2618423 : Nat := 118140960795 + 2618423 * 2 ^ 59
def prefixEnd_2618423 : Nat := 4983230072969 + 3 ^ 40 * 2618423 * 2
def baseEnd_2618423 : Nat := 896339703858476094447065

theorem tailTrace_2618423 : CollatzResearch.WordTrace tailWord_2618423 prefixEnd_2618423 896339703858476094447065 := by
  unfold tailWord_2618423
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501732592908136890811923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63667821728605424593874615 95501732592908136890811923)
  ·
    refine ⟨143252598889362205336217885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95501732592908136890811923 143252598889362205336217885)
    ·
      refine ⟨53719724583510827001081707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143252598889362205336217885 53719724583510827001081707)
      ·
        refine ⟨80579586875266240501622561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53719724583510827001081707 80579586875266240501622561)
        ·
          refine ⟨60434690156449680376216921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80579586875266240501622561 60434690156449680376216921)
          ·
            refine ⟨45326017617337260282162691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60434690156449680376216921 45326017617337260282162691)
            ·
              refine ⟨67989026426005890423244037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45326017617337260282162691 67989026426005890423244037)
              ·
                refine ⟨12747942454876104454358257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67989026426005890423244037 12747942454876104454358257)
                ·
                  refine ⟨9560956841157078340768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12747942454876104454358257 9560956841157078340768693)
                  ·
                    refine ⟨896339703858476094447065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9560956841157078340768693 896339703858476094447065)
                    ·
                      rfl

theorem cell22_2618423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2618423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618423 prefixEnd_2618423 := by exact prefixLift 2618423
  have htrace : WordTrace (prefixWord ++ tailWord_2618423) baseStart_2618423 baseEnd_2618423 := by
    simpa [prefixWord, tailWord_2618423, baseEnd_2618423] using wordTrace_append hprefix tailTrace_2618423
  have hstable : (prefixWord ++ tailWord_2618423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618423).length < 2 ^ (prefixWord ++ tailWord_2618423).sum := by decide
  have hdescent : baseEnd_2618423 < baseStart_2618423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618425 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 5]
def baseStart_2618425 : Nat := 118140960795 + 2618425 * 2 ^ 59
def prefixEnd_2618425 : Nat := 4983230072969 + 3 ^ 40 * 2618425 * 2
def baseEnd_2618425 : Nat := 298780129499782918632353

theorem tailTrace_2618425 : CollatzResearch.WordTrace tailWord_2618425 prefixEnd_2618425 298780129499782918632353 := by
  unfold tailWord_2618425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501805538900891232384729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63667870359267260821589819 95501805538900891232384729)
  ·
    refine ⟨71626354154175668424288547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95501805538900891232384729 71626354154175668424288547)
    ·
      refine ⟨107439531231263502636432821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71626354154175668424288547 107439531231263502636432821)
      ·
        refine ⟨10072456052930953372165577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107439531231263502636432821 10072456052930953372165577)
        ·
          refine ⟨7554342039698215029124183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10072456052930953372165577 7554342039698215029124183)
          ·
            refine ⟨11331513059547322543686275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554342039698215029124183 11331513059547322543686275)
            ·
              refine ⟨16997269589320983815529413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331513059547322543686275 16997269589320983815529413)
              ·
                refine ⟨3186988047997684465411765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16997269589320983815529413 3186988047997684465411765)
                ·
                  refine ⟨298780129499782918632353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3186988047997684465411765 298780129499782918632353)
                  ·
                    rfl

theorem cell22_2618425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_2618425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618425 prefixEnd_2618425 := by exact prefixLift 2618425
  have htrace : WordTrace (prefixWord ++ tailWord_2618425) baseStart_2618425 baseEnd_2618425 := by
    simpa [prefixWord, tailWord_2618425, baseEnd_2618425] using wordTrace_append hprefix tailTrace_2618425
  have hstable : (prefixWord ++ tailWord_2618425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618425).length < 2 ^ (prefixWord ++ tailWord_2618425).sum := by decide
  have hdescent : baseEnd_2618425 < baseStart_2618425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618429 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_2618429 : Nat := 118140960795 + 2618429 * 2 ^ 59
def prefixEnd_2618429 : Nat := 4983230072969 + 3 ^ 40 * 2618429 * 2
def baseEnd_2618429 : Nat := 896341757781094078797047

theorem tailTrace_2618429 : CollatzResearch.WordTrace tailWord_2618429 prefixEnd_2618429 896341757781094078797047 := by
  unfold tailWord_2618429
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501951430886399915530341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63667967620590933277020227 95501951430886399915530341)
  ·
    refine ⟨17906615893291199984161939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95501951430886399915530341 17906615893291199984161939)
    ·
      refine ⟨26859923839936799976242909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17906615893291199984161939 26859923839936799976242909)
      ·
        refine ⟨10072471439976299991091091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26859923839936799976242909 10072471439976299991091091)
        ·
          refine ⟨15108707159964449986636637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072471439976299991091091 15108707159964449986636637)
          ·
            refine ⟨5665765184986668744988739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15108707159964449986636637 5665765184986668744988739)
            ·
              refine ⟨8498647777480003117483109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665765184986668744988739 8498647777480003117483109)
              ·
                refine ⟨1593496458277500584528083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8498647777480003117483109 1593496458277500584528083)
                ·
                  refine ⟨2390244687416250876792125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593496458277500584528083 2390244687416250876792125)
                  ·
                    refine ⟨896341757781094078797047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390244687416250876792125 896341757781094078797047)
                    ·
                      rfl

theorem cell22_2618429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_2618429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618429 prefixEnd_2618429 := by exact prefixLift 2618429
  have htrace : WordTrace (prefixWord ++ tailWord_2618429) baseStart_2618429 baseEnd_2618429 := by
    simpa [prefixWord, tailWord_2618429, baseEnd_2618429] using wordTrace_append hprefix tailTrace_2618429
  have hstable : (prefixWord ++ tailWord_2618429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618429).length < 2 ^ (prefixWord ++ tailWord_2618429).sum := by decide
  have hdescent : baseEnd_2618429 < baseStart_2618429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618455 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2618455 : Nat := 118140960795 + 2618455 * 2 ^ 59
def prefixEnd_2618455 : Nat := 4983230072969 + 3 ^ 40 * 2618455 * 2
def baseEnd_2618455 : Nat := 896350658112438677646967

theorem tailTrace_2618455 : CollatzResearch.WordTrace tailWord_2618455 prefixEnd_2618455 896350658112438677646967 := by
  unfold tailWord_2618455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95502899728792206355976819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63668599819194804237317879 95502899728792206355976819)
  ·
    refine ⟨143254349593188309533965229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95502899728792206355976819 143254349593188309533965229)
    ·
      refine ⟨53720381097445616075236961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143254349593188309533965229 53720381097445616075236961)
      ·
        refine ⟨40290285823084212056427721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53720381097445616075236961 40290285823084212056427721)
        ·
          refine ⟨30217714367313159042320791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40290285823084212056427721 30217714367313159042320791)
          ·
            refine ⟨45326571550969738563481187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30217714367313159042320791 45326571550969738563481187)
            ·
              refine ⟨67989857326454607845221781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45326571550969738563481187 67989857326454607845221781)
              ·
                refine ⟨3187024562177559742744771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67989857326454607845221781 3187024562177559742744771)
                ·
                  refine ⟨4780536843266339614117157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187024562177559742744771 4780536843266339614117157)
                  ·
                    refine ⟨896350658112438677646967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780536843266339614117157 896350658112438677646967)
                    ·
                      rfl

theorem cell22_2618455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2618455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618455 prefixEnd_2618455 := by exact prefixLift 2618455
  have htrace : WordTrace (prefixWord ++ tailWord_2618455) baseStart_2618455 baseEnd_2618455 := by
    simpa [prefixWord, tailWord_2618455, baseEnd_2618455] using wordTrace_append hprefix tailTrace_2618455
  have hstable : (prefixWord ++ tailWord_2618455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618455).length < 2 ^ (prefixWord ++ tailWord_2618455).sum := by decide
  have hdescent : baseEnd_2618455 < baseStart_2618455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618500 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2618500 : Nat := 118140960795 + 2618500 * 2 ^ 59
def prefixEnd_2618500 : Nat := 4983230072969 + 3 ^ 40 * 2618500 * 2
def baseEnd_2618500 : Nat := 896366062532073560271829

theorem tailTrace_2618500 : CollatzResearch.WordTrace tailWord_2618500 prefixEnd_2618500 896366062532073560271829 := by
  unfold tailWord_2618500
  simp only [CollatzResearch.WordTrace]
  refine ⟨47752270506814589520682477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63669694009086119360909969 47752270506814589520682477)
  ·
    refine ⟨17907101440055471070255929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47752270506814589520682477 17907101440055471070255929)
    ·
      refine ⟨13430326080041603302691947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17907101440055471070255929 13430326080041603302691947)
      ·
        refine ⟨20145489120062404954037921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13430326080041603302691947 20145489120062404954037921)
        ·
          refine ⟨15109116840046803715528441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20145489120062404954037921 15109116840046803715528441)
          ·
            refine ⟨11331837630035102786646331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15109116840046803715528441 11331837630035102786646331)
            ·
              refine ⟨16997756445052654179969497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331837630035102786646331 16997756445052654179969497)
              ·
                refine ⟨12748317333789490634977123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16997756445052654179969497 12748317333789490634977123)
                ·
                  refine ⟨19122476000684235952465685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12748317333789490634977123 19122476000684235952465685)
                  ·
                    refine ⟨896366062532073560271829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19122476000684235952465685 896366062532073560271829)
                    ·
                      rfl

theorem cell22_2618500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2618500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618500 prefixEnd_2618500 := by exact prefixLift 2618500
  have htrace : WordTrace (prefixWord ++ tailWord_2618500) baseStart_2618500 baseEnd_2618500 := by
    simpa [prefixWord, tailWord_2618500, baseEnd_2618500] using wordTrace_append hprefix tailTrace_2618500
  have hstable : (prefixWord ++ tailWord_2618500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618500).length < 2 ^ (prefixWord ++ tailWord_2618500).sum := by decide
  have hdescent : baseEnd_2618500 < baseStart_2618500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618515 : List Nat := [1, 1, 1, 2, 1, 2, 8, 6]
def baseStart_2618515 : Nat := 118140960795 + 2618515 * 2 ^ 59
def prefixEnd_2618515 : Nat := 4983230072969 + 3 ^ 40 * 2618515 * 2
def baseEnd_2618515 : Nat := 99596799704290946794087

theorem tailTrace_2618515 : CollatzResearch.WordTrace tailWord_2618515 prefixEnd_2618515 99596799704290946794087 := by
  unfold tailWord_2618515
  simp only [CollatzResearch.WordTrace]
  refine ⟨95505088108574836603160999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63670058739049891068773999 95505088108574836603160999)
  ·
    refine ⟨143257632162862254904741499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95505088108574836603160999 143257632162862254904741499)
    ·
      refine ⟨214886448244293382357112249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143257632162862254904741499 214886448244293382357112249)
      ·
        refine ⟨161164836183220036767834187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214886448244293382357112249 161164836183220036767834187)
        ·
          refine ⟨241747254274830055151751281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161164836183220036767834187 241747254274830055151751281)
          ·
            refine ⟨181310440706122541363813461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241747254274830055151751281 181310440706122541363813461)
            ·
              refine ⟨2124731727024873531607189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 181310440706122541363813461 2124731727024873531607189)
              ·
                refine ⟨99596799704290946794087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2124731727024873531607189 99596799704290946794087)
                ·
                  rfl

theorem cell22_2618515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 6].length) (baseStart_2618515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618515 prefixEnd_2618515 := by exact prefixLift 2618515
  have htrace : WordTrace (prefixWord ++ tailWord_2618515) baseStart_2618515 baseEnd_2618515 := by
    simpa [prefixWord, tailWord_2618515, baseEnd_2618515] using wordTrace_append hprefix tailTrace_2618515
  have hstable : (prefixWord ++ tailWord_2618515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618515).length < 2 ^ (prefixWord ++ tailWord_2618515).sum := by decide
  have hdescent : baseEnd_2618515 < baseStart_2618515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618547 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 3, 3]
def baseStart_2618547 : Nat := 118140960795 + 2618547 * 2 ^ 59
def prefixEnd_2618547 : Nat := 4983230072969 + 3 ^ 40 * 2618547 * 2
def baseEnd_2618547 : Nat := 896382151592581104346685

theorem tailTrace_2618547 : CollatzResearch.WordTrace tailWord_2618547 prefixEnd_2618547 896382151592581104346685 := by
  unfold tailWord_2618547
  simp only [CollatzResearch.WordTrace]
  refine ⟨95506255244458906068325895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63670836829639270712217263 95506255244458906068325895)
  ·
    refine ⟨143259382866688359102488843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95506255244458906068325895 143259382866688359102488843)
    ·
      refine ⟨214889074300032538653733265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143259382866688359102488843 214889074300032538653733265)
      ·
        refine ⟨161166805725024403990299949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214889074300032538653733265 161166805725024403990299949)
        ·
          refine ⟨60437552146884151496362481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161166805725024403990299949 60437552146884151496362481)
          ·
            refine ⟨45328164110163113622271861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60437552146884151496362481 45328164110163113622271861)
            ·
              refine ⟨4249515385327791902087987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45328164110163113622271861 4249515385327791902087987)
              ·
                refine ⟨6374273077991687853131981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249515385327791902087987 6374273077991687853131981)
                ·
                  refine ⟨2390352404246882944924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6374273077991687853131981 2390352404246882944924493)
                  ·
                    refine ⟨896382151592581104346685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390352404246882944924493 896382151592581104346685)
                    ·
                      rfl

theorem cell22_2618547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].length) (baseStart_2618547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618547 prefixEnd_2618547 := by exact prefixLift 2618547
  have htrace : WordTrace (prefixWord ++ tailWord_2618547) baseStart_2618547 baseEnd_2618547 := by
    simpa [prefixWord, tailWord_2618547, baseEnd_2618547] using wordTrace_append hprefix tailTrace_2618547
  have hstable : (prefixWord ++ tailWord_2618547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618547).length < 2 ^ (prefixWord ++ tailWord_2618547).sum := by decide
  have hdescent : baseEnd_2618547 < baseStart_2618547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618622 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2618622 : Nat := 118140960795 + 2618622 * 2 ^ 59
def prefixEnd_2618622 : Nat := 4983230072969 + 3 ^ 40 * 2618622 * 2
def baseEnd_2618622 : Nat := 298802608541768636240485

theorem tailTrace_2618622 : CollatzResearch.WordTrace tailWord_2618622 prefixEnd_2618622 298802608541768636240485 := by
  unfold tailWord_2618622
  simp only [CollatzResearch.WordTrace]
  refine ⟨11938623839898399234663265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63672660479458129251537413 11938623839898399234663265)
  ·
    refine ⟨8953967879923799425997449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11938623839898399234663265 8953967879923799425997449)
    ·
      refine ⟨6715475909942849569498087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8953967879923799425997449 6715475909942849569498087)
      ·
        refine ⟨10073213864914274354247131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6715475909942849569498087 10073213864914274354247131)
        ·
          refine ⟨15109820797371411531370697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10073213864914274354247131 15109820797371411531370697)
          ·
            refine ⟨11332365598028558648528023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15109820797371411531370697 11332365598028558648528023)
            ·
              refine ⟨16998548397042837972792035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332365598028558648528023 16998548397042837972792035)
              ·
                refine ⟨25497822595564256959188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16998548397042837972792035 25497822595564256959188053)
                ·
                  refine ⟨298802608541768636240485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25497822595564256959188053 298802608541768636240485)
                  ·
                    rfl

theorem cell22_2618622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2618622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618622 prefixEnd_2618622 := by exact prefixLift 2618622
  have htrace : WordTrace (prefixWord ++ tailWord_2618622) baseStart_2618622 baseEnd_2618622 := by
    simpa [prefixWord, tailWord_2618622, baseEnd_2618622] using wordTrace_append hprefix tailTrace_2618622
  have hstable : (prefixWord ++ tailWord_2618622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618622).length < 2 ^ (prefixWord ++ tailWord_2618622).sum := by decide
  have hdescent : baseEnd_2618622 < baseStart_2618622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618652 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2618652 : Nat := 118140960795 + 2618652 * 2 ^ 59
def prefixEnd_2618652 : Nat := 4983230072969 + 3 ^ 40 * 2618652 * 2
def baseEnd_2618652 : Nat := 896418095238395830471363

theorem tailTrace_2618652 : CollatzResearch.WordTrace tailWord_2618652 prefixEnd_2618652 896418095238395830471363 := by
  unfold tailWord_2618652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47755042454539254500449105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63673389939385672667265473 47755042454539254500449105)
  ·
    refine ⟨35816281840904440875336829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47755042454539254500449105 35816281840904440875336829)
    ·
      refine ⟨13431105690339165328251311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35816281840904440875336829 13431105690339165328251311)
      ·
        refine ⟨20146658535508747992376967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13431105690339165328251311 20146658535508747992376967)
        ·
          refine ⟨30219987803263121988565451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20146658535508747992376967 30219987803263121988565451)
          ·
            refine ⟨45329981704894682982848177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30219987803263121988565451 45329981704894682982848177)
            ·
              refine ⟨33997486278671012237136133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45329981704894682982848177 33997486278671012237136133)
              ·
                refine ⟨6374528677250814794463025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33997486278671012237136133 6374528677250814794463025)
                ·
                  refine ⟨4780896507938111095847269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6374528677250814794463025 4780896507938111095847269)
                  ·
                    refine ⟨896418095238395830471363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780896507938111095847269 896418095238395830471363)
                    ·
                      rfl

theorem cell22_2618652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2618652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618652 prefixEnd_2618652 := by exact prefixLift 2618652
  have htrace : WordTrace (prefixWord ++ tailWord_2618652) baseStart_2618652 baseEnd_2618652 := by
    simpa [prefixWord, tailWord_2618652, baseEnd_2618652] using wordTrace_append hprefix tailTrace_2618652
  have hstable : (prefixWord ++ tailWord_2618652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618652).length < 2 ^ (prefixWord ++ tailWord_2618652).sum := by decide
  have hdescent : baseEnd_2618652 < baseStart_2618652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618669 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2618669 : Nat := 118140960795 + 2618669 * 2 ^ 59
def prefixEnd_2618669 : Nat := 4983230072969 + 3 ^ 40 * 2618669 * 2
def baseEnd_2618669 : Nat := 896423914685813452796311

theorem tailTrace_2618669 : CollatzResearch.WordTrace tailWord_2618669 prefixEnd_2618669 896423914685813452796311 := by
  unfold tailWord_2618669
  simp only [CollatzResearch.WordTrace]
  refine ⟨95510704950016920904267061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63673803300011280602844707 95510704950016920904267061)
  ·
    refine ⟨8954128589064086334775037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95510704950016920904267061 8954128589064086334775037)
    ·
      refine ⟨3357798220899032375540639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8954128589064086334775037 3357798220899032375540639)
      ·
        refine ⟨5036697331348548563310959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357798220899032375540639 5036697331348548563310959)
        ·
          refine ⟨7555045997022822844966439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036697331348548563310959 7555045997022822844966439)
          ·
            refine ⟨11332568995534234267449659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555045997022822844966439 11332568995534234267449659)
            ·
              refine ⟨16998853493301351401174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332568995534234267449659 16998853493301351401174489)
              ·
                refine ⟨12749140119976013550880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16998853493301351401174489 12749140119976013550880867)
                ·
                  refine ⟨19123710179964020326321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12749140119976013550880867 19123710179964020326321301)
                  ·
                    refine ⟨896423914685813452796311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19123710179964020326321301 896423914685813452796311)
                    ·
                      rfl

theorem cell22_2618669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2618669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618669 prefixEnd_2618669 := by exact prefixLift 2618669
  have htrace : WordTrace (prefixWord ++ tailWord_2618669) baseStart_2618669 baseEnd_2618669 := by
    simpa [prefixWord, tailWord_2618669, baseEnd_2618669] using wordTrace_append hprefix tailTrace_2618669
  have hstable : (prefixWord ++ tailWord_2618669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618669).length < 2 ^ (prefixWord ++ tailWord_2618669).sum := by decide
  have hdescent : baseEnd_2618669 < baseStart_2618669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618684 : List Nat := [2, 2, 2, 2, 1, 5, 2, 6]
def baseStart_2618684 : Nat := 118140960795 + 2618684 * 2 ^ 59
def prefixEnd_2618684 : Nat := 4983230072969 + 3 ^ 40 * 2618684 * 2
def baseEnd_2618684 : Nat := 99603227721373157074585

theorem tailTrace_2618684 : CollatzResearch.WordTrace tailWord_2618684 prefixEnd_2618684 99603227721373157074585 := by
  unfold tailWord_2618684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47755626022481289233031553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63674168029975052310708737 47755626022481289233031553)
  ·
    refine ⟨35816719516860966924773665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47755626022481289233031553 35816719516860966924773665)
    ·
      refine ⟨26862539637645725193580249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35816719516860966924773665 26862539637645725193580249)
      ·
        refine ⟨20146904728234293895185187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26862539637645725193580249 20146904728234293895185187)
        ·
          refine ⟨30220357092351440842777781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20146904728234293895185187 30220357092351440842777781)
          ·
            refine ⟨2833158477407947579010417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30220357092351440842777781 2833158477407947579010417)
            ·
              refine ⟨2124868858055960684257813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833158477407947579010417 2124868858055960684257813)
              ·
                refine ⟨99603227721373157074585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2124868858055960684257813 99603227721373157074585)
                ·
                  rfl

theorem cell22_2618684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_2618684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618684 prefixEnd_2618684 := by exact prefixLift 2618684
  have htrace : WordTrace (prefixWord ++ tailWord_2618684) baseStart_2618684 baseEnd_2618684 := by
    simpa [prefixWord, tailWord_2618684, baseEnd_2618684] using wordTrace_append hprefix tailTrace_2618684
  have hstable : (prefixWord ++ tailWord_2618684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618684).length < 2 ^ (prefixWord ++ tailWord_2618684).sum := by decide
  have hdescent : baseEnd_2618684 < baseStart_2618684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618701 : List Nat := [1, 6, 1, 3, 1, 2, 8]
def baseStart_2618701 : Nat := 118140960795 + 2618701 * 2 ^ 59
def prefixEnd_2618701 : Nat := 4983230072969 + 3 ^ 40 * 2618701 * 2
def baseEnd_2618701 : Nat := 33201291442213927259119

theorem tailTrace_2618701 : CollatzResearch.WordTrace tailWord_2618701 prefixEnd_2618701 33201291442213927259119 := by
  unfold tailWord_2618701
  simp only [CollatzResearch.WordTrace]
  refine ⟨95511872085900990369431957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63674581390600660246287971 95511872085900990369431957)
  ·
    refine ⟨4477119004026608923567123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95511872085900990369431957 4477119004026608923567123)
    ·
      refine ⟨6715678506039913385350685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477119004026608923567123 6715678506039913385350685)
      ·
        refine ⟨2518379439764967519506507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6715678506039913385350685 2518379439764967519506507)
        ·
          refine ⟨3777569159647451279259761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518379439764967519506507 3777569159647451279259761)
          ·
            refine ⟨2833176869735588459444821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3777569159647451279259761 2833176869735588459444821)
            ·
              refine ⟨33201291442213927259119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2833176869735588459444821 33201291442213927259119)
              ·
                rfl

theorem cell22_2618701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 8].length) (baseStart_2618701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618701 prefixEnd_2618701 := by exact prefixLift 2618701
  have htrace : WordTrace (prefixWord ++ tailWord_2618701) baseStart_2618701 baseEnd_2618701 := by
    simpa [prefixWord, tailWord_2618701, baseEnd_2618701] using wordTrace_append hprefix tailTrace_2618701
  have hstable : (prefixWord ++ tailWord_2618701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618701).length < 2 ^ (prefixWord ++ tailWord_2618701).sum := by decide
  have hdescent : baseEnd_2618701 < baseStart_2618701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618712 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_2618712 : Nat := 118140960795 + 2618712 * 2 ^ 59
def prefixEnd_2618712 : Nat := 4983230072969 + 3 ^ 40 * 2618712 * 2
def baseEnd_2618712 : Nat := 298812878154858557990393

theorem tailTrace_2618712 : CollatzResearch.WordTrace tailWord_2618712 prefixEnd_2618712 298812878154858557990393 := by
  unfold tailWord_2618712
  simp only [CollatzResearch.WordTrace]
  refine ⟨47756136644430569624041195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63674848859240759498721593 47756136644430569624041195)
  ·
    refine ⟨71634204966645854436061793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47756136644430569624041195 71634204966645854436061793)
    ·
      refine ⟨53725653724984390827046345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71634204966645854436061793 53725653724984390827046345)
      ·
        refine ⟨40294240293738293120284759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53725653724984390827046345 40294240293738293120284759)
        ·
          refine ⟨60441360440607439680427139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40294240293738293120284759 60441360440607439680427139)
          ·
            refine ⟨90662040660911159520640709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60441360440607439680427139 90662040660911159520640709)
            ·
              refine ⟨16999132623920842410120133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90662040660911159520640709 16999132623920842410120133)
              ·
                refine ⟨3187337366985157951897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16999132623920842410120133 3187337366985157951897525)
                ·
                  refine ⟨298812878154858557990393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3187337366985157951897525 298812878154858557990393)
                  ·
                    rfl

theorem cell22_2618712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_2618712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618712 prefixEnd_2618712 := by exact prefixLift 2618712
  have htrace : WordTrace (prefixWord ++ tailWord_2618712) baseStart_2618712 baseEnd_2618712 := by
    simpa [prefixWord, tailWord_2618712, baseEnd_2618712] using wordTrace_append hprefix tailTrace_2618712
  have hstable : (prefixWord ++ tailWord_2618712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618712).length < 2 ^ (prefixWord ++ tailWord_2618712).sum := by decide
  have hdescent : baseEnd_2618712 < baseStart_2618712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618787 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_2618787 : Nat := 118140960795 + 2618787 * 2 ^ 59
def prefixEnd_2618787 : Nat := 4983230072969 + 3 ^ 40 * 2618787 * 2
def baseEnd_2618787 : Nat := 896464308497300478345949

theorem tailTrace_2618787 : CollatzResearch.WordTrace tailWord_2618787 prefixEnd_2618787 896464308497300478345949 := by
  unfold tailWord_2618787
  simp only [CollatzResearch.WordTrace]
  refine ⟨95515008763589427057062615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63676672509059618038041743 95515008763589427057062615)
  ·
    refine ⟨143272513145384140585593923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95515008763589427057062615 143272513145384140585593923)
    ·
      refine ⟨214908769718076210878390885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143272513145384140585593923 214908769718076210878390885)
      ·
        refine ⟨40295394322139289539698291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214908769718076210878390885 40295394322139289539698291)
        ·
          refine ⟨60443091483208934309547437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40295394322139289539698291 60443091483208934309547437)
          ·
            refine ⟨22666159306203350366080289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60443091483208934309547437 22666159306203350366080289)
            ·
              refine ⟨16999619479652512774560217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22666159306203350366080289 16999619479652512774560217)
              ·
                refine ⟨12749714609739384580920163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16999619479652512774560217 12749714609739384580920163)
                ·
                  refine ⟨19124571914609076871380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12749714609739384580920163 19124571914609076871380245)
                  ·
                    refine ⟨896464308497300478345949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19124571914609076871380245 896464308497300478345949)
                    ·
                      rfl

theorem cell22_2618787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_2618787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618787 prefixEnd_2618787 := by exact prefixLift 2618787
  have htrace : WordTrace (prefixWord ++ tailWord_2618787) baseStart_2618787 baseEnd_2618787 := by
    simpa [prefixWord, tailWord_2618787, baseEnd_2618787] using wordTrace_append hprefix tailTrace_2618787
  have hstable : (prefixWord ++ tailWord_2618787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618787).length < 2 ^ (prefixWord ++ tailWord_2618787).sum := by decide
  have hdescent : baseEnd_2618787 < baseStart_2618787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618851 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 3, 3]
def baseStart_2618851 : Nat := 118140960795 + 2618851 * 2 ^ 59
def prefixEnd_2618851 : Nat := 4983230072969 + 3 ^ 40 * 2618851 * 2
def baseEnd_2618851 : Nat := 896486217005225644745753

theorem tailTrace_2618851 : CollatzResearch.WordTrace tailWord_2618851 prefixEnd_2618851 896486217005225644745753 := by
  unfold tailWord_2618851
  simp only [CollatzResearch.WordTrace]
  refine ⟨95517343035357565987392407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63678228690238377324928271 95517343035357565987392407)
  ·
    refine ⟨143276014553036348981088611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95517343035357565987392407 143276014553036348981088611)
    ·
      refine ⟨214914021829554523471632917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143276014553036348981088611 214914021829554523471632917)
      ·
        refine ⟨10074094773260368287732793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214914021829554523471632917 10074094773260368287732793)
        ·
          refine ⟨7555571079945276215799595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10074094773260368287732793 7555571079945276215799595)
          ·
            refine ⟨11333356619917914323699393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555571079945276215799595 11333356619917914323699393)
            ·
              refine ⟨8500017464938435742774545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11333356619917914323699393 8500017464938435742774545)
              ·
                refine ⟨6375013098703826807080909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500017464938435742774545 6375013098703826807080909)
                ·
                  refine ⟨2390629912013935052655341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6375013098703826807080909 2390629912013935052655341)
                  ·
                    refine ⟨896486217005225644745753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390629912013935052655341 896486217005225644745753)
                    ·
                      rfl

theorem cell22_2618851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].length) (baseStart_2618851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618851 prefixEnd_2618851 := by exact prefixLift 2618851
  have htrace : WordTrace (prefixWord ++ tailWord_2618851) baseStart_2618851 baseEnd_2618851 := by
    simpa [prefixWord, tailWord_2618851, baseEnd_2618851] using wordTrace_append hprefix tailTrace_2618851
  have hstable : (prefixWord ++ tailWord_2618851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618851).length < 2 ^ (prefixWord ++ tailWord_2618851).sum := by decide
  have hdescent : baseEnd_2618851 < baseStart_2618851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618909 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2618909 : Nat := 118140960795 + 2618909 * 2 ^ 59
def prefixEnd_2618909 : Nat := 4983230072969 + 3 ^ 40 * 2618909 * 2
def baseEnd_2618909 : Nat := 298835357196844275598525

theorem tailTrace_2618909 : CollatzResearch.WordTrace tailWord_2618909 prefixEnd_2618909 298835357196844275598525 := by
  unfold tailWord_2618909
  simp only [CollatzResearch.WordTrace]
  refine ⟨95519458469147441893003781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63679638979431627928669187 95519458469147441893003781)
  ·
    refine ⟨17909898462965145354938209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95519458469147441893003781 17909898462965145354938209)
    ·
      refine ⟨13432423847223859016203657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17909898462965145354938209 13432423847223859016203657)
      ·
        refine ⟨10074317885417894262152743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13432423847223859016203657 10074317885417894262152743)
        ·
          refine ⟨15111476828126841393229115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074317885417894262152743 15111476828126841393229115)
          ·
            refine ⟨22667215242190262089843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15111476828126841393229115 22667215242190262089843673)
            ·
              refine ⟨17000411431642696567382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22667215242190262089843673 17000411431642696567382755)
              ·
                refine ⟨25500617147464044851074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17000411431642696567382755 25500617147464044851074133)
                ·
                  refine ⟨298835357196844275598525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25500617147464044851074133 298835357196844275598525)
                  ·
                    rfl

theorem cell22_2618909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2618909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618909 prefixEnd_2618909 := by exact prefixLift 2618909
  have htrace : WordTrace (prefixWord ++ tailWord_2618909) baseStart_2618909 baseEnd_2618909 := by
    simpa [prefixWord, tailWord_2618909, baseEnd_2618909] using wordTrace_append hprefix tailTrace_2618909
  have hstable : (prefixWord ++ tailWord_2618909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618909).length < 2 ^ (prefixWord ++ tailWord_2618909).sum := by decide
  have hdescent : baseEnd_2618909 < baseStart_2618909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618911 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 1, 4]
def baseStart_2618911 : Nat := 118140960795 + 2618911 * 2 ^ 59
def prefixEnd_2618911 : Nat := 4983230072969 + 3 ^ 40 * 2618911 * 2
def baseEnd_2618911 : Nat := 896506756231405488245569

theorem tailTrace_2618911 : CollatzResearch.WordTrace tailWord_2618911 prefixEnd_2618911 896506756231405488245569 := by
  unfold tailWord_2618911
  simp only [CollatzResearch.WordTrace]
  refine ⟨95519531415140196234576587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63679687610093464156384391 95519531415140196234576587)
  ·
    refine ⟨143279297122710294351864881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95519531415140196234576587 143279297122710294351864881)
    ·
      refine ⟨107459472842032720763898661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143279297122710294351864881 107459472842032720763898661)
      ·
        refine ⟨20148651157881135143230999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107459472842032720763898661 20148651157881135143230999)
        ·
          refine ⟨30222976736821702714846499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20148651157881135143230999 30222976736821702714846499)
          ·
            refine ⟨45334465105232554072269749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30222976736821702714846499 45334465105232554072269749)
            ·
              refine ⟨4250106103615551944275289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45334465105232554072269749 4250106103615551944275289)
              ·
                refine ⟨3187579577711663958206467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4250106103615551944275289 3187579577711663958206467)
                ·
                  refine ⟨4781369366567495937309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187579577711663958206467 4781369366567495937309701)
                  ·
                    refine ⟨896506756231405488245569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4781369366567495937309701 896506756231405488245569)
                    ·
                      rfl

theorem cell22_2618911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_2618911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618911 prefixEnd_2618911 := by exact prefixLift 2618911
  have htrace : WordTrace (prefixWord ++ tailWord_2618911) baseStart_2618911 baseEnd_2618911 := by
    simpa [prefixWord, tailWord_2618911, baseEnd_2618911] using wordTrace_append hprefix tailTrace_2618911
  have hstable : (prefixWord ++ tailWord_2618911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618911).length < 2 ^ (prefixWord ++ tailWord_2618911).sum := by decide
  have hdescent : baseEnd_2618911 < baseStart_2618911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618943 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 4]
def baseStart_2618943 : Nat := 118140960795 + 2618943 * 2 ^ 59
def prefixEnd_2618943 : Nat := 4983230072969 + 3 ^ 40 * 2618943 * 2
def baseEnd_2618943 : Nat := 298839236828456023815157

theorem tailTrace_2618943 : CollatzResearch.WordTrace tailWord_2618943 prefixEnd_2618943 298839236828456023815157 := by
  unfold tailWord_2618943
  simp only [CollatzResearch.WordTrace]
  refine ⟨95520698551024265699741483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63680465700682843799827655 95520698551024265699741483)
  ·
    refine ⟨143281047826536398549612225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95520698551024265699741483 143281047826536398549612225)
    ·
      refine ⟨107460785869902298912209169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143281047826536398549612225 107460785869902298912209169)
      ·
        refine ⟨80595589402426724184156877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107460785869902298912209169 80595589402426724184156877)
        ·
          refine ⟨30223346025910021569058829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80595589402426724184156877 30223346025910021569058829)
          ·
            refine ⟨11333754759716258088397061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30223346025910021569058829 11333754759716258088397061)
            ·
              refine ⟨2125079017446798391574449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11333754759716258088397061 2125079017446798391574449)
              ·
                refine ⟨1593809263085098793680837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125079017446798391574449 1593809263085098793680837)
                ·
                  refine ⟨298839236828456023815157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593809263085098793680837 298839236828456023815157)
                  ·
                    rfl

theorem cell22_2618943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 4].length) (baseStart_2618943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2618943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2618943 prefixEnd_2618943 := by exact prefixLift 2618943
  have htrace : WordTrace (prefixWord ++ tailWord_2618943) baseStart_2618943 baseEnd_2618943 := by
    simpa [prefixWord, tailWord_2618943, baseEnd_2618943] using wordTrace_append hprefix tailTrace_2618943
  have hstable : (prefixWord ++ tailWord_2618943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618943).length < 2 ^ (prefixWord ++ tailWord_2618943).sum := by decide
  have hdescent : baseEnd_2618943 < baseStart_2618943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619003 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 1, 3]
def baseStart_2619003 : Nat := 118140960795 + 2619003 * 2 ^ 59
def prefixEnd_2619003 : Nat := 4983230072969 + 3 ^ 40 * 2619003 * 2
def baseEnd_2619003 : Nat := 896538249711547914945287

theorem tailTrace_2619003 : CollatzResearch.WordTrace tailWord_2619003 prefixEnd_2619003 896538249711547914945287 := by
  unfold tailWord_2619003
  simp only [CollatzResearch.WordTrace]
  refine ⟨95522886930806895946925663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63681924620537930631283775 95522886930806895946925663)
  ·
    refine ⟨143284330396210343920388495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95522886930806895946925663 143284330396210343920388495)
    ·
      refine ⟨214926495594315515880582743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143284330396210343920388495 214926495594315515880582743)
      ·
        refine ⟨322389743391473273820874115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214926495594315515880582743 322389743391473273820874115)
        ·
          refine ⟨483584615087209910731311173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322389743391473273820874115 483584615087209910731311173)
          ·
            refine ⟨90672115328851858262120845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 483584615087209910731311173 90672115328851858262120845)
            ·
              refine ⟨34002043248319446848295317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90672115328851858262120845 34002043248319446848295317)
              ·
                refine ⟨1593845777264974071013843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34002043248319446848295317 1593845777264974071013843)
                ·
                  refine ⟨2390768665897461106520765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593845777264974071013843 2390768665897461106520765)
                  ·
                    refine ⟨896538249711547914945287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390768665897461106520765 896538249711547914945287)
                    ·
                      rfl

theorem cell22_2619003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 3].length) (baseStart_2619003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619003 prefixEnd_2619003 := by exact prefixLift 2619003
  have htrace : WordTrace (prefixWord ++ tailWord_2619003) baseStart_2619003 baseEnd_2619003 := by
    simpa [prefixWord, tailWord_2619003, baseEnd_2619003] using wordTrace_append hprefix tailTrace_2619003
  have hstable : (prefixWord ++ tailWord_2619003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619003).length < 2 ^ (prefixWord ++ tailWord_2619003).sum := by decide
  have hdescent : baseEnd_2619003 < baseStart_2619003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619029 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2619029 : Nat := 118140960795 + 2619029 * 2 ^ 59
def prefixEnd_2619029 : Nat := 4983230072969 + 3 ^ 40 * 2619029 * 2
def baseEnd_2619029 : Nat := 896547150042892513795207

theorem tailTrace_2619029 : CollatzResearch.WordTrace tailWord_2619029 prefixEnd_2619029 896547150042892513795207 := by
  unfold tailWord_2619029
  simp only [CollatzResearch.WordTrace]
  refine ⟨95523835228712702387372141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63682556819141801591581427 95523835228712702387372141)
  ·
    refine ⟨35821438210767263395264553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95523835228712702387372141 35821438210767263395264553)
    ·
      refine ⟨26866078658075447546448415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35821438210767263395264553 26866078658075447546448415)
      ·
        refine ⟨40299117987113171319672623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26866078658075447546448415 40299117987113171319672623)
        ·
          refine ⟨60448676980669756979508935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40299117987113171319672623 60448676980669756979508935)
          ·
            refine ⟨90673015471004635469263403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60448676980669756979508935 90673015471004635469263403)
            ·
              refine ⟨136009523206506953203895105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90673015471004635469263403 136009523206506953203895105)
              ·
                refine ⟨102007142404880214902921329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136009523206506953203895105 102007142404880214902921329)
                ·
                  refine ⟨76505356803660161177190997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102007142404880214902921329 76505356803660161177190997)
                  ·
                    refine ⟨896547150042892513795207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76505356803660161177190997 896547150042892513795207)
                    ·
                      rfl

theorem cell22_2619029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2619029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619029 prefixEnd_2619029 := by exact prefixLift 2619029
  have htrace : WordTrace (prefixWord ++ tailWord_2619029) baseStart_2619029 baseEnd_2619029 := by
    simpa [prefixWord, tailWord_2619029, baseEnd_2619029] using wordTrace_append hprefix tailTrace_2619029
  have hstable : (prefixWord ++ tailWord_2619029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619029).length < 2 ^ (prefixWord ++ tailWord_2619029).sum := by decide
  have hdescent : baseEnd_2619029 < baseStart_2619029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619054 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2619054 : Nat := 118140960795 + 2619054 * 2 ^ 59
def prefixEnd_2619054 : Nat := 4983230072969 + 3 ^ 40 * 2619054 * 2
def baseEnd_2619054 : Nat := 896555708053800781920131

theorem tailTrace_2619054 : CollatzResearch.WordTrace tailWord_2619054 prefixEnd_2619054 896555708053800781920131 := by
  unfold tailWord_2619054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940593381702766457129027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63683164702414754438021477 11940593381702766457129027)
  ·
    refine ⟨17910890072554149685693541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11940593381702766457129027 17910890072554149685693541)
    ·
      refine ⟨3358291888603903066067539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17910890072554149685693541 3358291888603903066067539)
      ·
        refine ⟨5037437832905854599101309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358291888603903066067539 5037437832905854599101309)
        ·
          refine ⟨1889039187339695474662991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5037437832905854599101309 1889039187339695474662991)
          ·
            refine ⟨2833558781009543211994487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889039187339695474662991 2833558781009543211994487)
            ·
              refine ⟨4250338171514314817991731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833558781009543211994487 4250338171514314817991731)
              ·
                refine ⟨6375507257271472226987597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4250338171514314817991731 6375507257271472226987597)
                ·
                  refine ⟨2390815221476802085120349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6375507257271472226987597 2390815221476802085120349)
                  ·
                    refine ⟨896555708053800781920131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390815221476802085120349 896555708053800781920131)
                    ·
                      rfl

theorem cell22_2619054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2619054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619054 prefixEnd_2619054 := by exact prefixLift 2619054
  have htrace : WordTrace (prefixWord ++ tailWord_2619054) baseStart_2619054 baseEnd_2619054 := by
    simpa [prefixWord, tailWord_2619054, baseEnd_2619054] using wordTrace_append hprefix tailTrace_2619054
  have hstable : (prefixWord ++ tailWord_2619054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619054).length < 2 ^ (prefixWord ++ tailWord_2619054).sum := by decide
  have hdescent : baseEnd_2619054 < baseStart_2619054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619112 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_2619112 : Nat := 118140960795 + 2619112 * 2 ^ 59
def prefixEnd_2619112 : Nat := 4983230072969 + 3 ^ 40 * 2619112 * 2
def baseEnd_2619112 : Nat := 298858520879702654656651

theorem tailTrace_2619112 : CollatzResearch.WordTrace tailWord_2619112 prefixEnd_2619112 298858520879702654656651 := by
  unfold tailWord_2619112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47763431243706003781321795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63684574991608005041762393 47763431243706003781321795)
  ·
    refine ⟨71645146865559005671982693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47763431243706003781321795 71645146865559005671982693)
    ·
      refine ⟨13433465037292313563496755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71645146865559005671982693 13433465037292313563496755)
      ·
        refine ⟨20150197555938470345245133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13433465037292313563496755 20150197555938470345245133)
        ·
          refine ⟨7556324083476926379466925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20150197555938470345245133 7556324083476926379466925)
          ·
            refine ⟨2833621531303847392300097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7556324083476926379466925 2833621531303847392300097)
            ·
              refine ⟨2125216148477885544225073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833621531303847392300097 2125216148477885544225073)
              ·
                refine ⟨1593912111358414158168805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125216148477885544225073 1593912111358414158168805)
                ·
                  refine ⟨298858520879702654656651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1593912111358414158168805 298858520879702654656651)
                  ·
                    rfl

theorem cell22_2619112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_2619112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619112 prefixEnd_2619112 := by exact prefixLift 2619112
  have htrace : WordTrace (prefixWord ++ tailWord_2619112) baseStart_2619112 baseEnd_2619112 := by
    simpa [prefixWord, tailWord_2619112, baseEnd_2619112] using wordTrace_append hprefix tailTrace_2619112
  have hstable : (prefixWord ++ tailWord_2619112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619112).length < 2 ^ (prefixWord ++ tailWord_2619112).sum := by decide
  have hdescent : baseEnd_2619112 < baseStart_2619112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619172 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_2619172 : Nat := 118140960795 + 2619172 * 2 ^ 59
def prefixEnd_2619172 : Nat := 4983230072969 + 3 ^ 40 * 2619172 * 2
def baseEnd_2619172 : Nat := 896596101865287807469769

theorem tailTrace_2619172 : CollatzResearch.WordTrace tailWord_2619172 prefixEnd_2619172 896596101865287807469769 := by
  unfold tailWord_2619172
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764525433597318904913885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63686033911463091873218513 47764525433597318904913885)
  ·
    refine ⟨17911697037598994589342707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47764525433597318904913885 17911697037598994589342707)
    ·
      refine ⟨26867545556398491884014061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911697037598994589342707 26867545556398491884014061)
      ·
        refine ⟨10075329583649434456505273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26867545556398491884014061 10075329583649434456505273)
        ·
          refine ⟨7556497187737075842378955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10075329583649434456505273 7556497187737075842378955)
          ·
            refine ⟨11334745781605613763568433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556497187737075842378955 11334745781605613763568433)
            ·
              refine ⟨8501059336204210322676325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11334745781605613763568433 8501059336204210322676325)
              ·
                refine ⟨1593948625538289435501811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8501059336204210322676325 1593948625538289435501811)
                ·
                  refine ⟨2390922938307434153252717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593948625538289435501811 2390922938307434153252717)
                  ·
                    refine ⟨896596101865287807469769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390922938307434153252717 896596101865287807469769)
                    ·
                      rfl

theorem cell22_2619172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_2619172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619172 prefixEnd_2619172 := by exact prefixLift 2619172
  have htrace : WordTrace (prefixWord ++ tailWord_2619172) baseStart_2619172 baseEnd_2619172 := by
    simpa [prefixWord, tailWord_2619172, baseEnd_2619172] using wordTrace_append hprefix tailTrace_2619172
  have hstable : (prefixWord ++ tailWord_2619172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619172).length < 2 ^ (prefixWord ++ tailWord_2619172).sum := by decide
  have hdescent : baseEnd_2619172 < baseStart_2619172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619185 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 5]
def baseStart_2619185 : Nat := 118140960795 + 2619185 * 2 ^ 59
def prefixEnd_2619185 : Nat := 4983230072969 + 3 ^ 40 * 2619185 * 2
def baseEnd_2619185 : Nat := 298866850676986702298243

theorem tailTrace_2619185 : CollatzResearch.WordTrace tailWord_2619185 prefixEnd_2619185 298866850676986702298243 := by
  unfold tailWord_2619185
  simp only [CollatzResearch.WordTrace]
  refine ⟨95529525016147541030051009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63686350010765027353367339 95529525016147541030051009)
  ·
    refine ⟨71647143762110655772538257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95529525016147541030051009 71647143762110655772538257)
    ·
      refine ⟨53735357821582991829403693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71647143762110655772538257 53735357821582991829403693)
      ·
        refine ⟨20150759183093621936026385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53735357821582991829403693 20150759183093621936026385)
        ·
          refine ⟨15113069387320216452019789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20150759183093621936026385 15113069387320216452019789)
          ·
            refine ⟨5667401020245081169507421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15113069387320216452019789 5667401020245081169507421)
            ·
              refine ⟨2125275382591905438565283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5667401020245081169507421 2125275382591905438565283)
              ·
                refine ⟨3187913073887858157847925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125275382591905438565283 3187913073887858157847925)
                ·
                  refine ⟨298866850676986702298243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3187913073887858157847925 298866850676986702298243)
                  ·
                    rfl

theorem cell22_2619185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_2619185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619185 prefixEnd_2619185 := by exact prefixLift 2619185
  have htrace : WordTrace (prefixWord ++ tailWord_2619185) baseStart_2619185 baseEnd_2619185 := by
    simpa [prefixWord, tailWord_2619185, baseEnd_2619185] using wordTrace_append hprefix tailTrace_2619185
  have hstable : (prefixWord ++ tailWord_2619185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619185).length < 2 ^ (prefixWord ++ tailWord_2619185).sum := by decide
  have hdescent : baseEnd_2619185 < baseStart_2619185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619206 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2619206 : Nat := 118140960795 + 2619206 * 2 ^ 59
def prefixEnd_2619206 : Nat := 4983230072969 + 3 ^ 40 * 2619206 * 2
def baseEnd_2619206 : Nat := 896607740760123052119665

theorem tailTrace_2619206 : CollatzResearch.WordTrace tailWord_2619206 prefixEnd_2619206 896607740760123052119665 := by
  unfold tailWord_2619206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985321592158483175517671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63686860632714307744376981 2985321592158483175517671)
  ·
    refine ⟨4477982388237724763276507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2985321592158483175517671 4477982388237724763276507)
    ·
      refine ⟨6716973582356587144914761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477982388237724763276507 6716973582356587144914761)
      ·
        refine ⟨5037730186767440358686071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6716973582356587144914761 5037730186767440358686071)
        ·
          refine ⟨7556595280151160538029107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037730186767440358686071 7556595280151160538029107)
          ·
            refine ⟨11334892920226740807043661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556595280151160538029107 11334892920226740807043661)
            ·
              refine ⟨4250584845085027802641373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11334892920226740807043661 4250584845085027802641373)
              ·
                refine ⟨1593969316906885425990515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250584845085027802641373 1593969316906885425990515)
                ·
                  refine ⟨2390953975360328138985773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593969316906885425990515 2390953975360328138985773)
                  ·
                    refine ⟨896607740760123052119665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2390953975360328138985773 896607740760123052119665)
                    ·
                      rfl

theorem cell22_2619206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2619206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619206 prefixEnd_2619206 := by exact prefixLift 2619206
  have htrace : WordTrace (prefixWord ++ tailWord_2619206) baseStart_2619206 baseEnd_2619206 := by
    simpa [prefixWord, tailWord_2619206, baseEnd_2619206] using wordTrace_append hprefix tailTrace_2619206
  have hstable : (prefixWord ++ tailWord_2619206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619206).length < 2 ^ (prefixWord ++ tailWord_2619206).sum := by decide
  have hdescent : baseEnd_2619206 < baseStart_2619206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619262 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2619262 : Nat := 118140960795 + 2619262 * 2 ^ 59
def prefixEnd_2619262 : Nat := 4983230072969 + 3 ^ 40 * 2619262 * 2
def baseEnd_2619262 : Nat := 896626910704557572719493

theorem tailTrace_2619262 : CollatzResearch.WordTrace tailWord_2619262 prefixEnd_2619262 896626910704557572719493 := by
  unfold tailWord_2619262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941541679608572897575505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63688222291245722120402693 11941541679608572897575505)
  ·
    refine ⟨8956156259706429673181629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11941541679608572897575505 8956156259706429673181629)
    ·
      refine ⟨3358558597389911127443111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8956156259706429673181629 3358558597389911127443111)
      ·
        refine ⟨5037837896084866691164667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358558597389911127443111 5037837896084866691164667)
        ·
          refine ⟨7556756844127300036747001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037837896084866691164667 7556756844127300036747001)
          ·
            refine ⟨5667567633095475027560251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7556756844127300036747001 5667567633095475027560251)
            ·
              refine ⟨8501351449643212541340377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667567633095475027560251 8501351449643212541340377)
              ·
                refine ⟨6376013587232409406005283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8501351449643212541340377 6376013587232409406005283)
                ·
                  refine ⟨9564020380848614109007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6376013587232409406005283 9564020380848614109007925)
                  ·
                    refine ⟨896626910704557572719493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9564020380848614109007925 896626910704557572719493)
                    ·
                      rfl

theorem cell22_2619262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2619262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619262 prefixEnd_2619262 := by exact prefixLift 2619262
  have htrace : WordTrace (prefixWord ++ tailWord_2619262) baseStart_2619262 baseEnd_2619262 := by
    simpa [prefixWord, tailWord_2619262, baseEnd_2619262] using wordTrace_append hprefix tailTrace_2619262
  have hstable : (prefixWord ++ tailWord_2619262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619262).length < 2 ^ (prefixWord ++ tailWord_2619262).sum := by decide
  have hdescent : baseEnd_2619262 < baseStart_2619262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_2619333 : Nat := 118140960795 + 2619333 * 2 ^ 59
def prefixEnd_2619333 : Nat := 4983230072969 + 3 ^ 40 * 2619333 * 2
def baseEnd_2619333 : Nat := 896651215455537054194275

theorem tailTrace_2619333 : CollatzResearch.WordTrace tailWord_2619333 prefixEnd_2619333 896651215455537054194275 := by
  unfold tailWord_2619333
  simp only [CollatzResearch.WordTrace]
  refine ⟨95534923019611362306438653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63689948679740908204292435 95534923019611362306438653)
  ·
    refine ⟨35825596132354260864914495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95534923019611362306438653 35825596132354260864914495)
    ·
      refine ⟨53738394198531391297371743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35825596132354260864914495 53738394198531391297371743)
      ·
        refine ⟨80607591297797086946057615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53738394198531391297371743 80607591297797086946057615)
        ·
          refine ⟨120911386946695630419086423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80607591297797086946057615 120911386946695630419086423)
          ·
            refine ⟨181367080420043445628629635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120911386946695630419086423 181367080420043445628629635)
            ·
              refine ⟨272050620630065168442944453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181367080420043445628629635 272050620630065168442944453)
              ·
                refine ⟨51009491368137219083052085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272050620630065168442944453 51009491368137219083052085)
                ·
                  refine ⟨4782139815762864289036133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51009491368137219083052085 4782139815762864289036133)
                  ·
                    refine ⟨896651215455537054194275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4782139815762864289036133 896651215455537054194275)
                    ·
                      rfl

theorem cell22_2619333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_2619333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619333 prefixEnd_2619333 := by exact prefixLift 2619333
  have htrace : WordTrace (prefixWord ++ tailWord_2619333) baseStart_2619333 baseEnd_2619333 := by
    simpa [prefixWord, tailWord_2619333, baseEnd_2619333] using wordTrace_append hprefix tailTrace_2619333
  have hstable : (prefixWord ++ tailWord_2619333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619333).length < 2 ^ (prefixWord ++ tailWord_2619333).sum := by decide
  have hdescent : baseEnd_2619333 < baseStart_2619333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619399 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 4]
def baseStart_2619399 : Nat := 118140960795 + 2619399 * 2 ^ 59
def prefixEnd_2619399 : Nat := 4983230072969 + 3 ^ 40 * 2619399 * 2
def baseEnd_2619399 : Nat := 298891269534778294014691

theorem tailTrace_2619399 : CollatzResearch.WordTrace tailWord_2619399 prefixEnd_2619399 298891269534778294014691 := by
  unfold tailWord_2619399
  simp only [CollatzResearch.WordTrace]
  refine ⟨95537330237372255578341251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63691553491581503718894167 95537330237372255578341251)
  ·
    refine ⟨143305995356058383367511877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95537330237372255578341251 143305995356058383367511877)
    ·
      refine ⟨26869874129260946881408477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143305995356058383367511877 26869874129260946881408477)
      ·
        refine ⟨10076202798472855080528179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26869874129260946881408477 10076202798472855080528179)
        ·
          refine ⟨15114304197709282620792269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10076202798472855080528179 15114304197709282620792269)
          ·
            refine ⟨5667864074140980982797101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15114304197709282620792269 5667864074140980982797101)
            ·
              refine ⟨2125449027802867868548913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5667864074140980982797101 2125449027802867868548913)
              ·
                refine ⟨1594086770852150901411685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125449027802867868548913 1594086770852150901411685)
                ·
                  refine ⟨298891269534778294014691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594086770852150901411685 298891269534778294014691)
                  ·
                    rfl

theorem cell22_2619399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 4].length) (baseStart_2619399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619399 prefixEnd_2619399 := by exact prefixLift 2619399
  have htrace : WordTrace (prefixWord ++ tailWord_2619399) baseStart_2619399 baseEnd_2619399 := by
    simpa [prefixWord, tailWord_2619399, baseEnd_2619399] using wordTrace_append hprefix tailTrace_2619399
  have hstable : (prefixWord ++ tailWord_2619399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619399).length < 2 ^ (prefixWord ++ tailWord_2619399).sum := by decide
  have hdescent : baseEnd_2619399 < baseStart_2619399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619405 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2619405 : Nat := 118140960795 + 2619405 * 2 ^ 59
def prefixEnd_2619405 : Nat := 4983230072969 + 3 ^ 40 * 2619405 * 2
def baseEnd_2619405 : Nat := 298891954175650955464685

theorem tailTrace_2619405 : CollatzResearch.WordTrace tailWord_2619405 prefixEnd_2619405 298891954175650955464685 := by
  unfold tailWord_2619405
  simp only [CollatzResearch.WordTrace]
  refine ⟨95537549075350518603059669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63691699383567012402039779 95537549075350518603059669)
  ·
    refine ⟨2239161306453527779759211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 95537549075350518603059669 2239161306453527779759211)
    ·
      refine ⟨3358741959680291669638817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239161306453527779759211 3358741959680291669638817)
      ·
        refine ⟨2519056469760218752229113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3358741959680291669638817 2519056469760218752229113)
        ·
          refine ⟨1889292352320164064171835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2519056469760218752229113 1889292352320164064171835)
          ·
            refine ⟨2833938528480246096257753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889292352320164064171835 2833938528480246096257753)
            ·
              refine ⟨2125453896360184572193315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833938528480246096257753 2125453896360184572193315)
              ·
                refine ⟨3188180844540276858289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125453896360184572193315 3188180844540276858289973)
                ·
                  refine ⟨298891954175650955464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188180844540276858289973 298891954175650955464685)
                  ·
                    rfl

theorem cell22_2619405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2619405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619405 prefixEnd_2619405 := by exact prefixLift 2619405
  have htrace : WordTrace (prefixWord ++ tailWord_2619405) baseStart_2619405 baseEnd_2619405 := by
    simpa [prefixWord, tailWord_2619405, baseEnd_2619405] using wordTrace_append hprefix tailTrace_2619405
  have hstable : (prefixWord ++ tailWord_2619405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619405).length < 2 ^ (prefixWord ++ tailWord_2619405).sum := by decide
  have hdescent : baseEnd_2619405 < baseStart_2619405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619455 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 5]
def baseStart_2619455 : Nat := 118140960795 + 2619455 * 2 ^ 59
def prefixEnd_2619455 : Nat := 4983230072969 + 3 ^ 40 * 2619455 * 2
def baseEnd_2619455 : Nat := 298897659516256467547967

theorem tailTrace_2619455 : CollatzResearch.WordTrace tailWord_2619455 prefixEnd_2619455 298897659516256467547967 := by
  unfold tailWord_2619455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95539372725169377142379819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63692915150112918094919879 95539372725169377142379819)
  ·
    refine ⟨143309059087754065713569729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95539372725169377142379819 143309059087754065713569729)
    ·
      refine ⟨107481794315815549285177297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143309059087754065713569729 107481794315815549285177297)
      ·
        refine ⟨80611345736861661963882973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107481794315815549285177297 80611345736861661963882973)
        ·
          refine ⟨30229254651323123236456115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80611345736861661963882973 30229254651323123236456115)
          ·
            refine ⟨45343881976984684854684173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30229254651323123236456115 45343881976984684854684173)
            ·
              refine ⟨17003955741369256820506565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45343881976984684854684173 17003955741369256820506565)
              ·
                refine ⟨3188241701506735653844981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17003955741369256820506565 3188241701506735653844981)
                ·
                  refine ⟨298897659516256467547967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188241701506735653844981 298897659516256467547967)
                  ·
                    rfl

theorem cell22_2619455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].length) (baseStart_2619455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619455 prefixEnd_2619455 := by exact prefixLift 2619455
  have htrace : WordTrace (prefixWord ++ tailWord_2619455) baseStart_2619455 baseEnd_2619455 := by
    simpa [prefixWord, tailWord_2619455, baseEnd_2619455] using wordTrace_append hprefix tailTrace_2619455
  have hstable : (prefixWord ++ tailWord_2619455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619455).length < 2 ^ (prefixWord ++ tailWord_2619455).sum := by decide
  have hdescent : baseEnd_2619455 < baseStart_2619455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619470 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2619470 : Nat := 118140960795 + 2619470 * 2 ^ 59
def prefixEnd_2619470 : Nat := 4983230072969 + 3 ^ 40 * 2619470 * 2
def baseEnd_2619470 : Nat := 896698113355314363518855

theorem tailTrace_2619470 : CollatzResearch.WordTrace tailWord_2619470 prefixEnd_2619470 896698113355314363518855 := by
  unfold tailWord_2619470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942489977514379338021983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63693279880076689802783909 11942489977514379338021983)
  ·
    refine ⟨17913734966271569007032975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11942489977514379338021983 17913734966271569007032975)
    ·
      refine ⟨26870602449407353510549463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17913734966271569007032975 26870602449407353510549463)
      ·
        refine ⟨40305903674111030265824195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26870602449407353510549463 40305903674111030265824195)
        ·
          refine ⟨60458855511166545398736293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40305903674111030265824195 60458855511166545398736293)
          ·
            refine ⟨11336035408343727262263055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60458855511166545398736293 11336035408343727262263055)
            ·
              refine ⟨17004053112515590893394583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11336035408343727262263055 17004053112515590893394583)
              ·
                refine ⟨25506079668773386340091875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17004053112515590893394583 25506079668773386340091875)
                ·
                  refine ⟨38259119503160079510137813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25506079668773386340091875 38259119503160079510137813)
                  ·
                    refine ⟨896698113355314363518855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38259119503160079510137813 896698113355314363518855)
                    ·
                      rfl

theorem cell22_2619470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2619470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619470 prefixEnd_2619470 := by exact prefixLift 2619470
  have htrace : WordTrace (prefixWord ++ tailWord_2619470) baseStart_2619470 baseEnd_2619470 := by
    simpa [prefixWord, tailWord_2619470, baseEnd_2619470] using wordTrace_append hprefix tailTrace_2619470
  have hstable : (prefixWord ++ tailWord_2619470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619470).length < 2 ^ (prefixWord ++ tailWord_2619470).sum := by decide
  have hdescent : baseEnd_2619470 < baseStart_2619470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619517 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2619517 : Nat := 118140960795 + 2619517 * 2 ^ 59
def prefixEnd_2619517 : Nat := 4983230072969 + 3 ^ 40 * 2619517 * 2
def baseEnd_2619517 : Nat := 298904734138607302531237

theorem tailTrace_2619517 : CollatzResearch.WordTrace tailWord_2619517 prefixEnd_2619517 298904734138607302531237 := by
  unfold tailWord_2619517
  simp only [CollatzResearch.WordTrace]
  refine ⟨95541634050944761731136805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63694422700629841154091203 95541634050944761731136805)
  ·
    refine ⟨17914056384552142824588151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95541634050944761731136805 17914056384552142824588151)
    ·
      refine ⟨26871084576828214236882227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17914056384552142824588151 26871084576828214236882227)
      ·
        refine ⟨40306626865242321355323341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26871084576828214236882227 40306626865242321355323341)
        ·
          refine ⟨15114985074465870508246253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40306626865242321355323341 15114985074465870508246253)
          ·
            refine ⟨5668119402924701440592345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15114985074465870508246253 5668119402924701440592345)
            ·
              refine ⟨4251089552193526080444259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5668119402924701440592345 4251089552193526080444259)
              ·
                refine ⟨6376634328290289120666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251089552193526080444259 6376634328290289120666389)
                ·
                  refine ⟨298904734138607302531237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6376634328290289120666389 298904734138607302531237)
                  ·
                    rfl

theorem cell22_2619517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2619517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619517 prefixEnd_2619517 := by exact prefixLift 2619517
  have htrace : WordTrace (prefixWord ++ tailWord_2619517) baseStart_2619517 baseEnd_2619517 := by
    simpa [prefixWord, tailWord_2619517, baseEnd_2619517] using wordTrace_append hprefix tailTrace_2619517
  have hstable : (prefixWord ++ tailWord_2619517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619517).length < 2 ^ (prefixWord ++ tailWord_2619517).sum := by decide
  have hdescent : baseEnd_2619517 < baseStart_2619517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619551 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 4]
def baseStart_2619551 : Nat := 118140960795 + 2619551 * 2 ^ 59
def prefixEnd_2619551 : Nat := 4983230072969 + 3 ^ 40 * 2619551 * 2
def baseEnd_2619551 : Nat := 298908613770219050747869

theorem tailTrace_2619551 : CollatzResearch.WordTrace tailWord_2619551 prefixEnd_2619551 298908613770219050747869 := by
  unfold tailWord_2619551
  simp only [CollatzResearch.WordTrace]
  refine ⟨95542874132821585537874507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63695249421881057025249671 95542874132821585537874507)
  ·
    refine ⟨143314311199232378306811761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95542874132821585537874507 143314311199232378306811761)
    ·
      refine ⟨107485733399424283730108821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143314311199232378306811761 107485733399424283730108821)
      ·
        refine ⟨5038393753098013299848851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107485733399424283730108821 5038393753098013299848851)
        ·
          refine ⟨7557590629647019949773277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038393753098013299848851 7557590629647019949773277)
          ·
            refine ⟨2834096486117632481164979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7557590629647019949773277 2834096486117632481164979)
            ·
              refine ⟨4251144729176448721747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834096486117632481164979 4251144729176448721747469)
              ·
                refine ⟨1594179273441168270655301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4251144729176448721747469 1594179273441168270655301)
                ·
                  refine ⟨298908613770219050747869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594179273441168270655301 298908613770219050747869)
                  ·
                    rfl

theorem cell22_2619551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 4].length) (baseStart_2619551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619551 prefixEnd_2619551 := by exact prefixLift 2619551
  have htrace : WordTrace (prefixWord ++ tailWord_2619551) baseStart_2619551 baseEnd_2619551 := by
    simpa [prefixWord, tailWord_2619551, baseEnd_2619551] using wordTrace_append hprefix tailTrace_2619551
  have hstable : (prefixWord ++ tailWord_2619551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619551).length < 2 ^ (prefixWord ++ tailWord_2619551).sum := by decide
  have hdescent : baseEnd_2619551 < baseStart_2619551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619624 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_2619624 : Nat := 118140960795 + 2619624 * 2 ^ 59
def prefixEnd_2619624 : Nat := 4983230072969 + 3 ^ 40 * 2619624 * 2
def baseEnd_2619624 : Nat := 298916943567503098389461

theorem tailTrace_2619624 : CollatzResearch.WordTrace tailWord_2619624 prefixEnd_2619624 298916943567503098389461 := by
  unfold tailWord_2619624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47772768330778559502640963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63697024441038079336854617 47772768330778559502640963)
  ·
    refine ⟨71659152496167839253961445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47772768330778559502640963 71659152496167839253961445)
    ·
      refine ⟨13436091093031469860117771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71659152496167839253961445 13436091093031469860117771)
      ·
        refine ⟨20154136639547204790176657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13436091093031469860117771 20154136639547204790176657)
        ·
          refine ⟨15115602479660403592632493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20154136639547204790176657 15115602479660403592632493)
          ·
            refine ⟨5668350929872651347237185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15115602479660403592632493 5668350929872651347237185)
            ·
              refine ⟨4251263197404488510427889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5668350929872651347237185 4251263197404488510427889)
              ·
                refine ⟨3188447398053366382820917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251263197404488510427889 3188447398053366382820917)
                ·
                  refine ⟨298916943567503098389461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188447398053366382820917 298916943567503098389461)
                  ·
                    rfl

theorem cell22_2619624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_2619624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619624 prefixEnd_2619624 := by exact prefixLift 2619624
  have htrace : WordTrace (prefixWord ++ tailWord_2619624) baseStart_2619624 baseEnd_2619624 := by
    simpa [prefixWord, tailWord_2619624, baseEnd_2619624] using wordTrace_append hprefix tailTrace_2619624
  have hstable : (prefixWord ++ tailWord_2619624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619624).length < 2 ^ (prefixWord ++ tailWord_2619624).sum := by decide
  have hdescent : baseEnd_2619624 < baseStart_2619624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619669 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 4]
def baseStart_2619669 : Nat := 118140960795 + 2619669 * 2 ^ 59
def prefixEnd_2619669 : Nat := 4983230072969 + 3 ^ 40 * 2619669 * 2
def baseEnd_2619669 : Nat := 298922078374048059264415

theorem tailTrace_2619669 : CollatzResearch.WordTrace tailWord_2619669 prefixEnd_2619669 298922078374048059264415 := by
  unfold tailWord_2619669
  simp only [CollatzResearch.WordTrace]
  refine ⟨95547177946394091690670061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63698118630929394460446707 95547177946394091690670061)
  ·
    refine ⟨35830191729897784384001273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95547177946394091690670061 35830191729897784384001273)
    ·
      refine ⟨26872643797423338288000955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35830191729897784384001273 26872643797423338288000955)
      ·
        refine ⟨40308965696135007432001433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26872643797423338288000955 40308965696135007432001433)
        ·
          refine ⟨30231724272101255574001075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40308965696135007432001433 30231724272101255574001075)
          ·
            refine ⟨45347586408151883361001613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30231724272101255574001075 45347586408151883361001613)
            ·
              refine ⟨17005344903056956260375605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45347586408151883361001613 17005344903056956260375605)
              ·
                refine ⟨1594251084661589649410213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17005344903056956260375605 1594251084661589649410213)
                ·
                  refine ⟨298922078374048059264415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594251084661589649410213 298922078374048059264415)
                  ·
                    rfl

theorem cell22_2619669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_2619669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619669 prefixEnd_2619669 := by exact prefixLift 2619669
  have htrace : WordTrace (prefixWord ++ tailWord_2619669) baseStart_2619669 baseEnd_2619669 := by
    simpa [prefixWord, tailWord_2619669, baseEnd_2619669] using wordTrace_append hprefix tailTrace_2619669
  have hstable : (prefixWord ++ tailWord_2619669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619669).length < 2 ^ (prefixWord ++ tailWord_2619669).sum := by decide
  have hdescent : baseEnd_2619669 < baseStart_2619669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619671 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 1, 4]
def baseStart_2619671 : Nat := 118140960795 + 2619671 * 2 ^ 59
def prefixEnd_2619671 : Nat := 4983230072969 + 3 ^ 40 * 2619671 * 2
def baseEnd_2619671 : Nat := 896766919763016839243239

theorem tailTrace_2619671 : CollatzResearch.WordTrace tailWord_2619671 prefixEnd_2619671 896766919763016839243239 := by
  unfold tailWord_2619671
  simp only [CollatzResearch.WordTrace]
  refine ⟨95547250892386846032242867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63698167261591230688161911 95547250892386846032242867)
  ·
    refine ⟨143320876338580269048364301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95547250892386846032242867 143320876338580269048364301)
    ·
      refine ⟨53745328626967600893136613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143320876338580269048364301 53745328626967600893136613)
      ·
        refine ⟨10077249117556425167463115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53745328626967600893136613 10077249117556425167463115)
        ·
          refine ⟨15115873676334637751194673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10077249117556425167463115 15115873676334637751194673)
          ·
            refine ⟨11336905257250978313396005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15115873676334637751194673 11336905257250978313396005)
            ·
              refine ⟨2125669735734558433761751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11336905257250978313396005 2125669735734558433761751)
              ·
                refine ⟨3188504603601837650642627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125669735734558433761751 3188504603601837650642627)
                ·
                  refine ⟨4782756905402756475963941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188504603601837650642627 4782756905402756475963941)
                  ·
                    refine ⟨896766919763016839243239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4782756905402756475963941 896766919763016839243239)
                    ·
                      rfl

theorem cell22_2619671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_2619671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619671 prefixEnd_2619671 := by exact prefixLift 2619671
  have htrace : WordTrace (prefixWord ++ tailWord_2619671) baseStart_2619671 baseEnd_2619671 := by
    simpa [prefixWord, tailWord_2619671, baseEnd_2619671] using wordTrace_append hprefix tailTrace_2619671
  have hstable : (prefixWord ++ tailWord_2619671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619671).length < 2 ^ (prefixWord ++ tailWord_2619671).sum := by decide
  have hdescent : baseEnd_2619671 < baseStart_2619671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619836 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_2619836 : Nat := 118140960795 + 2619836 * 2 ^ 59
def prefixEnd_2619836 : Nat := 4983230072969 + 3 ^ 40 * 2619836 * 2
def baseEnd_2619836 : Nat := 896823402635011408867733

theorem tailTrace_2619836 : CollatzResearch.WordTrace tailWord_2619836 prefixEnd_2619836 896823402635011408867733 := by
  unfold tailWord_2619836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47776634468394539605999681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63702179291192719474666241 47776634468394539605999681)
  ·
    refine ⟨35832475851295904704499761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47776634468394539605999681 35832475851295904704499761)
    ·
      refine ⟨26874356888471928528374821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35832475851295904704499761 26874356888471928528374821)
      ·
        refine ⟨5038941916588486599070279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26874356888471928528374821 5038941916588486599070279)
        ·
          refine ⟨7558412874882729898605419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038941916588486599070279 7558412874882729898605419)
          ·
            refine ⟨11337619312324094847908129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7558412874882729898605419 11337619312324094847908129)
            ·
              refine ⟨8503214484243071135931097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11337619312324094847908129 8503214484243071135931097)
              ·
                refine ⟨6377410863182303351948323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8503214484243071135931097 6377410863182303351948323)
                ·
                  refine ⟨9566116294773455027922485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377410863182303351948323 9566116294773455027922485)
                  ·
                    refine ⟨896823402635011408867733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9566116294773455027922485 896823402635011408867733)
                    ·
                      rfl

theorem cell22_2619836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_2619836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619836 prefixEnd_2619836 := by exact prefixLift 2619836
  have htrace : WordTrace (prefixWord ++ tailWord_2619836) baseStart_2619836 baseEnd_2619836 := by
    simpa [prefixWord, tailWord_2619836, baseEnd_2619836] using wordTrace_append hprefix tailTrace_2619836
  have hstable : (prefixWord ++ tailWord_2619836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619836).length < 2 ^ (prefixWord ++ tailWord_2619836).sum := by decide
  have hdescent : baseEnd_2619836 < baseStart_2619836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619898 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_2619898 : Nat := 118140960795 + 2619898 * 2 ^ 59
def prefixEnd_2619898 : Nat := 4983230072969 + 3 ^ 40 * 2619898 * 2
def baseEnd_2619898 : Nat := 896844626502063913817543

theorem tailTrace_2619898 : CollatzResearch.WordTrace tailWord_2619898 prefixEnd_2619898 896844626502063913817543 := by
  unfold tailWord_2619898
  simp only [CollatzResearch.WordTrace]
  refine ⟨23888882565641115950189087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63703686841709642533837565 23888882565641115950189087)
  ·
    refine ⟨35833323848461673925283631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23888882565641115950189087 35833323848461673925283631)
    ·
      refine ⟨53749985772692510887925447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35833323848461673925283631 53749985772692510887925447)
      ·
        refine ⟨80624978659038766331888171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53749985772692510887925447 80624978659038766331888171)
        ·
          refine ⟨120937467988558149497832257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80624978659038766331888171 120937467988558149497832257)
          ·
            refine ⟨90703100991418612123374193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120937467988558149497832257 90703100991418612123374193)
            ·
              refine ⟨68027325743563959092530645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90703100991418612123374193 68027325743563959092530645)
              ·
                refine ⟨1594390447114780291231187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68027325743563959092530645 1594390447114780291231187)
                ·
                  refine ⟨2391585670672170436846781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594390447114780291231187 2391585670672170436846781)
                  ·
                    refine ⟨896844626502063913817543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391585670672170436846781 896844626502063913817543)
                    ·
                      rfl

theorem cell22_2619898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_2619898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619898 prefixEnd_2619898 := by exact prefixLift 2619898
  have htrace : WordTrace (prefixWord ++ tailWord_2619898) baseStart_2619898 baseEnd_2619898 := by
    simpa [prefixWord, tailWord_2619898, baseEnd_2619898] using wordTrace_append hprefix tailTrace_2619898
  have hstable : (prefixWord ++ tailWord_2619898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619898).length < 2 ^ (prefixWord ++ tailWord_2619898).sum := by decide
  have hdescent : baseEnd_2619898 < baseStart_2619898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619909 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2619909 : Nat := 118140960795 + 2619909 * 2 ^ 59
def prefixEnd_2619909 : Nat := 4983230072969 + 3 ^ 40 * 2619909 * 2
def baseEnd_2619909 : Nat := 896848392026863551792509

theorem tailTrace_2619909 : CollatzResearch.WordTrace tailWord_2619909 prefixEnd_2619909 896848392026863551792509 := by
  unfold tailWord_2619909
  simp only [CollatzResearch.WordTrace]
  refine ⟨95555931465524612679406781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63703954310349741786271187 95555931465524612679406781)
  ·
    refine ⟨35833474299571729754777543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95555931465524612679406781 35833474299571729754777543)
    ·
      refine ⟨53750211449357594632166315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35833474299571729754777543 53750211449357594632166315)
      ·
        refine ⟨80625317174036391948249473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53750211449357594632166315 80625317174036391948249473)
        ·
          refine ⟨60468987880527293961187105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80625317174036391948249473 60468987880527293961187105)
          ·
            refine ⟨45351740910395470470890329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60468987880527293961187105 45351740910395470470890329)
            ·
              refine ⟨34013805682796602853167747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45351740910395470470890329 34013805682796602853167747)
              ·
                refine ⟨51020708524194904279751621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34013805682796602853167747 51020708524194904279751621)
                ·
                  refine ⟨9566382848286544552453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51020708524194904279751621 9566382848286544552453429)
                  ·
                    refine ⟨896848392026863551792509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9566382848286544552453429 896848392026863551792509)
                    ·
                      rfl

theorem cell22_2619909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2619909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619909 prefixEnd_2619909 := by exact prefixLift 2619909
  have htrace : WordTrace (prefixWord ++ tailWord_2619909) baseStart_2619909 baseEnd_2619909 := by
    simpa [prefixWord, tailWord_2619909, baseEnd_2619909] using wordTrace_append hprefix tailTrace_2619909
  have hstable : (prefixWord ++ tailWord_2619909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619909).length < 2 ^ (prefixWord ++ tailWord_2619909).sum := by decide
  have hdescent : baseEnd_2619909 < baseStart_2619909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619928 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_2619928 : Nat := 118140960795 + 2619928 * 2 ^ 59
def prefixEnd_2619928 : Nat := 4983230072969 + 3 ^ 40 * 2619928 * 2
def baseEnd_2619928 : Nat := 298951632038384611855817

theorem tailTrace_2619928 : CollatzResearch.WordTrace tailWord_2619928 prefixEnd_2619928 298951632038384611855817 := by
  unfold tailWord_2619928
  simp only [CollatzResearch.WordTrace]
  refine ⟨47778312226227889462174219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63704416301637185949565625 47778312226227889462174219)
  ·
    refine ⟨71667468339341834193261329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47778312226227889462174219 71667468339341834193261329)
    ·
      refine ⟨53750601254506375644945997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71667468339341834193261329 53750601254506375644945997)
      ·
        refine ⟨20156475470439890866854749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53750601254506375644945997 20156475470439890866854749)
        ·
          refine ⟨7558678301414959075070531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20156475470439890866854749 7558678301414959075070531)
          ·
            refine ⟨11338017452122438612605797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7558678301414959075070531 11338017452122438612605797)
            ·
              refine ⟨2125878272272957239863587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11338017452122438612605797 2125878272272957239863587)
              ·
                refine ⟨3188817408409435859795381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125878272272957239863587 3188817408409435859795381)
                ·
                  refine ⟨298951632038384611855817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3188817408409435859795381 298951632038384611855817)
                  ·
                    rfl

theorem cell22_2619928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_2619928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619928 prefixEnd_2619928 := by exact prefixLift 2619928
  have htrace : WordTrace (prefixWord ++ tailWord_2619928) baseStart_2619928 baseEnd_2619928 := by
    simpa [prefixWord, tailWord_2619928, baseEnd_2619928] using wordTrace_append hprefix tailTrace_2619928
  have hstable : (prefixWord ++ tailWord_2619928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619928).length < 2 ^ (prefixWord ++ tailWord_2619928).sum := by decide
  have hdescent : baseEnd_2619928 < baseStart_2619928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619966 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2619966 : Nat := 118140960795 + 2619966 * 2 ^ 59
def prefixEnd_2619966 : Nat := 4983230072969 + 3 ^ 40 * 2619966 * 2
def baseEnd_2619966 : Nat := 896867904291734403117335

theorem tailTrace_2619966 : CollatzResearch.WordTrace tailWord_2619966 prefixEnd_2619966 896867904291734403117335 := by
  unfold tailWord_2619966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944751303289763926778969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63705340284212074276154501 11944751303289763926778969)
  ·
    refine ⟨8958563477467322945084227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11944751303289763926778969 8958563477467322945084227)
    ·
      refine ⟨13437845216200984417626341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8958563477467322945084227 13437845216200984417626341)
      ·
        refine ⟨2519595978037684578304939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13437845216200984417626341 2519595978037684578304939)
        ·
          refine ⟨3779393967056526867457409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519595978037684578304939 3779393967056526867457409)
          ·
            refine ⟨2834545475292395150593057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779393967056526867457409 2834545475292395150593057)
            ·
              refine ⟨2125909106469296362944793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834545475292395150593057 2125909106469296362944793)
              ·
                refine ⟨1594431829851972272208595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125909106469296362944793 1594431829851972272208595)
                ·
                  refine ⟨2391647744777958408312893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594431829851972272208595 2391647744777958408312893)
                  ·
                    refine ⟨896867904291734403117335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391647744777958408312893 896867904291734403117335)
                    ·
                      rfl

theorem cell22_2619966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2619966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619966 prefixEnd_2619966 := by exact prefixLift 2619966
  have htrace : WordTrace (prefixWord ++ tailWord_2619966) baseStart_2619966 baseEnd_2619966 := by
    simpa [prefixWord, tailWord_2619966, baseEnd_2619966] using wordTrace_append hprefix tailTrace_2619966
  have hstable : (prefixWord ++ tailWord_2619966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619966).length < 2 ^ (prefixWord ++ tailWord_2619966).sum := by decide
  have hdescent : baseEnd_2619966 < baseStart_2619966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619971 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 4, 3]
def baseStart_2619971 : Nat := 118140960795 + 2619971 * 2 ^ 59
def prefixEnd_2619971 : Nat := 4983230072969 + 3 ^ 40 * 2619971 * 2
def baseEnd_2619971 : Nat := 896869615893916056742319

theorem tailTrace_2619971 : CollatzResearch.WordTrace tailWord_2619971 prefixEnd_2619971 896869615893916056742319 := by
  unfold tailWord_2619971
  simp only [CollatzResearch.WordTrace]
  refine ⟨95558192791299997268163767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63705461860866664845442511 95558192791299997268163767)
  ·
    refine ⟨143337289186949995902245651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95558192791299997268163767 143337289186949995902245651)
    ·
      refine ⟨215005933780424993853368477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143337289186949995902245651 215005933780424993853368477)
      ·
        refine ⟨80627225167659372695013179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215005933780424993853368477 80627225167659372695013179)
        ·
          refine ⟨120940837751489059042519769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80627225167659372695013179 120940837751489059042519769)
          ·
            refine ⟨90705628313616794281889827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120940837751489059042519769 90705628313616794281889827)
            ·
              refine ⟨136058442470425191422834741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90705628313616794281889827 136058442470425191422834741)
              ·
                refine ⟨12755478981602361695890757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136058442470425191422834741 12755478981602361695890757)
                ·
                  refine ⟨2391652309050442817979517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12755478981602361695890757 2391652309050442817979517)
                  ·
                    refine ⟨896869615893916056742319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391652309050442817979517 896869615893916056742319)
                    ·
                      rfl

theorem cell22_2619971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].length) (baseStart_2619971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619971 prefixEnd_2619971 := by exact prefixLift 2619971
  have htrace : WordTrace (prefixWord ++ tailWord_2619971) baseStart_2619971 baseEnd_2619971 := by
    simpa [prefixWord, tailWord_2619971, baseEnd_2619971] using wordTrace_append hprefix tailTrace_2619971
  have hstable : (prefixWord ++ tailWord_2619971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619971).length < 2 ^ (prefixWord ++ tailWord_2619971).sum := by decide
  have hdescent : baseEnd_2619971 < baseStart_2619971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619973 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 4]
def baseStart_2619973 : Nat := 118140960795 + 2619973 * 2 ^ 59
def prefixEnd_2619973 : Nat := 4983230072969 + 3 ^ 40 * 2619973 * 2
def baseEnd_2619973 : Nat := 298956766844929572730771

theorem tailTrace_2619973 : CollatzResearch.WordTrace tailWord_2619973 prefixEnd_2619973 298956766844929572730771 := by
  unfold tailWord_2619973
  simp only [CollatzResearch.WordTrace]
  refine ⟨95558265737292751609736573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63705510491528501073157715 95558265737292751609736573)
  ·
    refine ⟨35834349651484781853651215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95558265737292751609736573 35834349651484781853651215)
    ·
      refine ⟨53751524477227172780476823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35834349651484781853651215 53751524477227172780476823)
      ·
        refine ⟨80627286715840759170715235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53751524477227172780476823 80627286715840759170715235)
        ·
          refine ⟨120940930073761138756072853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80627286715840759170715235 120940930073761138756072853)
          ·
            refine ⟨5669106097207553379190915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120940930073761138756072853 5669106097207553379190915)
            ·
              refine ⟨8503659145811330068786373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669106097207553379190915 8503659145811330068786373)
              ·
                refine ⟨1594436089839624387897445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8503659145811330068786373 1594436089839624387897445)
                ·
                  refine ⟨298956766844929572730771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594436089839624387897445 298956766844929572730771)
                  ·
                    rfl

theorem cell22_2619973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_2619973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619973 prefixEnd_2619973 := by exact prefixLift 2619973
  have htrace : WordTrace (prefixWord ++ tailWord_2619973) baseStart_2619973 baseEnd_2619973 := by
    simpa [prefixWord, tailWord_2619973, baseEnd_2619973] using wordTrace_append hprefix tailTrace_2619973
  have hstable : (prefixWord ++ tailWord_2619973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619973).length < 2 ^ (prefixWord ++ tailWord_2619973).sum := by decide
  have hdescent : baseEnd_2619973 < baseStart_2619973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619984 : List Nat := [2, 1, 1, 1, 1, 3, 2, 11]
def baseStart_2619984 : Nat := 118140960795 + 2619984 * 2 ^ 59
def prefixEnd_2619984 : Nat := 4983230072969 + 3 ^ 40 * 2619984 * 2
def baseEnd_2619984 : Nat := 99652674006620928463031

theorem tailTrace_2619984 : CollatzResearch.WordTrace tailWord_2619984 prefixEnd_2619984 99652674006620928463031 := by
  unfold tailWord_2619984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47779333470126450244193503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63705777960168600325591337 47779333470126450244193503)
  ·
    refine ⟨71669000205189675366290255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47779333470126450244193503 71669000205189675366290255)
    ·
      refine ⟨107503500307784513049435383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71669000205189675366290255 107503500307784513049435383)
      ·
        refine ⟨161255250461676769574153075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107503500307784513049435383 161255250461676769574153075)
        ·
          refine ⟨241882875692515154361229613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161255250461676769574153075 241882875692515154361229613)
          ·
            refine ⟨90706078384693182885461105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241882875692515154361229613 90706078384693182885461105)
            ·
              refine ⟨68029558788519887164095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90706078384693182885461105 68029558788519887164095829)
              ·
                refine ⟨99652674006620928463031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 68029558788519887164095829 99652674006620928463031)
                ·
                  rfl

theorem cell22_2619984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_2619984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619984 prefixEnd_2619984 := by exact prefixLift 2619984
  have htrace : WordTrace (prefixWord ++ tailWord_2619984) baseStart_2619984 baseEnd_2619984 := by
    simpa [prefixWord, tailWord_2619984, baseEnd_2619984] using wordTrace_append hprefix tailTrace_2619984
  have hstable : (prefixWord ++ tailWord_2619984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619984).length < 2 ^ (prefixWord ++ tailWord_2619984).sum := by decide
  have hdescent : baseEnd_2619984 < baseStart_2619984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619986 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2619986 : Nat := 118140960795 + 2619986 * 2 ^ 59
def prefixEnd_2619986 : Nat := 4983230072969 + 3 ^ 40 * 2619986 * 2
def baseEnd_2619986 : Nat := 896874750700461017617273

theorem tailTrace_2619986 : CollatzResearch.WordTrace tailWord_2619986 prefixEnd_2619986 896874750700461017617273 := by
  unfold tailWord_2619986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23889684971561413707489953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63705826590830436553306541 23889684971561413707489953)
  ·
    refine ⟨17917263728671060280617465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23889684971561413707489953 17917263728671060280617465)
    ·
      refine ⟨13437947796503295210463099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17917263728671060280617465 13437947796503295210463099)
      ·
        refine ⟨20156921694754942815694649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13437947796503295210463099 20156921694754942815694649)
        ·
          refine ⟨15117691271066207111770987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20156921694754942815694649 15117691271066207111770987)
          ·
            refine ⟨22676536906599310667656481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15117691271066207111770987 22676536906599310667656481)
            ·
              refine ⟨17007402679949483000742361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22676536906599310667656481 17007402679949483000742361)
              ·
                refine ⟨12755552009962112250556771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17007402679949483000742361 12755552009962112250556771)
                ·
                  refine ⟨19133328014943168375835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12755552009962112250556771 19133328014943168375835157)
                  ·
                    refine ⟨896874750700461017617273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19133328014943168375835157 896874750700461017617273)
                    ·
                      rfl

theorem cell22_2619986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2619986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619986 prefixEnd_2619986 := by exact prefixLift 2619986
  have htrace : WordTrace (prefixWord ++ tailWord_2619986) baseStart_2619986 baseEnd_2619986 := by
    simpa [prefixWord, tailWord_2619986, baseEnd_2619986] using wordTrace_append hprefix tailTrace_2619986
  have hstable : (prefixWord ++ tailWord_2619986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619986).length < 2 ^ (prefixWord ++ tailWord_2619986).sum := by decide
  have hdescent : baseEnd_2619986 < baseStart_2619986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2619988 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2619988 : Nat := 118140960795 + 2619988 * 2 ^ 59
def prefixEnd_2619988 : Nat := 4983230072969 + 3 ^ 40 * 2619988 * 2
def baseEnd_2619988 : Nat := 896875435341333679067267

theorem tailTrace_2619988 : CollatzResearch.WordTrace tailWord_2619988 prefixEnd_2619988 896875435341333679067267 := by
  unfold tailWord_2619988
  simp only [CollatzResearch.WordTrace]
  refine ⟨47779406416119204585766309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63705875221492272781021745 47779406416119204585766309)
  ·
    refine ⟨8958638703022350859831183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47779406416119204585766309 8958638703022350859831183)
    ·
      refine ⟨13437958054533526289746775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8958638703022350859831183 13437958054533526289746775)
      ·
        refine ⟨20156937081800289434620163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13437958054533526289746775 20156937081800289434620163)
        ·
          refine ⟨30235405622700434151930245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20156937081800289434620163 30235405622700434151930245)
          ·
            refine ⟨5669138554256331403486921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30235405622700434151930245 5669138554256331403486921)
            ·
              refine ⟨4251853915692248552615191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5669138554256331403486921 4251853915692248552615191)
              ·
                refine ⟨6377780873538372828922787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4251853915692248552615191 6377780873538372828922787)
                ·
                  refine ⟨9566671310307559243384181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6377780873538372828922787 9566671310307559243384181)
                  ·
                    refine ⟨896875435341333679067267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9566671310307559243384181 896875435341333679067267)
                    ·
                      rfl

theorem cell22_2619988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2619988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2619988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2619988 prefixEnd_2619988 := by exact prefixLift 2619988
  have htrace : WordTrace (prefixWord ++ tailWord_2619988) baseStart_2619988 baseEnd_2619988 := by
    simpa [prefixWord, tailWord_2619988, baseEnd_2619988] using wordTrace_append hprefix tailTrace_2619988
  have hstable : (prefixWord ++ tailWord_2619988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2619988).length < 2 ^ (prefixWord ++ tailWord_2619988).sum := by decide
  have hdescent : baseEnd_2619988 < baseStart_2619988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2619988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620050 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2620050 : Nat := 118140960795 + 2620050 * 2 ^ 59
def prefixEnd_2620050 : Nat := 4983230072969 + 3 ^ 40 * 2620050 * 2
def baseEnd_2620050 : Nat := 896896659208386184017077

theorem tailTrace_2620050 : CollatzResearch.WordTrace tailWord_2620050 prefixEnd_2620050 896896659208386184017077 := by
  unfold tailWord_2620050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23890268539503448440072401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63707382772009195840193069 23890268539503448440072401)
  ·
    refine ⟨17917701404627586330054301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23890268539503448440072401 17917701404627586330054301)
    ·
      refine ⟨6719138026735344873770363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17917701404627586330054301 6719138026735344873770363)
      ·
        refine ⟨10078707040103017310655545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719138026735344873770363 10078707040103017310655545)
        ·
          refine ⟨7559030280077262982991659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10078707040103017310655545 7559030280077262982991659)
          ·
            refine ⟨11338545420115894474487489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559030280077262982991659 11338545420115894474487489)
            ·
              refine ⟨8503909065086920855865617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11338545420115894474487489 8503909065086920855865617)
              ·
                refine ⟨6377931798815190641899213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8503909065086920855865617 6377931798815190641899213)
                ·
                  refine ⟨2391724424555696490712205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6377931798815190641899213 2391724424555696490712205)
                  ·
                    refine ⟨896896659208386184017077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2391724424555696490712205 896896659208386184017077)
                    ·
                      rfl

theorem cell22_2620050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2620050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620050 prefixEnd_2620050 := by exact prefixLift 2620050
  have htrace : WordTrace (prefixWord ++ tailWord_2620050) baseStart_2620050 baseEnd_2620050 := by
    simpa [prefixWord, tailWord_2620050, baseEnd_2620050] using wordTrace_append hprefix tailTrace_2620050
  have hstable : (prefixWord ++ tailWord_2620050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620050).length < 2 ^ (prefixWord ++ tailWord_2620050).sum := by decide
  have hdescent : baseEnd_2620050 < baseStart_2620050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620061 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2620061 : Nat := 118140960795 + 2620061 * 2 ^ 59
def prefixEnd_2620061 : Nat := 4983230072969 + 3 ^ 40 * 2620061 * 2
def baseEnd_2620061 : Nat := 896900424733185821992043

theorem tailTrace_2620061 : CollatzResearch.WordTrace tailWord_2620061 prefixEnd_2620061 896900424733185821992043 := by
  unfold tailWord_2620061
  simp only [CollatzResearch.WordTrace]
  refine ⟨95561475360973942638940037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63707650240649295092626691 95561475360973942638940037)
  ·
    refine ⟨17917776630182614244801257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95561475360973942638940037 17917776630182614244801257)
    ·
      refine ⟨13438332472636960683600943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17917776630182614244801257 13438332472636960683600943)
      ·
        refine ⟨20157498708955441025401415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438332472636960683600943 20157498708955441025401415)
        ·
          refine ⟨30236248063433161538102123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20157498708955441025401415 30236248063433161538102123)
          ·
            refine ⟨45354372095149742307153185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30236248063433161538102123 45354372095149742307153185)
            ·
              refine ⟨34015779071362306730364889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45354372095149742307153185 34015779071362306730364889)
              ·
                refine ⟨25511834303521730047773667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34015779071362306730364889 25511834303521730047773667)
                ·
                  refine ⟨38267751455282595071660501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25511834303521730047773667 38267751455282595071660501)
                  ·
                    refine ⟨896900424733185821992043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38267751455282595071660501 896900424733185821992043)
                    ·
                      rfl

theorem cell22_2620061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2620061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620061 prefixEnd_2620061 := by exact prefixLift 2620061
  have htrace : WordTrace (prefixWord ++ tailWord_2620061) baseStart_2620061 baseEnd_2620061 := by
    simpa [prefixWord, tailWord_2620061, baseEnd_2620061] using wordTrace_append hprefix tailTrace_2620061
  have hstable : (prefixWord ++ tailWord_2620061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620061).length < 2 ^ (prefixWord ++ tailWord_2620061).sum := by decide
  have hdescent : baseEnd_2620061 < baseStart_2620061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620097 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 5]
def baseStart_2620097 : Nat := 118140960795 + 2620097 * 2 ^ 59
def prefixEnd_2620097 : Nat := 4983230072969 + 3 ^ 40 * 2620097 * 2
def baseEnd_2620097 : Nat := 298970916089631242697311

theorem tailTrace_2620097 : CollatzResearch.WordTrace tailWord_2620097 prefixEnd_2620097 298970916089631242697311 := by
  unfold tailWord_2620097
  simp only [CollatzResearch.WordTrace]
  refine ⟨95562788388843520787250545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63708525592562347191500363 95562788388843520787250545)
  ·
    refine ⟨71672091291632640590437909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95562788388843520787250545 71672091291632640590437909)
    ·
      refine ⟨3359629279295280027676777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71672091291632640590437909 3359629279295280027676777)
      ·
        refine ⟨2519721959471460020757583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3359629279295280027676777 2519721959471460020757583)
        ·
          refine ⟨3779582939207190031136375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519721959471460020757583 3779582939207190031136375)
          ·
            refine ⟨5669374408810785046704563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779582939207190031136375 5669374408810785046704563)
            ·
              refine ⟨8504061613216177570056845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669374408810785046704563 8504061613216177570056845)
              ·
                refine ⟨3189023104956066588771317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8504061613216177570056845 3189023104956066588771317)
                ·
                  refine ⟨298970916089631242697311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189023104956066588771317 298970916089631242697311)
                  ·
                    rfl

theorem cell22_2620097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_2620097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620097 prefixEnd_2620097 := by exact prefixLift 2620097
  have htrace : WordTrace (prefixWord ++ tailWord_2620097) baseStart_2620097 baseEnd_2620097 := by
    simpa [prefixWord, tailWord_2620097, baseEnd_2620097] using wordTrace_append hprefix tailTrace_2620097
  have hstable : (prefixWord ++ tailWord_2620097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620097).length < 2 ^ (prefixWord ++ tailWord_2620097).sum := by decide
  have hdescent : baseEnd_2620097 < baseStart_2620097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620110 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2620110 : Nat := 118140960795 + 2620110 * 2 ^ 59
def prefixEnd_2620110 : Nat := 4983230072969 + 3 ^ 40 * 2620110 * 2
def baseEnd_2620110 : Nat := 896917198434566027516893

theorem tailTrace_2620110 : CollatzResearch.WordTrace tailWord_2620110 prefixEnd_2620110 896917198434566027516893 := by
  unfold tailWord_2620110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11945407817224553000934223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63708841691864282671649189 11945407817224553000934223)
  ·
    refine ⟨17918111725836829501401335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11945407817224553000934223 17918111725836829501401335)
    ·
      refine ⟨26877167588755244252102003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17918111725836829501401335 26877167588755244252102003)
      ·
        refine ⟨40315751383132866378153005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26877167588755244252102003 40315751383132866378153005)
        ·
          refine ⟨15118406768674824891807377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40315751383132866378153005 15118406768674824891807377)
          ·
            refine ⟨11338805076506118668855533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15118406768674824891807377 11338805076506118668855533)
            ·
              refine ⟨4252051903689794500820825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11338805076506118668855533 4252051903689794500820825)
              ·
                refine ⟨3189038927767345875615619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252051903689794500820825 3189038927767345875615619)
                ·
                  refine ⟨4783558391651018813423429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189038927767345875615619 4783558391651018813423429)
                  ·
                    refine ⟨896917198434566027516893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783558391651018813423429 896917198434566027516893)
                    ·
                      rfl

theorem cell22_2620110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2620110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620110 prefixEnd_2620110 := by exact prefixLift 2620110
  have htrace : WordTrace (prefixWord ++ tailWord_2620110) baseStart_2620110 baseEnd_2620110 := by
    simpa [prefixWord, tailWord_2620110, baseEnd_2620110] using wordTrace_append hprefix tailTrace_2620110
  have hstable : (prefixWord ++ tailWord_2620110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620110).length < 2 ^ (prefixWord ++ tailWord_2620110).sum := by decide
  have hdescent : baseEnd_2620110 < baseStart_2620110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620136 : List Nat := [2, 1, 4, 1, 14]
def baseStart_2620136 : Nat := 118140960795 + 2620136 * 2 ^ 59
def prefixEnd_2620136 : Nat := 4983230072969 + 3 ^ 40 * 2620136 * 2
def baseEnd_2620136 : Nat := 3691053904386463482991

theorem tailTrace_2620136 : CollatzResearch.WordTrace tailWord_2620136 prefixEnd_2620136 3691053904386463482991 := by
  unfold tailWord_2620136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47782105417851115223960131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63709473890468153631946841 47782105417851115223960131)
  ·
    refine ⟨71673158126776672835940197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47782105417851115223960131 71673158126776672835940197)
    ·
      refine ⟨13438717148770626156738787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71673158126776672835940197 13438717148770626156738787)
      ·
        refine ⟨20158075723155939235108181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438717148770626156738787 20158075723155939235108181)
        ·
          refine ⟨3691053904386463482991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20158075723155939235108181 3691053904386463482991)
          ·
            rfl

theorem cell22_2620136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 14].length) (baseStart_2620136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620136 prefixEnd_2620136 := by exact prefixLift 2620136
  have htrace : WordTrace (prefixWord ++ tailWord_2620136) baseStart_2620136 baseEnd_2620136 := by
    simpa [prefixWord, tailWord_2620136, baseEnd_2620136] using wordTrace_append hprefix tailTrace_2620136
  have hstable : (prefixWord ++ tailWord_2620136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620136).length < 2 ^ (prefixWord ++ tailWord_2620136).sum := by decide
  have hdescent : baseEnd_2620136 < baseStart_2620136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620142 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_2620142 : Nat := 118140960795 + 2620142 * 2 ^ 59
def prefixEnd_2620142 : Nat := 4983230072969 + 3 ^ 40 * 2620142 * 2
def baseEnd_2620142 : Nat := 298976050896176203572265

theorem tailTrace_2620142 : CollatzResearch.WordTrace tailWord_2620142 prefixEnd_2620142 298976050896176203572265 := by
  unfold tailWord_2620142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11945553709210061684079835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63709619782453662315092453 11945553709210061684079835)
  ·
    refine ⟨17918330563815092526119753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11945553709210061684079835 17918330563815092526119753)
    ·
      refine ⟨13438747922861319394589815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17918330563815092526119753 13438747922861319394589815)
      ·
        refine ⟨20158121884291979091884723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13438747922861319394589815 20158121884291979091884723)
        ·
          refine ⟨30237182826437968637827085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20158121884291979091884723 30237182826437968637827085)
          ·
            refine ⟨11338943559914238239185157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30237182826437968637827085 11338943559914238239185157)
            ·
              refine ⟨2126051917483919669847217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11338943559914238239185157 2126051917483919669847217)
              ·
                refine ⟨1594538938112939752385413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126051917483919669847217 1594538938112939752385413)
                ·
                  refine ⟨298976050896176203572265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594538938112939752385413 298976050896176203572265)
                  ·
                    rfl

theorem cell22_2620142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_2620142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620142 prefixEnd_2620142 := by exact prefixLift 2620142
  have htrace : WordTrace (prefixWord ++ tailWord_2620142) baseStart_2620142 baseEnd_2620142 := by
    simpa [prefixWord, tailWord_2620142, baseEnd_2620142] using wordTrace_append hprefix tailTrace_2620142
  have hstable : (prefixWord ++ tailWord_2620142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620142).length < 2 ^ (prefixWord ++ tailWord_2620142).sum := by decide
  have hdescent : baseEnd_2620142 < baseStart_2620142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620151 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2620151 : Nat := 118140960795 + 2620151 * 2 ^ 59
def prefixEnd_2620151 : Nat := 4983230072969 + 3 ^ 40 * 2620151 * 2
def baseEnd_2620151 : Nat := 896931233572455587241767

theorem tailTrace_2620151 : CollatzResearch.WordTrace tailWord_2620151 prefixEnd_2620151 896931233572455587241767 := by
  unfold tailWord_2620151
  simp only [CollatzResearch.WordTrace]
  refine ⟨95564757930647888009716307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63709838620431925339810871 95564757930647888009716307)
  ·
    refine ⟨143347136895971832014574461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95564757930647888009716307 143347136895971832014574461)
    ·
      refine ⟨53755176335989437005465423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143347136895971832014574461 53755176335989437005465423)
      ·
        refine ⟨80632764503984155508198135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53755176335989437005465423 80632764503984155508198135)
        ·
          refine ⟨120949146755976233262297203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80632764503984155508198135 120949146755976233262297203)
          ·
            refine ⟨181423720133964349893445805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120949146755976233262297203 181423720133964349893445805)
            ·
              refine ⟨68033895050236631210042177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181423720133964349893445805 68033895050236631210042177)
              ·
                refine ⟨51025421287677473407531633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68033895050236631210042177 51025421287677473407531633)
                ·
                  refine ⟨38269065965758105055648725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51025421287677473407531633 38269065965758105055648725)
                  ·
                    refine ⟨896931233572455587241767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38269065965758105055648725 896931233572455587241767)
                    ·
                      rfl

theorem cell22_2620151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2620151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620151 prefixEnd_2620151 := by exact prefixLift 2620151
  have htrace : WordTrace (prefixWord ++ tailWord_2620151) baseStart_2620151 baseEnd_2620151 := by
    simpa [prefixWord, tailWord_2620151, baseEnd_2620151] using wordTrace_append hprefix tailTrace_2620151
  have hstable : (prefixWord ++ tailWord_2620151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620151).length < 2 ^ (prefixWord ++ tailWord_2620151).sum := by decide
  have hdescent : baseEnd_2620151 < baseStart_2620151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620215 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 5]
def baseStart_2620215 : Nat := 118140960795 + 2620215 * 2 ^ 59
def prefixEnd_2620215 : Nat := 4983230072969 + 3 ^ 40 * 2620215 * 2
def baseEnd_2620215 : Nat := 298984380693460251213857

theorem tailTrace_2620215 : CollatzResearch.WordTrace tailWord_2620215 prefixEnd_2620215 298984380693460251213857 := by
  unfold tailWord_2620215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95567092202416026940046099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63711394801610684626697399 95567092202416026940046099)
  ·
    refine ⟨143350638303624040410069149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95567092202416026940046099 143350638303624040410069149)
    ·
      refine ⟨53756489363859015153775931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143350638303624040410069149 53756489363859015153775931)
      ·
        refine ⟨80634734045788522730663897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53756489363859015153775931 80634734045788522730663897)
        ·
          refine ⟨60476050534341392047997923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80634734045788522730663897 60476050534341392047997923)
          ·
            refine ⟨90714075801512088071996885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60476050534341392047997923 90714075801512088071996885)
            ·
              refine ⟨2126111151597939564187427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90714075801512088071996885 2126111151597939564187427)
              ·
                refine ⟨3189166727396909346281141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126111151597939564187427 3189166727396909346281141)
                ·
                  refine ⟨298984380693460251213857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189166727396909346281141 298984380693460251213857)
                  ·
                    rfl

theorem cell22_2620215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 5].length) (baseStart_2620215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620215 prefixEnd_2620215 := by exact prefixLift 2620215
  have htrace : WordTrace (prefixWord ++ tailWord_2620215) baseStart_2620215 baseEnd_2620215 := by
    simpa [prefixWord, tailWord_2620215, baseEnd_2620215] using wordTrace_append hprefix tailTrace_2620215
  have hstable : (prefixWord ++ tailWord_2620215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620215).length < 2 ^ (prefixWord ++ tailWord_2620215).sum := by decide
  have hdescent : baseEnd_2620215 < baseStart_2620215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620245 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2620245 : Nat := 118140960795 + 2620245 * 2 ^ 59
def prefixEnd_2620245 : Nat := 4983230072969 + 3 ^ 40 * 2620245 * 2
def baseEnd_2620245 : Nat := 896963411693470675391479

theorem tailTrace_2620245 : CollatzResearch.WordTrace tailWord_2620245 prefixEnd_2620245 896963411693470675391479 := by
  unfold tailWord_2620245
  simp only [CollatzResearch.WordTrace]
  refine ⟨95568186392307342063638189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63712124261538228042425459 95568186392307342063638189)
  ·
    refine ⟨35838069897115253273864321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95568186392307342063638189 35838069897115253273864321)
    ·
      refine ⟨26878552422836439955398241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35838069897115253273864321 26878552422836439955398241)
      ·
        refine ⟨20158914317127329966548681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26878552422836439955398241 20158914317127329966548681)
        ·
          refine ⟨15119185737845497474911511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20158914317127329966548681 15119185737845497474911511)
          ·
            refine ⟨22678778606768246212367267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15119185737845497474911511 22678778606768246212367267)
            ·
              refine ⟨34018167910152369318550901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22678778606768246212367267 34018167910152369318550901)
              ·
                refine ⟨3189203241576784623614147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34018167910152369318550901 3189203241576784623614147)
                ·
                  refine ⟨4783804862365176935421221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189203241576784623614147 4783804862365176935421221)
                  ·
                    refine ⟨896963411693470675391479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4783804862365176935421221 896963411693470675391479)
                    ·
                      rfl

theorem cell22_2620245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2620245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620245 prefixEnd_2620245 := by exact prefixLift 2620245
  have htrace : WordTrace (prefixWord ++ tailWord_2620245) baseStart_2620245 baseEnd_2620245 := by
    simpa [prefixWord, tailWord_2620245, baseEnd_2620245] using wordTrace_append hprefix tailTrace_2620245
  have hstable : (prefixWord ++ tailWord_2620245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620245).length < 2 ^ (prefixWord ++ tailWord_2620245).sum := by decide
  have hdescent : baseEnd_2620245 < baseStart_2620245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620260 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2620260 : Nat := 118140960795 + 2620260 * 2 ^ 59
def prefixEnd_2620260 : Nat := 4983230072969 + 3 ^ 40 * 2620260 * 2
def baseEnd_2620260 : Nat := 298989515500005212088811

theorem tailTrace_2620260 : CollatzResearch.WordTrace tailWord_2620260 prefixEnd_2620260 298989515500005212088811 := by
  unfold tailWord_2620260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47784366743626499812717117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63712488991501999750289489 47784366743626499812717117)
  ·
    refine ⟨17919137528859937429768919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47784366743626499812717117 17919137528859937429768919)
    ·
      refine ⟨26878706293289906144653379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17919137528859937429768919 26878706293289906144653379)
      ·
        refine ⟨40318059439934859216980069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26878706293289906144653379 40318059439934859216980069)
        ·
          refine ⟨7559636144987786103183763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40318059439934859216980069 7559636144987786103183763)
          ·
            refine ⟨11339454217481679154775645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559636144987786103183763 11339454217481679154775645)
            ·
              refine ⟨4252295331555629683040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11339454217481679154775645 4252295331555629683040867)
              ·
                refine ⟨6378442997333444524561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252295331555629683040867 6378442997333444524561301)
                ·
                  refine ⟨298989515500005212088811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6378442997333444524561301 298989515500005212088811)
                  ·
                    rfl

theorem cell22_2620260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2620260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620260 prefixEnd_2620260 := by exact prefixLift 2620260
  have htrace : WordTrace (prefixWord ++ tailWord_2620260) baseStart_2620260 baseEnd_2620260 := by
    simpa [prefixWord, tailWord_2620260, baseEnd_2620260] using wordTrace_append hprefix tailTrace_2620260
  have hstable : (prefixWord ++ tailWord_2620260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620260).length < 2 ^ (prefixWord ++ tailWord_2620260).sum := by decide
  have hdescent : baseEnd_2620260 < baseStart_2620260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620322 : List Nat := [3, 3, 1, 2, 2, 3, 1, 7]
def baseStart_2620322 : Nat := 118140960795 + 2620322 * 2 ^ 59
def prefixEnd_2620322 : Nat := 4983230072969 + 3 ^ 40 * 2620322 * 2
def baseEnd_2620322 : Nat := 99665530040785349024027

theorem tailTrace_2620322 : CollatzResearch.WordTrace tailWord_2620322 prefixEnd_2620322 99665530040785349024027 := by
  unfold tailWord_2620322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892748703257096053547805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63713996542018922809460813 23892748703257096053547805)
  ·
    refine ⟨8959780763721411020080427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23892748703257096053547805 8959780763721411020080427)
    ·
      refine ⟨13439671145582116530120641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959780763721411020080427 13439671145582116530120641)
      ·
        refine ⟨10079753359186587397590481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13439671145582116530120641 10079753359186587397590481)
        ·
          refine ⟨7559815019389940548192861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10079753359186587397590481 7559815019389940548192861)
          ·
            refine ⟨2834930632271227705572323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559815019389940548192861 2834930632271227705572323)
            ·
              refine ⟨4252395948406841558358485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834930632271227705572323 4252395948406841558358485)
              ·
                refine ⟨99665530040785349024027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4252395948406841558358485 99665530040785349024027)
                ·
                  rfl

theorem cell22_2620322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_2620322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620322 prefixEnd_2620322 := by exact prefixLift 2620322
  have htrace : WordTrace (prefixWord ++ tailWord_2620322) baseStart_2620322 baseEnd_2620322 := by
    simpa [prefixWord, tailWord_2620322, baseEnd_2620322] using wordTrace_append hprefix tailTrace_2620322
  have hstable : (prefixWord ++ tailWord_2620322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620322).length < 2 ^ (prefixWord ++ tailWord_2620322).sum := by decide
  have hdescent : baseEnd_2620322 < baseStart_2620322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620350 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2620350 : Nat := 118140960795 + 2620350 * 2 ^ 59
def prefixEnd_2620350 : Nat := 4983230072969 + 3 ^ 40 * 2620350 * 2
def baseEnd_2620350 : Nat := 298999785113095133838719

theorem tailTrace_2620350 : CollatzResearch.WordTrace tailWord_2620350 prefixEnd_2620350 298999785113095133838719 := by
  unfold tailWord_2620350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946502007115868124526313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63714677371284629997473669 11946502007115868124526313)
  ·
    refine ⟨8959876505336901093394735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11946502007115868124526313 8959876505336901093394735)
    ·
      refine ⟨13439814758005351640092103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959876505336901093394735 13439814758005351640092103)
      ·
        refine ⟨20159722137008027460138155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13439814758005351640092103 20159722137008027460138155)
        ·
          refine ⟨30239583205512041190207233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20159722137008027460138155 30239583205512041190207233)
          ·
            refine ⟨22679687404134030892655425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30239583205512041190207233 22679687404134030892655425)
            ·
              refine ⟨17009765553100523169491569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22679687404134030892655425 17009765553100523169491569)
              ·
                refine ⟨12757324164825392377118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17009765553100523169491569 12757324164825392377118677)
                ·
                  refine ⟨298999785113095133838719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12757324164825392377118677 298999785113095133838719)
                  ·
                    rfl

theorem cell22_2620350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2620350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620350 prefixEnd_2620350 := by exact prefixLift 2620350
  have htrace : WordTrace (prefixWord ++ tailWord_2620350) baseStart_2620350 baseEnd_2620350 := by
    simpa [prefixWord, tailWord_2620350, baseEnd_2620350] using wordTrace_append hprefix tailTrace_2620350
  have hstable : (prefixWord ++ tailWord_2620350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620350).length < 2 ^ (prefixWord ++ tailWord_2620350).sum := by decide
  have hdescent : baseEnd_2620350 < baseStart_2620350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620367 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 5]
def baseStart_2620367 : Nat := 118140960795 + 2620367 * 2 ^ 59
def prefixEnd_2620367 : Nat := 4983230072969 + 3 ^ 40 * 2620367 * 2
def baseEnd_2620367 : Nat := 299001724928901007947035

theorem tailTrace_2620367 : CollatzResearch.WordTrace tailWord_2620367 prefixEnd_2620367 299001724928901007947035 := by
  unfold tailWord_2620367
  simp only [CollatzResearch.WordTrace]
  refine ⟨95572636097865356899579355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63715090731910237933052903 95572636097865356899579355)
  ·
    refine ⟨143358954146798035349369033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95572636097865356899579355 143358954146798035349369033)
    ·
      refine ⟨107519215610098526512026775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143358954146798035349369033 107519215610098526512026775)
      ·
        refine ⟨161278823415147789768040163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107519215610098526512026775 161278823415147789768040163)
        ·
          refine ⟨241918235122721684652060245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161278823415147789768040163 241918235122721684652060245)
          ·
            refine ⟨2834979317844394742016331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 241918235122721684652060245 2834979317844394742016331)
            ·
              refine ⟨4252468976766592113024497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834979317844394742016331 4252468976766592113024497)
              ·
                refine ⟨3189351732574944084768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252468976766592113024497 3189351732574944084768373)
                ·
                  refine ⟨299001724928901007947035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189351732574944084768373 299001724928901007947035)
                  ·
                    rfl

theorem cell22_2620367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].length) (baseStart_2620367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620367 prefixEnd_2620367 := by exact prefixLift 2620367
  have htrace : WordTrace (prefixWord ++ tailWord_2620367) baseStart_2620367 baseEnd_2620367 := by
    simpa [prefixWord, tailWord_2620367, baseEnd_2620367] using wordTrace_append hprefix tailTrace_2620367
  have hstable : (prefixWord ++ tailWord_2620367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620367).length < 2 ^ (prefixWord ++ tailWord_2620367).sum := by decide
  have hdescent : baseEnd_2620367 < baseStart_2620367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620405 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2620405 : Nat := 118140960795 + 2620405 * 2 ^ 59
def prefixEnd_2620405 : Nat := 4983230072969 + 3 ^ 40 * 2620405 * 2
def baseEnd_2620405 : Nat := 897018182963283591390989

theorem tailTrace_2620405 : CollatzResearch.WordTrace tailWord_2620405 prefixEnd_2620405 897018182963283591390989 := by
  unfold tailWord_2620405
  simp only [CollatzResearch.WordTrace]
  refine ⟨95574022071727689389462669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63716014714485126259641779 95574022071727689389462669)
  ·
    refine ⟨35840258276897883521048501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95574022071727689389462669 35840258276897883521048501)
    ·
      refine ⟨3360024213459176580098297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35840258276897883521048501 3360024213459176580098297)
      ·
        refine ⟨2520018160094382435073723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3360024213459176580098297 2520018160094382435073723)
        ·
          refine ⟨3780027240141573652610585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520018160094382435073723 3780027240141573652610585)
          ·
            refine ⟨2835020430106180239457939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780027240141573652610585 2835020430106180239457939)
            ·
              refine ⟨4252530645159270359186909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835020430106180239457939 4252530645159270359186909)
              ·
                refine ⟨1594698991934726384695091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4252530645159270359186909 1594698991934726384695091)
                ·
                  refine ⟨2392048487902089577042637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594698991934726384695091 2392048487902089577042637)
                  ·
                    refine ⟨897018182963283591390989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392048487902089577042637 897018182963283591390989)
                    ·
                      rfl

theorem cell22_2620405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2620405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620405 prefixEnd_2620405 := by exact prefixLift 2620405
  have htrace : WordTrace (prefixWord ++ tailWord_2620405) baseStart_2620405 baseEnd_2620405 := by
    simpa [prefixWord, tailWord_2620405, baseEnd_2620405] using wordTrace_append hprefix tailTrace_2620405
  have hstable : (prefixWord ++ tailWord_2620405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620405).length < 2 ^ (prefixWord ++ tailWord_2620405).sum := by decide
  have hdescent : baseEnd_2620405 < baseStart_2620405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620410 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_2620410 : Nat := 118140960795 + 2620410 * 2 ^ 59
def prefixEnd_2620410 : Nat := 4983230072969 + 3 ^ 40 * 2620410 * 2
def baseEnd_2620410 : Nat := 897019894565465245015973

theorem tailTrace_2620410 : CollatzResearch.WordTrace tailWord_2620410 prefixEnd_2620410 897019894565465245015973 := by
  unfold tailWord_2620410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23893551109177393810848671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63716136291139716828929789 23893551109177393810848671)
  ·
    refine ⟨35840326663766090716273007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23893551109177393810848671 35840326663766090716273007)
    ·
      refine ⟨53760489995649136074409511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35840326663766090716273007 53760489995649136074409511)
      ·
        refine ⟨80640734993473704111614267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53760489995649136074409511 80640734993473704111614267)
        ·
          refine ⟨120961102490210556167421401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80640734993473704111614267 120961102490210556167421401)
          ·
            refine ⟨90720826867657917125566051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120961102490210556167421401 90720826867657917125566051)
            ·
              refine ⟨136081240301486875688349077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90720826867657917125566051 136081240301486875688349077)
              ·
                refine ⟨6378808139132197297891363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136081240301486875688349077 6378808139132197297891363)
                ·
                  refine ⟨9568212208698295946837045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6378808139132197297891363 9568212208698295946837045)
                  ·
                    refine ⟨897019894565465245015973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9568212208698295946837045 897019894565465245015973)
                    ·
                      rfl

theorem cell22_2620410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_2620410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620410 prefixEnd_2620410 := by exact prefixLift 2620410
  have htrace : WordTrace (prefixWord ++ tailWord_2620410) baseStart_2620410 baseEnd_2620410 := by
    simpa [prefixWord, tailWord_2620410, baseEnd_2620410] using wordTrace_append hprefix tailTrace_2620410
  have hstable : (prefixWord ++ tailWord_2620410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620410).length < 2 ^ (prefixWord ++ tailWord_2620410).sum := by decide
  have hdescent : baseEnd_2620410 < baseStart_2620410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620427 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 4, 3]
def baseStart_2620427 : Nat := 118140960795 + 2620427 * 2 ^ 59
def prefixEnd_2620427 : Nat := 4983230072969 + 3 ^ 40 * 2620427 * 2
def baseEnd_2620427 : Nat := 897025714012882867340921

theorem tailTrace_2620427 : CollatzResearch.WordTrace tailWord_2620427 prefixEnd_2620427 897025714012882867340921 := by
  unfold tailWord_2620427
  simp only [CollatzResearch.WordTrace]
  refine ⟨95574824477647987146763535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63716549651765324764509023 95574824477647987146763535)
  ·
    refine ⟨143362236716471980720145303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95574824477647987146763535 143362236716471980720145303)
    ·
      refine ⟨215043355074707971080217955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143362236716471980720145303 215043355074707971080217955)
      ·
        refine ⟨322565032612061956620326933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215043355074707971080217955 322565032612061956620326933)
        ·
          refine ⟨15120235903690404216577825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 322565032612061956620326933 15120235903690404216577825)
          ·
            refine ⟨11340176927767803162433369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15120235903690404216577825 11340176927767803162433369)
            ·
              refine ⟨8505132695825852371825027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11340176927767803162433369 8505132695825852371825027)
              ·
                refine ⟨12757699043738778557737541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505132695825852371825027 12757699043738778557737541)
                ·
                  refine ⟨2392068570701020979575789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12757699043738778557737541 2392068570701020979575789)
                  ·
                    refine ⟨897025714012882867340921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392068570701020979575789 897025714012882867340921)
                    ·
                      rfl

theorem cell22_2620427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].length) (baseStart_2620427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620427 prefixEnd_2620427 := by exact prefixLift 2620427
  have htrace : WordTrace (prefixWord ++ tailWord_2620427) baseStart_2620427 baseEnd_2620427 := by
    simpa [prefixWord, tailWord_2620427, baseEnd_2620427] using wordTrace_append hprefix tailTrace_2620427
  have hstable : (prefixWord ++ tailWord_2620427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620427).length < 2 ^ (prefixWord ++ tailWord_2620427).sum := by decide
  have hdescent : baseEnd_2620427 < baseStart_2620427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620440 : List Nat := [2, 1, 2, 3, 2, 2, 1, 9]
def baseStart_2620440 : Nat := 118140960795 + 2620440 * 2 ^ 59
def prefixEnd_2620440 : Nat := 4983230072969 + 3 ^ 40 * 2620440 * 2
def baseEnd_2620440 : Nat := 99670018242061685196209

theorem tailTrace_2620440 : CollatzResearch.WordTrace tailWord_2620440 prefixEnd_2620440 99670018242061685196209 := by
  unfold tailWord_2620440
  simp only [CollatzResearch.WordTrace]
  refine ⟨47787649313300445183493387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63716865751067260244657849 47787649313300445183493387)
  ·
    refine ⟨71681473969950667775240081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47787649313300445183493387 71681473969950667775240081)
    ·
      refine ⟨53761105477463000831430061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71681473969950667775240081 53761105477463000831430061)
      ·
        refine ⟨20160414554048625311786273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53761105477463000831430061 20160414554048625311786273)
        ·
          refine ⟨15120310915536468983839705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20160414554048625311786273 15120310915536468983839705)
          ·
            refine ⟨11340233186652351737879779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15120310915536468983839705 11340233186652351737879779)
            ·
              refine ⟨17010349779978527606819669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340233186652351737879779 17010349779978527606819669)
              ·
                refine ⟨99670018242061685196209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17010349779978527606819669 99670018242061685196209)
                ·
                  rfl

theorem cell22_2620440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_2620440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620440 prefixEnd_2620440 := by exact prefixLift 2620440
  have htrace : WordTrace (prefixWord ++ tailWord_2620440) baseStart_2620440 baseEnd_2620440 := by
    simpa [prefixWord, tailWord_2620440, baseEnd_2620440] using wordTrace_append hprefix tailTrace_2620440
  have hstable : (prefixWord ++ tailWord_2620440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620440).length < 2 ^ (prefixWord ++ tailWord_2620440).sum := by decide
  have hdescent : baseEnd_2620440 < baseStart_2620440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620448 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_2620448 : Nat := 118140960795 + 2620448 * 2 ^ 59
def prefixEnd_2620448 : Nat := 4983230072969 + 3 ^ 40 * 2620448 * 2
def baseEnd_2620448 : Nat := 897032902742045812565857

theorem tailTrace_2620448 : CollatzResearch.WordTrace tailWord_2620448 prefixEnd_2620448 897032902742045812565857 := by
  unfold tailWord_2620448
  simp only [CollatzResearch.WordTrace]
  refine ⟨47787795205285953866638999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63717060273714605155518665 47787795205285953866638999)
  ·
    refine ⟨71681692807928930799958499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47787795205285953866638999 71681692807928930799958499)
    ·
      refine ⟨107522539211893396199937749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71681692807928930799958499 107522539211893396199937749)
      ·
        refine ⟨2520059512778751473436041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 107522539211893396199937749 2520059512778751473436041)
        ·
          refine ⟨1890044634584063605077031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520059512778751473436041 1890044634584063605077031)
          ·
            refine ⟨2835066951876095407615547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890044634584063605077031 2835066951876095407615547)
            ·
              refine ⟨4252600427814143111423321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835066951876095407615547 4252600427814143111423321)
              ·
                refine ⟨3189450320860607333567491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252600427814143111423321 3189450320860607333567491)
                ·
                  refine ⟨4784175481290911000351237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189450320860607333567491 4784175481290911000351237)
                  ·
                    refine ⟨897032902742045812565857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784175481290911000351237 897032902742045812565857)
                    ·
                      rfl

theorem cell22_2620448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_2620448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620448 prefixEnd_2620448 := by exact prefixLift 2620448
  have htrace : WordTrace (prefixWord ++ tailWord_2620448) baseStart_2620448 baseEnd_2620448 := by
    simpa [prefixWord, tailWord_2620448, baseEnd_2620448] using wordTrace_append hprefix tailTrace_2620448
  have hstable : (prefixWord ++ tailWord_2620448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620448).length < 2 ^ (prefixWord ++ tailWord_2620448).sum := by decide
  have hdescent : baseEnd_2620448 < baseStart_2620448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620485 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 7]
def baseStart_2620485 : Nat := 118140960795 + 2620485 * 2 ^ 59
def prefixEnd_2620485 : Nat := 4983230072969 + 3 ^ 40 * 2620485 * 2
def baseEnd_2620485 : Nat := 299015189532730016463581

theorem tailTrace_2620485 : CollatzResearch.WordTrace tailWord_2620485 prefixEnd_2620485 299015189532730016463581 := by
  unfold tailWord_2620485
  simp only [CollatzResearch.WordTrace]
  refine ⟨95576939911437863052374909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63717959940958575368249939 95576939911437863052374909)
  ·
    refine ⟨35841352466789198644640591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95576939911437863052374909 35841352466789198644640591)
    ·
      refine ⟨53762028700183797966960887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35841352466789198644640591 53762028700183797966960887)
      ·
        refine ⟨80643043050275696950441331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53762028700183797966960887 80643043050275696950441331)
        ·
          refine ⟨120964564575413545425661997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80643043050275696950441331 120964564575413545425661997)
          ·
            refine ⟨45361711715780079534623249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120964564575413545425661997 45361711715780079534623249)
            ·
              refine ⟨34021283786835059650967437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45361711715780079534623249 34021283786835059650967437)
              ·
                refine ⟨12757981420063147369112789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34021283786835059650967437 12757981420063147369112789)
                ·
                  refine ⟨299015189532730016463581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12757981420063147369112789 299015189532730016463581)
                  ·
                    rfl

theorem cell22_2620485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_2620485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620485 prefixEnd_2620485 := by exact prefixLift 2620485
  have htrace : WordTrace (prefixWord ++ tailWord_2620485) baseStart_2620485 baseEnd_2620485 := by
    simpa [prefixWord, tailWord_2620485, baseEnd_2620485] using wordTrace_append hprefix tailTrace_2620485
  have hstable : (prefixWord ++ tailWord_2620485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620485).length < 2 ^ (prefixWord ++ tailWord_2620485).sum := by decide
  have hdescent : baseEnd_2620485 < baseStart_2620485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620547 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 6]
def baseStart_2620547 : Nat := 118140960795 + 2620547 * 2 ^ 59
def prefixEnd_2620547 : Nat := 4983230072969 + 3 ^ 40 * 2620547 * 2
def baseEnd_2620547 : Nat := 299022264155080851446851

theorem tailTrace_2620547 : CollatzResearch.WordTrace tailWord_2620547 prefixEnd_2620547 299022264155080851446851 := by
  unfold tailWord_2620547
  simp only [CollatzResearch.WordTrace]
  refine ⟨95579201237213247641131895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63719467491475498427421263 95579201237213247641131895)
  ·
    refine ⟨143368801855819871461697843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95579201237213247641131895 143368801855819871461697843)
    ·
      refine ⟨215053202783729807192546765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143368801855819871461697843 215053202783729807192546765)
      ·
        refine ⟨80644951043898677697205037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215053202783729807192546765 80644951043898677697205037)
        ·
          refine ⟨30241856641462004136451889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80644951043898677697205037 30241856641462004136451889)
          ·
            refine ⟨22681392481096503102338917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30241856641462004136451889 22681392481096503102338917)
            ·
              refine ⟨4252761090205594331688547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22681392481096503102338917 4252761090205594331688547)
              ·
                refine ⟨6379141635308391497532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252761090205594331688547 6379141635308391497532821)
                ·
                  refine ⟨299022264155080851446851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6379141635308391497532821 299022264155080851446851)
                  ·
                    rfl

theorem cell22_2620547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_2620547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620547 prefixEnd_2620547 := by exact prefixLift 2620547
  have htrace : WordTrace (prefixWord ++ tailWord_2620547) baseStart_2620547 baseEnd_2620547 := by
    simpa [prefixWord, tailWord_2620547, baseEnd_2620547] using wordTrace_append hprefix tailTrace_2620547
  have hstable : (prefixWord ++ tailWord_2620547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620547).length < 2 ^ (prefixWord ++ tailWord_2620547).sum := by decide
  have hdescent : baseEnd_2620547 < baseStart_2620547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620577 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2620577 : Nat := 118140960795 + 2620577 * 2 ^ 59
def prefixEnd_2620577 : Nat := 4983230072969 + 3 ^ 40 * 2620577 * 2
def baseEnd_2620577 : Nat := 897077062078332476090461

theorem tailTrace_2620577 : CollatzResearch.WordTrace tailWord_2620577 prefixEnd_2620577 897077062078332476090461 := by
  unfold tailWord_2620577
  simp only [CollatzResearch.WordTrace]
  refine ⟨95580295427104562764723985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63720196951403041843149323 95580295427104562764723985)
  ·
    refine ⟨71685221570328422073542989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95580295427104562764723985 71685221570328422073542989)
    ·
      refine ⟨26881958088873158277578621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71685221570328422073542989 26881958088873158277578621)
      ·
        refine ⟨10080734283327434354091983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26881958088873158277578621 10080734283327434354091983)
        ·
          refine ⟨15121101424991151531137975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10080734283327434354091983 15121101424991151531137975)
          ·
            refine ⟨22681652137486727296706963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15121101424991151531137975 22681652137486727296706963)
            ·
              refine ⟨34022478206230090945060445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22681652137486727296706963 34022478206230090945060445)
              ·
                refine ⟨12758429327336284104397667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34022478206230090945060445 12758429327336284104397667)
                ·
                  refine ⟨19137643991004426156596501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12758429327336284104397667 19137643991004426156596501)
                  ·
                    refine ⟨897077062078332476090461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19137643991004426156596501 897077062078332476090461)
                    ·
                      rfl

theorem cell22_2620577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2620577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620577 prefixEnd_2620577 := by exact prefixLift 2620577
  have htrace : WordTrace (prefixWord ++ tailWord_2620577) baseStart_2620577 baseEnd_2620577 := by
    simpa [prefixWord, tailWord_2620577, baseEnd_2620577] using wordTrace_append hprefix tailTrace_2620577
  have hstable : (prefixWord ++ tailWord_2620577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620577).length < 2 ^ (prefixWord ++ tailWord_2620577).sum := by decide
  have hdescent : baseEnd_2620577 < baseStart_2620577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620581 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 4]
def baseStart_2620581 : Nat := 118140960795 + 2620581 * 2 ^ 59
def prefixEnd_2620581 : Nat := 4983230072969 + 3 ^ 40 * 2620581 * 2
def baseEnd_2620581 : Nat := 299026143786692599663483

theorem tailTrace_2620581 : CollatzResearch.WordTrace tailWord_2620581 prefixEnd_2620581 299026143786692599663483 := by
  unfold tailWord_2620581
  simp only [CollatzResearch.WordTrace]
  refine ⟨95580441319090071447869597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63720294212726714298579731 95580441319090071447869597)
  ·
    refine ⟨35842665494658776792951099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95580441319090071447869597 35842665494658776792951099)
    ·
      refine ⟨53763998241988165189426649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35842665494658776792951099 53763998241988165189426649)
      ·
        refine ⟨40322998681491123892069987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53763998241988165189426649 40322998681491123892069987)
        ·
          refine ⟨60484498022236685838104981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40322998681491123892069987 60484498022236685838104981)
          ·
            refine ⟨2835210844792344648661171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60484498022236685838104981 2835210844792344648661171)
            ·
              refine ⟨4252816267188516972991757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835210844792344648661171 4252816267188516972991757)
              ·
                refine ⟨1594806100195693864871909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4252816267188516972991757 1594806100195693864871909)
                ·
                  refine ⟨299026143786692599663483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1594806100195693864871909 299026143786692599663483)
                  ·
                    rfl

theorem cell22_2620581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_2620581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620581 prefixEnd_2620581 := by exact prefixLift 2620581
  have htrace : WordTrace (prefixWord ++ tailWord_2620581) baseStart_2620581 baseEnd_2620581 := by
    simpa [prefixWord, tailWord_2620581, baseEnd_2620581] using wordTrace_append hprefix tailTrace_2620581
  have hstable : (prefixWord ++ tailWord_2620581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620581).length < 2 ^ (prefixWord ++ tailWord_2620581).sum := by decide
  have hdescent : baseEnd_2620581 < baseStart_2620581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620594 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2620594 : Nat := 118140960795 + 2620594 * 2 ^ 59
def prefixEnd_2620594 : Nat := 4983230072969 + 3 ^ 40 * 2620594 * 2
def baseEnd_2620594 : Nat := 897082881525750098415409

theorem tailTrace_2620594 : CollatzResearch.WordTrace tailWord_2620594 prefixEnd_2620594 897082881525750098415409 := by
  unfold tailWord_2620594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23895228867010743667023209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63720610312028649778728557 23895228867010743667023209)
  ·
    refine ⟨17921421650258057750267407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23895228867010743667023209 17921421650258057750267407)
    ·
      refine ⟨26882132475387086625401111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17921421650258057750267407 26882132475387086625401111)
      ·
        refine ⟨40323198713080629938101667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26882132475387086625401111 40323198713080629938101667)
        ·
          refine ⟨60484798069620944907152501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40323198713080629938101667 60484798069620944907152501)
          ·
            refine ⟨5670449819026963585045547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60484798069620944907152501 5670449819026963585045547)
            ·
              refine ⟨8505674728540445377568321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5670449819026963585045547 8505674728540445377568321)
              ·
                refine ⟨6379256046405334033176241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8505674728540445377568321 6379256046405334033176241)
                ·
                  refine ⟨4784442034804000524882181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379256046405334033176241 4784442034804000524882181)
                  ·
                    refine ⟨897082881525750098415409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784442034804000524882181 897082881525750098415409)
                    ·
                      rfl

theorem cell22_2620594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2620594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620594 prefixEnd_2620594 := by exact prefixLift 2620594
  have htrace : WordTrace (prefixWord ++ tailWord_2620594) baseStart_2620594 baseEnd_2620594 := by
    simpa [prefixWord, tailWord_2620594, baseEnd_2620594] using wordTrace_append hprefix tailTrace_2620594
  have hstable : (prefixWord ++ tailWord_2620594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620594).length < 2 ^ (prefixWord ++ tailWord_2620594).sum := by decide
  have hdescent : baseEnd_2620594 < baseStart_2620594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620609 : List Nat := [1, 2, 6, 1, 1, 1, 1, 9]
def baseStart_2620609 : Nat := 118140960795 + 2620609 * 2 ^ 59
def prefixEnd_2620609 : Nat := 4983230072969 + 3 ^ 40 * 2620609 * 2
def baseEnd_2620609 : Nat := 99676446259143895476707

theorem tailTrace_2620609 : CollatzResearch.WordTrace tailWord_2620609 prefixEnd_2620609 99676446259143895476707 := by
  unfold tailWord_2620609
  simp only [CollatzResearch.WordTrace]
  refine ⟨95581462562988632229888881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63720975041992421486592587 95581462562988632229888881)
  ·
    refine ⟨71686096922241474172416661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95581462562988632229888881 71686096922241474172416661)
    ·
      refine ⟨3360285793230069101832031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71686096922241474172416661 3360285793230069101832031)
      ·
        refine ⟨5040428689845103652748047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360285793230069101832031 5040428689845103652748047)
        ·
          refine ⟨7560643034767655479122071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040428689845103652748047 7560643034767655479122071)
          ·
            refine ⟨11340964552151483218683107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7560643034767655479122071 11340964552151483218683107)
            ·
              refine ⟨17011446828227224828024661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11340964552151483218683107 17011446828227224828024661)
              ·
                refine ⟨99676446259143895476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17011446828227224828024661 99676446259143895476707)
                ·
                  rfl

theorem cell22_2620609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 9].length) (baseStart_2620609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620609 prefixEnd_2620609 := by exact prefixLift 2620609
  have htrace : WordTrace (prefixWord ++ tailWord_2620609) baseStart_2620609 baseEnd_2620609 := by
    simpa [prefixWord, tailWord_2620609, baseEnd_2620609] using wordTrace_append hprefix tailTrace_2620609
  have hstable : (prefixWord ++ tailWord_2620609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620609).length < 2 ^ (prefixWord ++ tailWord_2620609).sum := by decide
  have hdescent : baseEnd_2620609 < baseStart_2620609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620628 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2620628 : Nat := 118140960795 + 2620628 * 2 ^ 59
def prefixEnd_2620628 : Nat := 4983230072969 + 3 ^ 40 * 2620628 * 2
def baseEnd_2620628 : Nat := 897094520420585343065305

theorem tailTrace_2620628 : CollatzResearch.WordTrace tailWord_2620628 prefixEnd_2620628 897094520420585343065305 := by
  unfold tailWord_2620628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47791077774959899237415269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63721437033279865649887025 47791077774959899237415269)
  ·
    refine ⟨8960827082804981107015363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47791077774959899237415269 8960827082804981107015363)
    ·
      refine ⟨13441240624207471660523045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8960827082804981107015363 13441240624207471660523045)
      ·
        refine ⟨2520232617038900936348071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13441240624207471660523045 2520232617038900936348071)
        ·
          refine ⟨3780348925558351404522107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520232617038900936348071 3780348925558351404522107)
          ·
            refine ⟨5670523388337527106783161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780348925558351404522107 5670523388337527106783161)
            ·
              refine ⟨4252892541253145330087371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5670523388337527106783161 4252892541253145330087371)
              ·
                refine ⟨6379338811879717995131057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4252892541253145330087371 6379338811879717995131057)
                ·
                  refine ⟨4784504108909788496348293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6379338811879717995131057 4784504108909788496348293)
                  ·
                    refine ⟨897094520420585343065305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784504108909788496348293 897094520420585343065305)
                    ·
                      rfl

theorem cell22_2620628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2620628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620628 prefixEnd_2620628 := by exact prefixLift 2620628
  have htrace : WordTrace (prefixWord ++ tailWord_2620628) baseStart_2620628 baseEnd_2620628 := by
    simpa [prefixWord, tailWord_2620628, baseEnd_2620628] using wordTrace_append hprefix tailTrace_2620628
  have hstable : (prefixWord ++ tailWord_2620628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620628).length < 2 ^ (prefixWord ++ tailWord_2620628).sum := by decide
  have hdescent : baseEnd_2620628 < baseStart_2620628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620654 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_2620654 : Nat := 118140960795 + 2620654 * 2 ^ 59
def prefixEnd_2620654 : Nat := 4983230072969 + 3 ^ 40 * 2620654 * 2
def baseEnd_2620654 : Nat := 299034473583976647305075

theorem tailTrace_2620654 : CollatzResearch.WordTrace tailWord_2620654 prefixEnd_2620654 299034473583976647305075 := by
  unfold tailWord_2620654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11947887980978200614409627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63722069231883736610184677 11947887980978200614409627)
  ·
    refine ⟨17921831971467300921614441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11947887980978200614409627 17921831971467300921614441)
    ·
      refine ⟨13441373978600475691210831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17921831971467300921614441 13441373978600475691210831)
      ·
        refine ⟨20162060967900713536816247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13441373978600475691210831 20162060967900713536816247)
        ·
          refine ⟨30243091451851070305224371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20162060967900713536816247 30243091451851070305224371)
          ·
            refine ⟨45364637177776605457836557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30243091451851070305224371 45364637177776605457836557)
            ·
              refine ⟨17011738941666227046688709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45364637177776605457836557 17011738941666227046688709)
              ·
                refine ⟨3189701051562417571254133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17011738941666227046688709 3189701051562417571254133)
                ·
                  refine ⟨299034473583976647305075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3189701051562417571254133 299034473583976647305075)
                  ·
                    rfl

theorem cell22_2620654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2620654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620654 prefixEnd_2620654 := by exact prefixLift 2620654
  have htrace : WordTrace (prefixWord ++ tailWord_2620654) baseStart_2620654 baseEnd_2620654 := by
    simpa [prefixWord, tailWord_2620654, baseEnd_2620654] using wordTrace_append hprefix tailTrace_2620654
  have hstable : (prefixWord ++ tailWord_2620654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620654).length < 2 ^ (prefixWord ++ tailWord_2620654).sum := by decide
  have hdescent : baseEnd_2620654 < baseStart_2620654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620660 : List Nat := [2, 6, 1, 2, 1, 2, 1, 7]
def baseStart_2620660 : Nat := 118140960795 + 2620660 * 2 ^ 59
def prefixEnd_2620660 : Nat := 4983230072969 + 3 ^ 40 * 2620660 * 2
def baseEnd_2620660 : Nat := 99678386074949769585023

theorem tailTrace_2620660 : CollatzResearch.WordTrace tailWord_2620660 prefixEnd_2620660 99678386074949769585023 := by
  unfold tailWord_2620660
  simp only [CollatzResearch.WordTrace]
  refine ⟨47791661342901933969997717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63722215123869245293330289 47791661342901933969997717)
  ·
    refine ⟨2240234125448528154843643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47791661342901933969997717 2240234125448528154843643)
    ·
      refine ⟨3360351188172792232265465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240234125448528154843643 3360351188172792232265465)
      ·
        refine ⟨2520263391129594174199099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3360351188172792232265465 2520263391129594174199099)
        ·
          refine ⟨3780395086694391261298649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520263391129594174199099 3780395086694391261298649)
          ·
            refine ⟨2835296315020793445973987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780395086694391261298649 2835296315020793445973987)
            ·
              refine ⟨4252944472531190168960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835296315020793445973987 4252944472531190168960981)
              ·
                refine ⟨99678386074949769585023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4252944472531190168960981 99678386074949769585023)
                ·
                  rfl

theorem cell22_2620660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_2620660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620660 prefixEnd_2620660 := by exact prefixLift 2620660
  have htrace : WordTrace (prefixWord ++ tailWord_2620660) baseStart_2620660 baseEnd_2620660 := by
    simpa [prefixWord, tailWord_2620660, baseEnd_2620660] using wordTrace_append hprefix tailTrace_2620660
  have hstable : (prefixWord ++ tailWord_2620660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620660).length < 2 ^ (prefixWord ++ tailWord_2620660).sum := by decide
  have hdescent : baseEnd_2620660 < baseStart_2620660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620684 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2620684 : Nat := 118140960795 + 2620684 * 2 ^ 59
def prefixEnd_2620684 : Nat := 4983230072969 + 3 ^ 40 * 2620684 * 2
def baseEnd_2620684 : Nat := 897113690365019863665133

theorem tailTrace_2620684 : CollatzResearch.WordTrace tailWord_2620684 prefixEnd_2620684 897113690365019863665133 := by
  unfold tailWord_2620684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47792099018858460019434553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63722798691811280025912737 47792099018858460019434553)
  ·
    refine ⟨35844074264143845014575915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47792099018858460019434553 35844074264143845014575915)
    ·
      refine ⟨53766111396215767521863873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35844074264143845014575915 53766111396215767521863873)
      ·
        refine ⟨40324583547161825641397905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53766111396215767521863873 40324583547161825641397905)
        ·
          refine ⟨30243437660371369231048429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40324583547161825641397905 30243437660371369231048429)
          ·
            refine ⟨11341289122639263461643161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30243437660371369231048429 11341289122639263461643161)
            ·
              refine ⟨8505966841979447596232371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11341289122639263461643161 8505966841979447596232371)
              ·
                refine ⟨12758950262969171394348557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8505966841979447596232371 12758950262969171394348557)
                ·
                  refine ⟨4784606348613439272880709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12758950262969171394348557 4784606348613439272880709)
                  ·
                    refine ⟨897113690365019863665133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4784606348613439272880709 897113690365019863665133)
                    ·
                      rfl

theorem cell22_2620684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2620684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620684 prefixEnd_2620684 := by exact prefixLift 2620684
  have htrace : WordTrace (prefixWord ++ tailWord_2620684) baseStart_2620684 baseEnd_2620684 := by
    simpa [prefixWord, tailWord_2620684, baseEnd_2620684] using wordTrace_append hprefix tailTrace_2620684
  have hstable : (prefixWord ++ tailWord_2620684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620684).length < 2 ^ (prefixWord ++ tailWord_2620684).sum := by decide
  have hdescent : baseEnd_2620684 < baseStart_2620684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620913 : List Nat := [1, 2, 2, 2, 3, 4, 2, 6]
def baseStart_2620913 : Nat := 118140960795 + 2620913 * 2 ^ 59
def prefixEnd_2620913 : Nat := 4983230072969 + 3 ^ 40 * 2620913 * 2
def baseEnd_2620913 : Nat := 99688009082771066632159

theorem tailTrace_2620913 : CollatzResearch.WordTrace tailWord_2620913 prefixEnd_2620913 99688009082771066632159 := by
  unfold tailWord_2620913
  simp only [CollatzResearch.WordTrace]
  refine ⟨95592550353887292148955393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63728366902591528099303595 95592550353887292148955393)
  ·
    refine ⟨71694412765415469111716545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95592550353887292148955393 71694412765415469111716545)
    ·
      refine ⟨53770809574061601833787409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71694412765415469111716545 53770809574061601833787409)
      ·
        refine ⟨40328107180546201375340557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53770809574061601833787409 40328107180546201375340557)
        ·
          refine ⟨15123040192704825515752709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40328107180546201375340557 15123040192704825515752709)
          ·
            refine ⟨2835570036132154784203633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15123040192704825515752709 2835570036132154784203633)
            ·
              refine ⟨2126677527099116088152725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835570036132154784203633 2126677527099116088152725)
              ·
                refine ⟨99688009082771066632159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2126677527099116088152725 99688009082771066632159)
                ·
                  rfl

theorem cell22_2620913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 6].length) (baseStart_2620913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620913 prefixEnd_2620913 := by exact prefixLift 2620913
  have htrace : WordTrace (prefixWord ++ tailWord_2620913) baseStart_2620913 baseEnd_2620913 := by
    simpa [prefixWord, tailWord_2620913, baseEnd_2620913] using wordTrace_append hprefix tailTrace_2620913
  have hstable : (prefixWord ++ tailWord_2620913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620913).length < 2 ^ (prefixWord ++ tailWord_2620913).sum := by decide
  have hdescent : baseEnd_2620913 < baseStart_2620913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2620956 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2620956 : Nat := 118140960795 + 2620956 * 2 ^ 59
def prefixEnd_2620956 : Nat := 4983230072969 + 3 ^ 40 * 2620956 * 2
def baseEnd_2620956 : Nat := 897206801523701820864299

theorem tailTrace_2620956 : CollatzResearch.WordTrace tailWord_2620956 prefixEnd_2620956 897206801523701820864299 := by
  unfold tailWord_2620956
  simp only [CollatzResearch.WordTrace]
  refine ⟨47797059346365755246385361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63729412461821006995180481 47797059346365755246385361)
  ·
    refine ⟨35847794509774316434789021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47797059346365755246385361 35847794509774316434789021)
    ·
      refine ⟨13442922941165368663045883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35847794509774316434789021 13442922941165368663045883)
      ·
        refine ⟨20164384411748052994568825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13442922941165368663045883 20164384411748052994568825)
        ·
          refine ⟨15123288308811039745926619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20164384411748052994568825 15123288308811039745926619)
          ·
            refine ⟨22684932463216559618889929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15123288308811039745926619 22684932463216559618889929)
            ·
              refine ⟨17013699347412419714167447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22684932463216559618889929 17013699347412419714167447)
              ·
                refine ⟨25520549021118629571251171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17013699347412419714167447 25520549021118629571251171)
                ·
                  refine ⟨38280823531677944356876757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25520549021118629571251171 38280823531677944356876757)
                  ·
                    refine ⟨897206801523701820864299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38280823531677944356876757 897206801523701820864299)
                    ·
                      rfl

theorem cell22_2620956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2620956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2620956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2620956 prefixEnd_2620956 := by exact prefixLift 2620956
  have htrace : WordTrace (prefixWord ++ tailWord_2620956) baseStart_2620956 baseEnd_2620956 := by
    simpa [prefixWord, tailWord_2620956, baseEnd_2620956] using wordTrace_append hprefix tailTrace_2620956
  have hstable : (prefixWord ++ tailWord_2620956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2620956).length < 2 ^ (prefixWord ++ tailWord_2620956).sum := by decide
  have hdescent : baseEnd_2620956 < baseStart_2620956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2620956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621016 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2621016 : Nat := 118140960795 + 2621016 * 2 ^ 59
def prefixEnd_2621016 : Nat := 4983230072969 + 3 ^ 40 * 2621016 * 2
def baseEnd_2621016 : Nat := 897227340749881664364115

theorem tailTrace_2621016 : CollatzResearch.WordTrace tailWord_2621016 prefixEnd_2621016 897227340749881664364115 := by
  unfold tailWord_2621016
  simp only [CollatzResearch.WordTrace]
  refine ⟨47798153536257070369977451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63730871381676093826636601 47798153536257070369977451)
  ·
    refine ⟨71697230304385605554966177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47798153536257070369977451 71697230304385605554966177)
    ·
      refine ⟨53772922728289204166224633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71697230304385605554966177 53772922728289204166224633)
      ·
        refine ⟨40329692046216903124668475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53772922728289204166224633 40329692046216903124668475)
        ·
          refine ⟨60494538069325354687002713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40329692046216903124668475 60494538069325354687002713)
          ·
            refine ⟨45370903551994016015252035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60494538069325354687002713 45370903551994016015252035)
            ·
              refine ⟨68056355327991024022878053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45370903551994016015252035 68056355327991024022878053)
              ·
                refine ⟨12760566623998317004289635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68056355327991024022878053 12760566623998317004289635)
                ·
                  refine ⟨19140849935997475506434453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12760566623998317004289635 19140849935997475506434453)
                  ·
                    refine ⟨897227340749881664364115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19140849935997475506434453 897227340749881664364115)
                    ·
                      rfl

theorem cell22_2621016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2621016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621016 prefixEnd_2621016 := by exact prefixLift 2621016
  have htrace : WordTrace (prefixWord ++ tailWord_2621016) baseStart_2621016 baseEnd_2621016 := by
    simpa [prefixWord, tailWord_2621016, baseEnd_2621016] using wordTrace_append hprefix tailTrace_2621016
  have hstable : (prefixWord ++ tailWord_2621016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621016).length < 2 ^ (prefixWord ++ tailWord_2621016).sum := by decide
  have hdescent : baseEnd_2621016 < baseStart_2621016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621031 : List Nat := [1, 1, 5, 1, 1, 1, 2, 10]
def baseStart_2621031 : Nat := 118140960795 + 2621031 * 2 ^ 59
def prefixEnd_2621031 : Nat := 4983230072969 + 3 ^ 40 * 2621031 * 2
def baseEnd_2621031 : Nat := 99692497284047402804341

theorem tailTrace_2621031 : CollatzResearch.WordTrace tailWord_2621031 prefixEnd_2621031 99692497284047402804341 := by
  unfold tailWord_2621031
  simp only [CollatzResearch.WordTrace]
  refine ⟨95596854167459798301750947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63731236111639865534500631 95596854167459798301750947)
  ·
    refine ⟨143395281251189697452626421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95596854167459798301750947 143395281251189697452626421)
    ·
      refine ⟨13443307617299034136183727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143395281251189697452626421 13443307617299034136183727)
      ·
        refine ⟨20164961425948551204275591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13443307617299034136183727 20164961425948551204275591)
        ·
          refine ⟨30247442138922826806413387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20164961425948551204275591 30247442138922826806413387)
          ·
            refine ⟨45371163208384240209620081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30247442138922826806413387 45371163208384240209620081)
            ·
              refine ⟨34028372406288180157215061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45371163208384240209620081 34028372406288180157215061)
              ·
                refine ⟨99692497284047402804341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34028372406288180157215061 99692497284047402804341)
                ·
                  rfl

theorem cell22_2621031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 10].length) (baseStart_2621031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621031 prefixEnd_2621031 := by exact prefixLift 2621031
  have htrace : WordTrace (prefixWord ++ tailWord_2621031) baseStart_2621031 baseEnd_2621031 := by
    simpa [prefixWord, tailWord_2621031, baseEnd_2621031] using wordTrace_append hprefix tailTrace_2621031
  have hstable : (prefixWord ++ tailWord_2621031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621031).length < 2 ^ (prefixWord ++ tailWord_2621031).sum := by decide
  have hdescent : baseEnd_2621031 < baseStart_2621031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621033 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_2621033 : Nat := 118140960795 + 2621033 * 2 ^ 59
def prefixEnd_2621033 : Nat := 4983230072969 + 3 ^ 40 * 2621033 * 2
def baseEnd_2621033 : Nat := 897233160197299286689063

theorem tailTrace_2621033 : CollatzResearch.WordTrace tailWord_2621033 prefixEnd_2621033 897233160197299286689063 := by
  unfold tailWord_2621033
  simp only [CollatzResearch.WordTrace]
  refine ⟨95596927113452552643323753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63731284742301701762215835 95596927113452552643323753)
  ·
    refine ⟨71697695335089414482492815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95596927113452552643323753 71697695335089414482492815)
    ·
      refine ⟨107546543002634121723739223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71697695335089414482492815 107546543002634121723739223)
      ·
        refine ⟨161319814503951182585608835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107546543002634121723739223 161319814503951182585608835)
        ·
          refine ⟨241979721755926773878413253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161319814503951182585608835 241979721755926773878413253)
          ·
            refine ⟨45371197829236270102202485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241979721755926773878413253 45371197829236270102202485)
            ·
              refine ⟨4253549796490900322081483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45371197829236270102202485 4253549796490900322081483)
              ·
                refine ⟨6380324694736350483122225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253549796490900322081483 6380324694736350483122225)
                ·
                  refine ⟨4785243521052262862341669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6380324694736350483122225 4785243521052262862341669)
                  ·
                    refine ⟨897233160197299286689063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785243521052262862341669 897233160197299286689063)
                    ·
                      rfl

theorem cell22_2621033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_2621033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621033 prefixEnd_2621033 := by exact prefixLift 2621033
  have htrace : WordTrace (prefixWord ++ tailWord_2621033) baseStart_2621033 baseEnd_2621033 := by
    simpa [prefixWord, tailWord_2621033, baseEnd_2621033] using wordTrace_append hprefix tailTrace_2621033
  have hstable : (prefixWord ++ tailWord_2621033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621033).length < 2 ^ (prefixWord ++ tailWord_2621033).sum := by decide
  have hdescent : baseEnd_2621033 < baseStart_2621033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621037 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2621037 : Nat := 118140960795 + 2621037 * 2 ^ 59
def prefixEnd_2621037 : Nat := 4983230072969 + 3 ^ 40 * 2621037 * 2
def baseEnd_2621037 : Nat := 299078176493014869863017

theorem tailTrace_2621037 : CollatzResearch.WordTrace tailWord_2621037 prefixEnd_2621037 299078176493014869863017 := by
  unfold tailWord_2621037
  simp only [CollatzResearch.WordTrace]
  refine ⟨95597073005438061326469365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63731382003625374217646243 95597073005438061326469365)
  ·
    refine ⟨8962225594259818249356503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95597073005438061326469365 8962225594259818249356503)
    ·
      refine ⟨13443338391389727374034755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8962225594259818249356503 13443338391389727374034755)
      ·
        refine ⟨20165007587084591061052133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13443338391389727374034755 20165007587084591061052133)
        ·
          refine ⟨3780938922578360823947275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20165007587084591061052133 3780938922578360823947275)
          ·
            refine ⟨5671408383867541235920913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780938922578360823947275 5671408383867541235920913)
            ·
              refine ⟨4253556287900655926940685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671408383867541235920913 4253556287900655926940685)
              ·
                refine ⟨1595083607962745972602757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4253556287900655926940685 1595083607962745972602757)
                ·
                  refine ⟨299078176493014869863017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595083607962745972602757 299078176493014869863017)
                  ·
                    rfl

theorem cell22_2621037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2621037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621037 prefixEnd_2621037 := by exact prefixLift 2621037
  have htrace : WordTrace (prefixWord ++ tailWord_2621037) baseStart_2621037 baseEnd_2621037 := by
    simpa [prefixWord, tailWord_2621037, baseEnd_2621037] using wordTrace_append hprefix tailTrace_2621037
  have hstable : (prefixWord ++ tailWord_2621037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621037).length < 2 ^ (prefixWord ++ tailWord_2621037).sum := by decide
  have hdescent : baseEnd_2621037 < baseStart_2621037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621080 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_2621080 : Nat := 118140960795 + 2621080 * 2 ^ 59
def prefixEnd_2621080 : Nat := 4983230072969 + 3 ^ 40 * 2621080 * 2
def baseEnd_2621080 : Nat := 897249249257806830763919

theorem tailTrace_2621080 : CollatzResearch.WordTrace tailWord_2621080 prefixEnd_2621080 897249249257806830763919 := by
  unfold tailWord_2621080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47799320672141139835142347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63732427562854853113523129 47799320672141139835142347)
  ·
    refine ⟨71698981008211709752713521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47799320672141139835142347 71698981008211709752713521)
    ·
      refine ⟨53774235756158782314535141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71698981008211709752713521 53774235756158782314535141)
      ·
        refine ⟨10082669204279771683975339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53774235756158782314535141 10082669204279771683975339)
        ·
          refine ⟨15124003806419657525963009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10082669204279771683975339 15124003806419657525963009)
          ·
            refine ⟨11343002854814743144472257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15124003806419657525963009 11343002854814743144472257)
            ·
              refine ⟨8507252141111057358354193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11343002854814743144472257 8507252141111057358354193)
              ·
                refine ⟨6380439105833293018765645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8507252141111057358354193 6380439105833293018765645)
                ·
                  refine ⟨2392664664687484882037117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6380439105833293018765645 2392664664687484882037117)
                  ·
                    refine ⟨897249249257806830763919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392664664687484882037117 897249249257806830763919)
                    ·
                      rfl

theorem cell22_2621080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_2621080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621080 prefixEnd_2621080 := by exact prefixLift 2621080
  have htrace : WordTrace (prefixWord ++ tailWord_2621080) baseStart_2621080 baseEnd_2621080 := by
    simpa [prefixWord, tailWord_2621080, baseEnd_2621080] using wordTrace_append hprefix tailTrace_2621080
  have hstable : (prefixWord ++ tailWord_2621080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621080).length < 2 ^ (prefixWord ++ tailWord_2621080).sum := by decide
  have hdescent : baseEnd_2621080 < baseStart_2621080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621114 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_2621114 : Nat := 118140960795 + 2621114 * 2 ^ 59
def prefixEnd_2621114 : Nat := 4983230072969 + 3 ^ 40 * 2621114 * 2
def baseEnd_2621114 : Nat := 897260888152642075413815

theorem tailTrace_2621114 : CollatzResearch.WordTrace tailWord_2621114 prefixEnd_2621114 897260888152642075413815 := by
  unfold tailWord_2621114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23899970356539775869255599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63733254284106068984681597 23899970356539775869255599)
  ·
    refine ⟨35849955534809663803883399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23899970356539775869255599 35849955534809663803883399)
    ·
      refine ⟨53774933302214495705825099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35849955534809663803883399 53774933302214495705825099)
      ·
        refine ⟨80662399953321743558737649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53774933302214495705825099 80662399953321743558737649)
        ·
          refine ⟨60496799964991307669053237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80662399953321743558737649 60496799964991307669053237)
          ·
            refine ⟨5671574996717935093973741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60496799964991307669053237 5671574996717935093973741)
            ·
              refine ⟨2126840623769225660240153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5671574996717935093973741 2126840623769225660240153)
              ·
                refine ⟨1595130467826919245180115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2126840623769225660240153 1595130467826919245180115)
                ·
                  refine ⟨2392695701740378867770173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595130467826919245180115 2392695701740378867770173)
                  ·
                    refine ⟨897260888152642075413815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392695701740378867770173 897260888152642075413815)
                    ·
                      rfl

theorem cell22_2621114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_2621114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621114 prefixEnd_2621114 := by exact prefixLift 2621114
  have htrace : WordTrace (prefixWord ++ tailWord_2621114) baseStart_2621114 baseEnd_2621114 := by
    simpa [prefixWord, tailWord_2621114, baseEnd_2621114] using wordTrace_append hprefix tailTrace_2621114
  have hstable : (prefixWord ++ tailWord_2621114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621114).length < 2 ^ (prefixWord ++ tailWord_2621114).sum := by decide
  have hdescent : baseEnd_2621114 < baseStart_2621114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621157 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_2621157 : Nat := 118140960795 + 2621157 * 2 ^ 59
def prefixEnd_2621157 : Nat := 4983230072969 + 3 ^ 40 * 2621157 * 2
def baseEnd_2621157 : Nat := 897275607931404296588683

theorem tailTrace_2621157 : CollatzResearch.WordTrace tailWord_2621157 prefixEnd_2621157 897275607931404296588683 := by
  unfold tailWord_2621157
  simp only [CollatzResearch.WordTrace]
  refine ⟨95601449765003321820837725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63734299843335547880558483 95601449765003321820837725)
  ·
    refine ⟨35850543661876245682814147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95601449765003321820837725 35850543661876245682814147)
    ·
      refine ⟨53775815492814368524221221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35850543661876245682814147 53775815492814368524221221)
      ·
        refine ⟨10082965404902694098291479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53775815492814368524221221 10082965404902694098291479)
        ·
          refine ⟨15124448107354041147437219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10082965404902694098291479 15124448107354041147437219)
          ·
            refine ⟨22686672161031061721155829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124448107354041147437219 22686672161031061721155829)
            ·
              refine ⟨2126875515096662036358359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22686672161031061721155829 2126875515096662036358359)
              ·
                refine ⟨3190313272644993054537539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126875515096662036358359 3190313272644993054537539)
                ·
                  refine ⟨4785469908967489581806309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190313272644993054537539 4785469908967489581806309)
                  ·
                    refine ⟨897275607931404296588683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785469908967489581806309 897275607931404296588683)
                    ·
                      rfl

theorem cell22_2621157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_2621157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621157 prefixEnd_2621157 := by exact prefixLift 2621157
  have htrace : WordTrace (prefixWord ++ tailWord_2621157) baseStart_2621157 baseEnd_2621157 := by
    simpa [prefixWord, tailWord_2621157, baseEnd_2621157] using wordTrace_append hprefix tailTrace_2621157
  have hstable : (prefixWord ++ tailWord_2621157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621157).length < 2 ^ (prefixWord ++ tailWord_2621157).sum := by decide
  have hdescent : baseEnd_2621157 < baseStart_2621157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621168 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_2621168 : Nat := 118140960795 + 2621168 * 2 ^ 59
def prefixEnd_2621168 : Nat := 4983230072969 + 3 ^ 40 * 2621168 * 2
def baseEnd_2621168 : Nat := 897279373456203934563649

theorem tailTrace_2621168 : CollatzResearch.WordTrace tailWord_2621168 prefixEnd_2621168 897279373456203934563649 := by
  unfold tailWord_2621168
  simp only [CollatzResearch.WordTrace]
  refine ⟨47800925483981735349744079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63734567311975647132992105 47800925483981735349744079)
  ·
    refine ⟨71701388225972603024616119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47800925483981735349744079 71701388225972603024616119)
    ·
      refine ⟨107552082338958904536924179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71701388225972603024616119 107552082338958904536924179)
      ·
        refine ⟨161328123508438356805386269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107552082338958904536924179 161328123508438356805386269)
        ·
          refine ⟨60498046315664383802019851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161328123508438356805386269 60498046315664383802019851)
          ·
            refine ⟨90747069473496575703029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60498046315664383802019851 90747069473496575703029777)
            ·
              refine ⟨68060302105122431777272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90747069473496575703029777 68060302105122431777272333)
              ·
                refine ⟨25522613289420911916477125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68060302105122431777272333 25522613289420911916477125)
                ·
                  refine ⟨4785489991766420984339461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25522613289420911916477125 4785489991766420984339461)
                  ·
                    refine ⟨897279373456203934563649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4785489991766420984339461 897279373456203934563649)
                    ·
                      rfl

theorem cell22_2621168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_2621168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621168 prefixEnd_2621168 := by exact prefixLift 2621168
  have htrace : WordTrace (prefixWord ++ tailWord_2621168) baseStart_2621168 baseEnd_2621168 := by
    simpa [prefixWord, tailWord_2621168, baseEnd_2621168] using wordTrace_append hprefix tailTrace_2621168
  have hstable : (prefixWord ++ tailWord_2621168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621168).length < 2 ^ (prefixWord ++ tailWord_2621168).sum := by decide
  have hdescent : baseEnd_2621168 < baseStart_2621168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621183 : List Nat := [1, 1, 2, 2, 1, 3, 5, 7]
def baseStart_2621183 : Nat := 118140960795 + 2621183 * 2 ^ 59
def prefixEnd_2621183 : Nat := 4983230072969 + 3 ^ 40 * 2621183 * 2
def baseEnd_2621183 : Nat := 99698278695860988382067

theorem tailTrace_2621183 : CollatzResearch.WordTrace tailWord_2621183 prefixEnd_2621183 99698278695860988382067 := by
  unfold tailWord_2621183
  simp only [CollatzResearch.WordTrace]
  refine ⟨95602398062909128261284203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63734932041939418840856135 95602398062909128261284203)
  ·
    refine ⟨143403597094363692391926305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95602398062909128261284203 143403597094363692391926305)
    ·
      refine ⟨107552697820772769293944729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143403597094363692391926305 107552697820772769293944729)
      ·
        refine ⟨80664523365579576970458547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107552697820772769293944729 80664523365579576970458547)
        ·
          refine ⟨120996785048369365455687821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80664523365579576970458547 120996785048369365455687821)
          ·
            refine ⟨45373794393138512045882933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120996785048369365455687821 45373794393138512045882933)
            ·
              refine ⟨4253793224356735504301525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45373794393138512045882933 4253793224356735504301525)
              ·
                refine ⟨99698278695860988382067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4253793224356735504301525 99698278695860988382067)
                ·
                  rfl

theorem cell22_2621183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 7].length) (baseStart_2621183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621183 prefixEnd_2621183 := by exact prefixLift 2621183
  have htrace : WordTrace (prefixWord ++ tailWord_2621183) baseStart_2621183 baseEnd_2621183 := by
    simpa [prefixWord, tailWord_2621183, baseEnd_2621183] using wordTrace_append hprefix tailTrace_2621183
  have hstable : (prefixWord ++ tailWord_2621183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621183).length < 2 ^ (prefixWord ++ tailWord_2621183).sum := by decide
  have hdescent : baseEnd_2621183 < baseStart_2621183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621202 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2621202 : Nat := 118140960795 + 2621202 * 2 ^ 59
def prefixEnd_2621202 : Nat := 4983230072969 + 3 ^ 40 * 2621202 * 2
def baseEnd_2621202 : Nat := 897291012351039179213545

theorem tailTrace_2621202 : CollatzResearch.WordTrace tailWord_2621202 prefixEnd_2621202 897291012351039179213545 := by
  unfold tailWord_2621202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23900772762460073626556465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63735394033226863004150573 23900772762460073626556465)
  ·
    refine ⟨17925579571845055219917349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23900772762460073626556465 17925579571845055219917349)
    ·
      refine ⟨3361046169720947853734503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17925579571845055219917349 3361046169720947853734503)
      ·
        refine ⟨5041569254581421780601755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361046169720947853734503 5041569254581421780601755)
        ·
          refine ⟨7562353881872132670902633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5041569254581421780601755 7562353881872132670902633)
          ·
            refine ⟨5671765411404099503176975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7562353881872132670902633 5671765411404099503176975)
            ·
              refine ⟨8507648117106149254765463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5671765411404099503176975 8507648117106149254765463)
              ·
                refine ⟨12761472175659223882148195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8507648117106149254765463 12761472175659223882148195)
                ·
                  refine ⟨19142208263488835823222293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12761472175659223882148195 19142208263488835823222293)
                  ·
                    refine ⟨897291012351039179213545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19142208263488835823222293 897291012351039179213545)
                    ·
                      rfl

theorem cell22_2621202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2621202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621202 prefixEnd_2621202 := by exact prefixLift 2621202
  have htrace : WordTrace (prefixWord ++ tailWord_2621202) baseStart_2621202 baseEnd_2621202 := by
    simpa [prefixWord, tailWord_2621202, baseEnd_2621202] using wordTrace_append hprefix tailTrace_2621202
  have hstable : (prefixWord ++ tailWord_2621202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621202).length < 2 ^ (prefixWord ++ tailWord_2621202).sum := by decide
  have hdescent : baseEnd_2621202 < baseStart_2621202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621215 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 5, 3]
def baseStart_2621215 : Nat := 118140960795 + 2621215 * 2 ^ 59
def prefixEnd_2621215 : Nat := 4983230072969 + 3 ^ 40 * 2621215 * 2
def baseEnd_2621215 : Nat := 897295462516711478638505

theorem tailTrace_2621215 : CollatzResearch.WordTrace tailWord_2621215 prefixEnd_2621215 897295462516711478638505 := by
  unfold tailWord_2621215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95603565198793197726449099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63735710132528798484299399 95603565198793197726449099)
  ·
    refine ⟨143405347798189796589673649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95603565198793197726449099 143405347798189796589673649)
    ·
      refine ⟨107554010848642347442255237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143405347798189796589673649 107554010848642347442255237)
      ·
        refine ⟨20166377034120440145422857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107554010848642347442255237 20166377034120440145422857)
        ·
          refine ⟨15124782775590330109067143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20166377034120440145422857 15124782775590330109067143)
          ·
            refine ⟨22687174163385495163600715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15124782775590330109067143 22687174163385495163600715)
            ·
              refine ⟨34030761245078242745401073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22687174163385495163600715 34030761245078242745401073)
              ·
                refine ⟨25523070933808682059050805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34030761245078242745401073 25523070933808682059050805)
                ·
                  refine ⟨2392787900044563943036013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25523070933808682059050805 2392787900044563943036013)
                  ·
                    refine ⟨897295462516711478638505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392787900044563943036013 897295462516711478638505)
                    ·
                      rfl

theorem cell22_2621215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_2621215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621215 prefixEnd_2621215 := by exact prefixLift 2621215
  have htrace : WordTrace (prefixWord ++ tailWord_2621215) baseStart_2621215 baseEnd_2621215 := by
    simpa [prefixWord, tailWord_2621215, baseEnd_2621215] using wordTrace_append hprefix tailTrace_2621215
  have hstable : (prefixWord ++ tailWord_2621215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621215).length < 2 ^ (prefixWord ++ tailWord_2621215).sum := by decide
  have hdescent : baseEnd_2621215 < baseStart_2621215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621266 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2621266 : Nat := 118140960795 + 2621266 * 2 ^ 59
def prefixEnd_2621266 : Nat := 4983230072969 + 3 ^ 40 * 2621266 * 2
def baseEnd_2621266 : Nat := 897312920858964345613349

theorem tailTrace_2621266 : CollatzResearch.WordTrace tailWord_2621266 prefixEnd_2621266 897312920858964345613349 := by
  unfold tailWord_2621266
  simp only [CollatzResearch.WordTrace]
  refine ⟨23901356330402108359138913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63736950214405622291037101 23901356330402108359138913)
  ·
    refine ⟨17926017247801581269354185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23901356330402108359138913 17926017247801581269354185)
    ·
      refine ⟨13444512935851185952015639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17926017247801581269354185 13444512935851185952015639)
      ·
        refine ⟨20166769403776778928023459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444512935851185952015639 20166769403776778928023459)
        ·
          refine ⟨30250154105665168392035189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20166769403776778928023459 30250154105665168392035189)
          ·
            refine ⟨2835951947406109536753299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30250154105665168392035189 2835951947406109536753299)
            ·
              refine ⟨4253927921109164305129949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835951947406109536753299 4253927921109164305129949)
              ·
                refine ⟨1595222970415936614423731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4253927921109164305129949 1595222970415936614423731)
                ·
                  refine ⟨2392834455623904921635597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595222970415936614423731 2392834455623904921635597)
                  ·
                    refine ⟨897312920858964345613349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392834455623904921635597 897312920858964345613349)
                    ·
                      rfl

theorem cell22_2621266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2621266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621266 prefixEnd_2621266 := by exact prefixLift 2621266
  have htrace : WordTrace (prefixWord ++ tailWord_2621266) baseStart_2621266 baseEnd_2621266 := by
    simpa [prefixWord, tailWord_2621266, baseEnd_2621266] using wordTrace_append hprefix tailTrace_2621266
  have hstable : (prefixWord ++ tailWord_2621266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621266).length < 2 ^ (prefixWord ++ tailWord_2621266).sum := by decide
  have hdescent : baseEnd_2621266 < baseStart_2621266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621305 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_2621305 : Nat := 118140960795 + 2621305 * 2 ^ 59
def prefixEnd_2621305 : Nat := 4983230072969 + 3 ^ 40 * 2621305 * 2
def baseEnd_2621305 : Nat := 897326271355981243888229

theorem tailTrace_2621305 : CollatzResearch.WordTrace tailWord_2621305 prefixEnd_2621305 897326271355981243888229 := by
  unfold tailWord_2621305
  simp only [CollatzResearch.WordTrace]
  refine ⟨95606847768467143097225369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63737898512311428731483579 95606847768467143097225369)
  ·
    refine ⟨71705135826350357322919027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95606847768467143097225369 71705135826350357322919027)
    ·
      refine ⟨107557703739525535984378541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71705135826350357322919027 107557703739525535984378541)
      ·
        refine ⟨40334138902322075994141953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107557703739525535984378541 40334138902322075994141953)
        ·
          refine ⟨30250604176741556995606465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40334138902322075994141953 30250604176741556995606465)
          ·
            refine ⟨22687953132556167746704849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30250604176741556995606465 22687953132556167746704849)
            ·
              refine ⟨17015964849417125810028637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22687953132556167746704849 17015964849417125810028637)
              ·
                refine ⟨6380986818531422178760739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17015964849417125810028637 6380986818531422178760739)
                ·
                  refine ⟨9571480227797133268141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380986818531422178760739 9571480227797133268141109)
                  ·
                    refine ⟨897326271355981243888229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9571480227797133268141109 897326271355981243888229)
                    ·
                      rfl

theorem cell22_2621305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_2621305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621305 prefixEnd_2621305 := by exact prefixLift 2621305
  have htrace : WordTrace (prefixWord ++ tailWord_2621305) baseStart_2621305 baseEnd_2621305 := by
    simpa [prefixWord, tailWord_2621305, baseEnd_2621305] using wordTrace_append hprefix tailTrace_2621305
  have hstable : (prefixWord ++ tailWord_2621305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621305).length < 2 ^ (prefixWord ++ tailWord_2621305).sum := by decide
  have hdescent : baseEnd_2621305 < baseStart_2621305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621334 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2621334 : Nat := 118140960795 + 2621334 * 2 ^ 59
def prefixEnd_2621334 : Nat := 4983230072969 + 3 ^ 40 * 2621334 * 2
def baseEnd_2621334 : Nat := 897336198648634834913141

theorem tailTrace_2621334 : CollatzResearch.WordTrace tailWord_2621334 prefixEnd_2621334 897336198648634834913141 := by
  unfold tailWord_2621334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975494092835130065626941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63738603656908054033354037 5975494092835130065626941)
  ·
    refine ⟨2240810284813173774610103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5975494092835130065626941 2240810284813173774610103)
    ·
      refine ⟨3361215427219760661915155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240810284813173774610103 3361215427219760661915155)
      ·
        refine ⟨5041823140829640992872733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361215427219760661915155 5041823140829640992872733)
        ·
          refine ⟨1890683677811115372327275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5041823140829640992872733 1890683677811115372327275)
          ·
            refine ⟨2836025516716673058490913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890683677811115372327275 2836025516716673058490913)
            ·
              refine ⟨2127019137537504793868185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836025516716673058490913 2127019137537504793868185)
              ·
                refine ⟨1595264353153128595401139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127019137537504793868185 1595264353153128595401139)
                ·
                  refine ⟨2392896529729692893101709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595264353153128595401139 2392896529729692893101709)
                  ·
                    refine ⟨897336198648634834913141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2392896529729692893101709 897336198648634834913141)
                    ·
                      rfl

theorem cell22_2621334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2621334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621334 prefixEnd_2621334 := by exact prefixLift 2621334
  have htrace : WordTrace (prefixWord ++ tailWord_2621334) baseStart_2621334 baseEnd_2621334 := by
    simpa [prefixWord, tailWord_2621334, baseEnd_2621334] using wordTrace_append hprefix tailTrace_2621334
  have hstable : (prefixWord ++ tailWord_2621334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621334).length < 2 ^ (prefixWord ++ tailWord_2621334).sum := by decide
  have hdescent : baseEnd_2621334 < baseStart_2621334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621341 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 4]
def baseStart_2621341 : Nat := 118140960795 + 2621341 * 2 ^ 59
def prefixEnd_2621341 : Nat := 4983230072969 + 3 ^ 40 * 2621341 * 2
def baseEnd_2621341 : Nat := 299112864963896383329373

theorem tailTrace_2621341 : CollatzResearch.WordTrace tailWord_2621341 prefixEnd_2621341 299112864963896383329373 := by
  unfold tailWord_2621341
  simp only [CollatzResearch.WordTrace]
  refine ⟨95608160796336721245535877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63738773864224480830357251 95608160796336721245535877)
  ·
    refine ⟨17926530149313135233537977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95608160796336721245535877 17926530149313135233537977)
    ·
      refine ⟨13444897611984851425153483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17926530149313135233537977 13444897611984851425153483)
      ·
        refine ⟨20167346417977277137730225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13444897611984851425153483 20167346417977277137730225)
        ·
          refine ⟨15125509813482957853297669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20167346417977277137730225 15125509813482957853297669)
          ·
            refine ⟨2836033090028054597493313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15125509813482957853297669 2836033090028054597493313)
            ·
              refine ⟨2127024817521040948119985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836033090028054597493313 2127024817521040948119985)
              ·
                refine ⟨1595268613140780711089989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127024817521040948119985 1595268613140780711089989)
                ·
                  refine ⟨299112864963896383329373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595268613140780711089989 299112864963896383329373)
                  ·
                    rfl

theorem cell22_2621341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_2621341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621341 prefixEnd_2621341 := by exact prefixLift 2621341
  have htrace : WordTrace (prefixWord ++ tailWord_2621341) baseStart_2621341 baseEnd_2621341 := by
    simpa [prefixWord, tailWord_2621341, baseEnd_2621341] using wordTrace_append hprefix tailTrace_2621341
  have hstable : (prefixWord ++ tailWord_2621341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621341).length < 2 ^ (prefixWord ++ tailWord_2621341).sum := by decide
  have hdescent : baseEnd_2621341 < baseStart_2621341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621397 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 7]
def baseStart_2621397 : Nat := 118140960795 + 2621397 * 2 ^ 59
def prefixEnd_2621397 : Nat := 4983230072969 + 3 ^ 40 * 2621397 * 2
def baseEnd_2621397 : Nat := 299119254945374556862649

theorem tailTrace_2621397 : CollatzResearch.WordTrace tailWord_2621397 prefixEnd_2621397 299119254945374556862649 := by
  unfold tailWord_2621397
  simp only [CollatzResearch.WordTrace]
  refine ⟨95610203284133842809574445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63740135522755895206382963 95610203284133842809574445)
  ·
    refine ⟨35853826231550191053590417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95610203284133842809574445 35853826231550191053590417)
    ·
      refine ⟨26890369673662643290192813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35853826231550191053590417 26890369673662643290192813)
      ·
        refine ⟨10083888627623491233822305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26890369673662643290192813 10083888627623491233822305)
        ·
          refine ⟨7562916470717618425366729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10083888627623491233822305 7562916470717618425366729)
          ·
            refine ⟨5672187353038213819025047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7562916470717618425366729 5672187353038213819025047)
            ·
              refine ⟨8508281029557320728537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672187353038213819025047 8508281029557320728537571)
              ·
                refine ⟨12762421544335981092806357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8508281029557320728537571 12762421544335981092806357)
                ·
                  refine ⟨299119254945374556862649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12762421544335981092806357 299119254945374556862649)
                  ·
                    rfl

theorem cell22_2621397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_2621397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621397 prefixEnd_2621397 := by exact prefixLift 2621397
  have htrace : WordTrace (prefixWord ++ tailWord_2621397) baseStart_2621397 baseEnd_2621397 := by
    simpa [prefixWord, tailWord_2621397, baseEnd_2621397] using wordTrace_append hprefix tailTrace_2621397
  have hstable : (prefixWord ++ tailWord_2621397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621397).length < 2 ^ (prefixWord ++ tailWord_2621397).sum := by decide
  have hdescent : baseEnd_2621397 < baseStart_2621397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621489 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2621489 : Nat := 118140960795 + 2621489 * 2 ^ 59
def prefixEnd_2621489 : Nat := 4983230072969 + 3 ^ 40 * 2621489 * 2
def baseEnd_2621489 : Nat := 897389258316266097287665

theorem tailTrace_2621489 : CollatzResearch.WordTrace tailWord_2621489 prefixEnd_2621489 897389258316266097287665 := by
  unfold tailWord_2621489
  simp only [CollatzResearch.WordTrace]
  refine ⟨95613558799800542521923521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63742372533200361681282347 95613558799800542521923521)
  ·
    refine ⟨71710169099850406891442641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95613558799800542521923521 71710169099850406891442641)
    ·
      refine ⟨53782626824887805168581981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71710169099850406891442641 53782626824887805168581981)
      ·
        refine ⟨20168485059332926938218243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53782626824887805168581981 20168485059332926938218243)
        ·
          refine ⟨30252727588999390407327365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20168485059332926938218243 30252727588999390407327365)
          ·
            refine ⟨5672386422937385701373881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30252727588999390407327365 5672386422937385701373881)
            ·
              refine ⟨4254289817203039276030411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5672386422937385701373881 4254289817203039276030411)
              ·
                refine ⟨6381434725804558914045617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254289817203039276030411 6381434725804558914045617)
                ·
                  refine ⟨4786076044353419185534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6381434725804558914045617 4786076044353419185534213)
                  ·
                    refine ⟨897389258316266097287665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786076044353419185534213 897389258316266097287665)
                    ·
                      rfl

theorem cell22_2621489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2621489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621489 prefixEnd_2621489 := by exact prefixLift 2621489
  have htrace : WordTrace (prefixWord ++ tailWord_2621489) baseStart_2621489 baseEnd_2621489 := by
    simpa [prefixWord, tailWord_2621489, baseEnd_2621489] using wordTrace_append hprefix tailTrace_2621489
  have hstable : (prefixWord ++ tailWord_2621489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621489).length < 2 ^ (prefixWord ++ tailWord_2621489).sum := by decide
  have hdescent : baseEnd_2621489 < baseStart_2621489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621596 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_2621596 : Nat := 118140960795 + 2621596 * 2 ^ 59
def prefixEnd_2621596 : Nat := 4983230072969 + 3 ^ 40 * 2621596 * 2
def baseEnd_2621596 : Nat := 897425886602953484862337

theorem tailTrace_2621596 : CollatzResearch.WordTrace tailWord_2621596 prefixEnd_2621596 897425886602953484862337 := by
  unfold tailWord_2621596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47808730705206449898034321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63744974273608599864045761 47808730705206449898034321)
  ·
    refine ⟨35856548028904837423525741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47808730705206449898034321 35856548028904837423525741)
    ·
      refine ⟨13446205510839314033822153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35856548028904837423525741 13446205510839314033822153)
      ·
        refine ⟨10084654133129485525366615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13446205510839314033822153 10084654133129485525366615)
        ·
          refine ⟨15126981199694228288049923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084654133129485525366615 15126981199694228288049923)
          ·
            refine ⟨22690471799541342432074885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15126981199694228288049923 22690471799541342432074885)
            ·
              refine ⟨4254463462414001706014041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22690471799541342432074885 4254463462414001706014041)
              ·
                refine ⟨3190847596810501279510531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254463462414001706014041 3190847596810501279510531)
                ·
                  refine ⟨4786271395215751919265797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190847596810501279510531 4786271395215751919265797)
                  ·
                    refine ⟨897425886602953484862337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786271395215751919265797 897425886602953484862337)
                    ·
                      rfl

theorem cell22_2621596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_2621596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621596 prefixEnd_2621596 := by exact prefixLift 2621596
  have htrace : WordTrace (prefixWord ++ tailWord_2621596) baseStart_2621596 baseEnd_2621596 := by
    simpa [prefixWord, tailWord_2621596, baseEnd_2621596] using wordTrace_append hprefix tailTrace_2621596
  have hstable : (prefixWord ++ tailWord_2621596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621596).length < 2 ^ (prefixWord ++ tailWord_2621596).sum := by decide
  have hdescent : baseEnd_2621596 < baseStart_2621596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621624 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_2621624 : Nat := 118140960795 + 2621624 * 2 ^ 59
def prefixEnd_2621624 : Nat := 4983230072969 + 3 ^ 40 * 2621624 * 2
def baseEnd_2621624 : Nat := 897435471575170745162251

theorem tailTrace_2621624 : CollatzResearch.WordTrace tailWord_2621624 prefixEnd_2621624 897435471575170745162251 := by
  unfold tailWord_2621624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47809241327155730289043963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63745655102874307052058617 47809241327155730289043963)
  ·
    refine ⟨71713861990733595433565945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47809241327155730289043963 71713861990733595433565945)
    ·
      refine ⟨53785396493050196575174459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71713861990733595433565945 53785396493050196575174459)
      ·
        refine ⟨80678094739575294862761689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53785396493050196575174459 80678094739575294862761689)
        ·
          refine ⟨60508571054681471147071267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80678094739575294862761689 60508571054681471147071267)
          ·
            refine ⟨90762856582022206720606901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60508571054681471147071267 90762856582022206720606901)
            ·
              refine ⟨8509017804564581880056897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90762856582022206720606901 8509017804564581880056897)
              ·
                refine ⟨6381763353423436410042673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8509017804564581880056897 6381763353423436410042673)
                ·
                  refine ⟨4786322515067577307532005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6381763353423436410042673 4786322515067577307532005)
                  ·
                    refine ⟨897435471575170745162251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786322515067577307532005 897435471575170745162251)
                    ·
                      rfl

theorem cell22_2621624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_2621624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621624 prefixEnd_2621624 := by exact prefixLift 2621624
  have htrace : WordTrace (prefixWord ++ tailWord_2621624) baseStart_2621624 baseEnd_2621624 := by
    simpa [prefixWord, tailWord_2621624, baseEnd_2621624] using wordTrace_append hprefix tailTrace_2621624
  have hstable : (prefixWord ++ tailWord_2621624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621624).length < 2 ^ (prefixWord ++ tailWord_2621624).sum := by decide
  have hdescent : baseEnd_2621624 < baseStart_2621624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621628 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_2621628 : Nat := 118140960795 + 2621628 * 2 ^ 59
def prefixEnd_2621628 : Nat := 4983230072969 + 3 ^ 40 * 2621628 * 2
def baseEnd_2621628 : Nat := 299145613618972022687413

theorem tailTrace_2621628 : CollatzResearch.WordTrace tailWord_2621628 prefixEnd_2621628 299145613618972022687413 := by
  unfold tailWord_2621628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47809314273148484630616769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63745752364197979507489025 47809314273148484630616769)
  ·
    refine ⟨35856985704861363472962577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47809314273148484630616769 35856985704861363472962577)
    ·
      refine ⟨26892739278646022604721933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35856985704861363472962577 26892739278646022604721933)
      ·
        refine ⟨10084777229492258476770725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26892739278646022604721933 10084777229492258476770725)
        ·
          refine ⟨1890895730529798464394511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10084777229492258476770725 1890895730529798464394511)
          ·
            refine ⟨2836343595794697696591767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890895730529798464394511 2836343595794697696591767)
            ·
              refine ⟨4254515393692046544887651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836343595794697696591767 4254515393692046544887651)
              ·
                refine ⟨6381773090538069817331477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254515393692046544887651 6381773090538069817331477)
                ·
                  refine ⟨299145613618972022687413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6381773090538069817331477 299145613618972022687413)
                  ·
                    rfl

theorem cell22_2621628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_2621628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621628 prefixEnd_2621628 := by exact prefixLift 2621628
  have htrace : WordTrace (prefixWord ++ tailWord_2621628) baseStart_2621628 baseEnd_2621628 := by
    simpa [prefixWord, tailWord_2621628, baseEnd_2621628] using wordTrace_append hprefix tailTrace_2621628
  have hstable : (prefixWord ++ tailWord_2621628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621628).length < 2 ^ (prefixWord ++ tailWord_2621628).sum := by decide
  have hdescent : baseEnd_2621628 < baseStart_2621628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621699 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_2621699 : Nat := 118140960795 + 2621699 * 2 ^ 59
def prefixEnd_2621699 : Nat := 4983230072969 + 3 ^ 40 * 2621699 * 2
def baseEnd_2621699 : Nat := 897461145607895549537021

theorem tailTrace_2621699 : CollatzResearch.WordTrace tailWord_2621699 prefixEnd_2621699 897461145607895549537021 := by
  unfold tailWord_2621699
  simp only [CollatzResearch.WordTrace]
  refine ⟨95621218129039748387068151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63747478752693165591378767 95621218129039748387068151)
  ·
    refine ⟨143431827193559622580602227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95621218129039748387068151 143431827193559622580602227)
    ·
      refine ⟨215147740790339433870903341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143431827193559622580602227 215147740790339433870903341)
      ·
        refine ⟨80680402796377287701588753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 215147740790339433870903341 80680402796377287701588753)
        ·
          refine ⟨60510302097282965776191565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80680402796377287701588753 60510302097282965776191565)
          ·
            refine ⟨22691363286481112166071837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60510302097282965776191565 22691363286481112166071837)
            ·
              refine ⟨8509261232430417062276939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22691363286481112166071837 8509261232430417062276939)
              ·
                refine ⟨12763891848645625593415409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509261232430417062276939 12763891848645625593415409)
                ·
                  refine ⟨9572918886484219195061557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12763891848645625593415409 9572918886484219195061557)
                  ·
                    refine ⟨897461145607895549537021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9572918886484219195061557 897461145607895549537021)
                    ·
                      rfl

theorem cell22_2621699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_2621699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621699 prefixEnd_2621699 := by exact prefixLift 2621699
  have htrace : WordTrace (prefixWord ++ tailWord_2621699) baseStart_2621699 baseEnd_2621699 := by
    simpa [prefixWord, tailWord_2621699, baseEnd_2621699] using wordTrace_append hprefix tailTrace_2621699
  have hstable : (prefixWord ++ tailWord_2621699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621699).length < 2 ^ (prefixWord ++ tailWord_2621699).sum := by decide
  have hdescent : baseEnd_2621699 < baseStart_2621699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621731 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 1, 4]
def baseStart_2621731 : Nat := 118140960795 + 2621731 * 2 ^ 59
def prefixEnd_2621731 : Nat := 4983230072969 + 3 ^ 40 * 2621731 * 2
def baseEnd_2621731 : Nat := 897472099861858132736923

theorem tailTrace_2621731 : CollatzResearch.WordTrace tailWord_2621731 prefixEnd_2621731 897472099861858132736923 := by
  unfold tailWord_2621731
  simp only [CollatzResearch.WordTrace]
  refine ⟨95622385264923817852233047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63748256843282545234822031 95622385264923817852233047)
  ·
    refine ⟨143433577897385726778349571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95622385264923817852233047 143433577897385726778349571)
    ·
      refine ⟨215150366846078590167524357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143433577897385726778349571 215150366846078590167524357)
      ·
        refine ⟨40340693783639735656410817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215150366846078590167524357 40340693783639735656410817)
        ·
          refine ⟨30255520337729801742308113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40340693783639735656410817 30255520337729801742308113)
          ·
            refine ⟨22691640253297351306731085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30255520337729801742308113 22691640253297351306731085)
            ·
              refine ⟨8509365094986506740024157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22691640253297351306731085 8509365094986506740024157)
              ·
                refine ⟨3191011910619940027509059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8509365094986506740024157 3191011910619940027509059)
                ·
                  refine ⟨4786517865929910041263589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191011910619940027509059 4786517865929910041263589)
                  ·
                    refine ⟨897472099861858132736923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786517865929910041263589 897472099861858132736923)
                    ·
                      rfl

theorem cell22_2621731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_2621731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621731 prefixEnd_2621731 := by exact prefixLift 2621731
  have htrace : WordTrace (prefixWord ++ tailWord_2621731) baseStart_2621731 baseEnd_2621731 := by
    simpa [prefixWord, tailWord_2621731, baseEnd_2621731] using wordTrace_append hprefix tailTrace_2621731
  have hstable : (prefixWord ++ tailWord_2621731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621731).length < 2 ^ (prefixWord ++ tailWord_2621731).sum := by decide
  have hdescent : baseEnd_2621731 < baseStart_2621731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621735 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 7]
def baseStart_2621735 : Nat := 118140960795 + 2621735 * 2 ^ 59
def prefixEnd_2621735 : Nat := 4983230072969 + 3 ^ 40 * 2621735 * 2
def baseEnd_2621735 : Nat := 299157823047867818545637

theorem tailTrace_2621735 : CollatzResearch.WordTrace tailWord_2621735 prefixEnd_2621735 299157823047867818545637 := by
  unfold tailWord_2621735
  simp only [CollatzResearch.WordTrace]
  refine ⟨95622531156909326535378659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63748354104606217690252439 95622531156909326535378659)
  ·
    refine ⟨143433796735363989803067989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95622531156909326535378659 143433796735363989803067989)
    ·
      refine ⟨1680864805492546755504703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 143433796735363989803067989 1680864805492546755504703)
      ·
        refine ⟨2521297208238820133257055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680864805492546755504703 2521297208238820133257055)
        ·
          refine ⟨3781945812358230199885583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521297208238820133257055 3781945812358230199885583)
          ·
            refine ⟨5672918718537345299828375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3781945812358230199885583 5672918718537345299828375)
            ·
              refine ⟨8509378077806017949742563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672918718537345299828375 8509378077806017949742563)
              ·
                refine ⟨12764067116709026924613845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509378077806017949742563 12764067116709026924613845)
                ·
                  refine ⟨299157823047867818545637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12764067116709026924613845 299157823047867818545637)
                  ·
                    rfl

theorem cell22_2621735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 7].length) (baseStart_2621735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621735 prefixEnd_2621735 := by exact prefixLift 2621735
  have htrace : WordTrace (prefixWord ++ tailWord_2621735) baseStart_2621735 baseEnd_2621735 := by
    simpa [prefixWord, tailWord_2621735, baseEnd_2621735] using wordTrace_append hprefix tailTrace_2621735
  have hstable : (prefixWord ++ tailWord_2621735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621735).length < 2 ^ (prefixWord ++ tailWord_2621735).sum := by decide
  have hdescent : baseEnd_2621735 < baseStart_2621735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621759 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2621759 : Nat := 118140960795 + 2621759 * 2 ^ 59
def prefixEnd_2621759 : Nat := 4983230072969 + 3 ^ 40 * 2621759 * 2
def baseEnd_2621759 : Nat := 897481684834075393036837

theorem tailTrace_2621759 : CollatzResearch.WordTrace tailWord_2621759 prefixEnd_2621759 897481684834075393036837 := by
  unfold tailWord_2621759
  simp only [CollatzResearch.WordTrace]
  refine ⟨95623406508822378634252331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63748937672548252422834887 95623406508822378634252331)
  ·
    refine ⟨143435109763233567951378497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95623406508822378634252331 143435109763233567951378497)
    ·
      refine ⟨107576332322425175963533873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143435109763233567951378497 107576332322425175963533873)
      ·
        refine ⟨80682249241818881972650405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107576332322425175963533873 80682249241818881972650405)
        ·
          refine ⟨15127921732841040369871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80682249241818881972650405 15127921732841040369871951)
          ·
            refine ⟨22691882599261560554807927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15127921732841040369871951 22691882599261560554807927)
            ·
              refine ⟨34037823898892340832211891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22691882599261560554807927 34037823898892340832211891)
              ·
                refine ⟨51056735848338511248317837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34037823898892340832211891 51056735848338511248317837)
                ·
                  refine ⟨19146275943126941718119189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51056735848338511248317837 19146275943126941718119189)
                  ·
                    refine ⟨897481684834075393036837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19146275943126941718119189 897481684834075393036837)
                    ·
                      rfl

theorem cell22_2621759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2621759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621759 prefixEnd_2621759 := by exact prefixLift 2621759
  have htrace : WordTrace (prefixWord ++ tailWord_2621759) baseStart_2621759 baseEnd_2621759 := by
    simpa [prefixWord, tailWord_2621759, baseEnd_2621759] using wordTrace_append hprefix tailTrace_2621759
  have hstable : (prefixWord ++ tailWord_2621759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621759).length < 2 ^ (prefixWord ++ tailWord_2621759).sum := by decide
  have hdescent : baseEnd_2621759 < baseStart_2621759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621780 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2621780 : Nat := 118140960795 + 2621780 * 2 ^ 59
def prefixEnd_2621780 : Nat := 4983230072969 + 3 ^ 40 * 2621780 * 2
def baseEnd_2621780 : Nat := 299162957854412779420591

theorem tailTrace_2621780 : CollatzResearch.WordTrace tailWord_2621780 prefixEnd_2621780 299162957854412779420591 := by
  unfold tailWord_2621780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47812086220873149610383397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63749448294497532813844529 47812086220873149610383397)
  ·
    refine ⟨8964766166413715551946887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47812086220873149610383397 8964766166413715551946887)
    ·
      refine ⟨13447149249620573327920331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964766166413715551946887 13447149249620573327920331)
      ·
        refine ⟨20170723874430859991880497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447149249620573327920331 20170723874430859991880497)
        ·
          refine ⟨15128042905823144993910373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20170723874430859991880497 15128042905823144993910373)
          ·
            refine ⟨2836508044841839686358195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15128042905823144993910373 2836508044841839686358195)
            ·
              refine ⟨4254762067262759529537293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836508044841839686358195 4254762067262759529537293)
              ·
                refine ⟨1595535775223534823576485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4254762067262759529537293 1595535775223534823576485)
                ·
                  refine ⟨299162957854412779420591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595535775223534823576485 299162957854412779420591)
                  ·
                    rfl

theorem cell22_2621780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2621780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621780 prefixEnd_2621780 := by exact prefixLift 2621780
  have htrace : WordTrace (prefixWord ++ tailWord_2621780) baseStart_2621780 baseEnd_2621780 := by
    simpa [prefixWord, tailWord_2621780, baseEnd_2621780] using wordTrace_append hprefix tailTrace_2621780
  have hstable : (prefixWord ++ tailWord_2621780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621780).length < 2 ^ (prefixWord ++ tailWord_2621780).sum := by decide
  have hdescent : baseEnd_2621780 < baseStart_2621780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621846 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2621846 : Nat := 118140960795 + 2621846 * 2 ^ 59
def prefixEnd_2621846 : Nat := 4983230072969 + 3 ^ 40 * 2621846 * 2
def baseEnd_2621846 : Nat := 897511466712036166111571

theorem tailTrace_2621846 : CollatzResearch.WordTrace tailWord_2621846 prefixEnd_2621846 897511466712036166111571 := by
  unfold tailWord_2621846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976661228719199530791837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63751053106338128328446261 5976661228719199530791837)
  ·
    refine ⟨2241247960769699824046939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5976661228719199530791837 2241247960769699824046939)
    ·
      refine ⟨3361871941154549736070409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241247960769699824046939 3361871941154549736070409)
      ·
        refine ⟨2521403955865912302052807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3361871941154549736070409 2521403955865912302052807)
        ·
          refine ⟨3782105933798868453079211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521403955865912302052807 3782105933798868453079211)
          ·
            refine ⟨5673158900698302679618817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782105933798868453079211 5673158900698302679618817)
            ·
              refine ⟨4254869175523727009714113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673158900698302679618817 4254869175523727009714113)
              ·
                refine ⟨3191151881642795257285585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254869175523727009714113 3191151881642795257285585)
                ·
                  refine ⟨2393363911232096442964189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191151881642795257285585 2393363911232096442964189)
                  ·
                    refine ⟨897511466712036166111571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393363911232096442964189 897511466712036166111571)
                    ·
                      rfl

theorem cell22_2621846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2621846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621846 prefixEnd_2621846 := by exact prefixLift 2621846
  have htrace : WordTrace (prefixWord ++ tailWord_2621846) baseStart_2621846 baseEnd_2621846 := by
    simpa [prefixWord, tailWord_2621846, baseEnd_2621846] using wordTrace_append hprefix tailTrace_2621846
  have hstable : (prefixWord ++ tailWord_2621846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621846).length < 2 ^ (prefixWord ++ tailWord_2621846).sum := by decide
  have hdescent : baseEnd_2621846 < baseStart_2621846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621881 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 8]
def baseStart_2621881 : Nat := 118140960795 + 2621881 * 2 ^ 59
def prefixEnd_2621881 : Nat := 4983230072969 + 3 ^ 40 * 2621881 * 2
def baseEnd_2621881 : Nat := 299174482642435913828821

theorem tailTrace_2621881 : CollatzResearch.WordTrace tailWord_2621881 prefixEnd_2621881 299174482642435913828821 := by
  unfold tailWord_2621881
  simp only [CollatzResearch.WordTrace]
  refine ⟨95627856214380393470193497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63751904142920262313462331 95627856214380393470193497)
  ·
    refine ⟨71720892160785295102645123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95627856214380393470193497 71720892160785295102645123)
    ·
      refine ⟨107581338241177942653967685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71720892160785295102645123 107581338241177942653967685)
      ·
        refine ⟨20171500920220864247618941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107581338241177942653967685 20171500920220864247618941)
        ·
          refine ⟨7564312845082824092857103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20171500920220864247618941 7564312845082824092857103)
          ·
            refine ⟨11346469267624236139285655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564312845082824092857103 11346469267624236139285655)
            ·
              refine ⟨17019703901436354208928483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11346469267624236139285655 17019703901436354208928483)
              ·
                refine ⟨25529555852154531313392725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17019703901436354208928483 25529555852154531313392725)
                ·
                  refine ⟨299174482642435913828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25529555852154531313392725 299174482642435913828821)
                  ·
                    rfl

theorem cell22_2621881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_2621881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621881 prefixEnd_2621881 := by exact prefixLift 2621881
  have htrace : WordTrace (prefixWord ++ tailWord_2621881) baseStart_2621881 baseEnd_2621881 := by
    simpa [prefixWord, tailWord_2621881, baseEnd_2621881] using wordTrace_append hprefix tailTrace_2621881
  have hstable : (prefixWord ++ tailWord_2621881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621881).length < 2 ^ (prefixWord ++ tailWord_2621881).sum := by decide
  have hdescent : baseEnd_2621881 < baseStart_2621881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621900 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_2621900 : Nat := 118140960795 + 2621900 * 2 ^ 59
def prefixEnd_2621900 : Nat := 4983230072969 + 3 ^ 40 * 2621900 * 2
def baseEnd_2621900 : Nat := 897529952015598025261405

theorem tailTrace_2621900 : CollatzResearch.WordTrace tailWord_2621900 prefixEnd_2621900 897529952015598025261405 := by
  unfold tailWord_2621900
  simp only [CollatzResearch.WordTrace]
  refine ⟨47814274600655779857567577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63752366134207706476756769 47814274600655779857567577)
  ·
    refine ⟨35860705950491834893175683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47814274600655779857567577 35860705950491834893175683)
    ·
      refine ⟨53791058925737752339763525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35860705950491834893175683 53791058925737752339763525)
      ·
        refine ⟨10085823548575828563705661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53791058925737752339763525 10085823548575828563705661)
        ·
          refine ⟨3782183830715935711389623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10085823548575828563705661 3782183830715935711389623)
          ·
            refine ⟨5673275746073903567084435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782183830715935711389623 5673275746073903567084435)
            ·
              refine ⟨8509913619110855350626653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673275746073903567084435 8509913619110855350626653)
              ·
                refine ⟨3191217607166570756484995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8509913619110855350626653 3191217607166570756484995)
                ·
                  refine ⟨4786826410749856134727493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191217607166570756484995 4786826410749856134727493)
                  ·
                    refine ⟨897529952015598025261405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4786826410749856134727493 897529952015598025261405)
                    ·
                      rfl

theorem cell22_2621900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_2621900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621900 prefixEnd_2621900 := by exact prefixLift 2621900
  have htrace : WordTrace (prefixWord ++ tailWord_2621900) baseStart_2621900 baseEnd_2621900 := by
    simpa [prefixWord, tailWord_2621900, baseEnd_2621900] using wordTrace_append hprefix tailTrace_2621900
  have hstable : (prefixWord ++ tailWord_2621900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621900).length < 2 ^ (prefixWord ++ tailWord_2621900).sum := by decide
  have hdescent : baseEnd_2621900 < baseStart_2621900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621913 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_2621913 : Nat := 118140960795 + 2621913 * 2 ^ 59
def prefixEnd_2621913 : Nat := 4983230072969 + 3 ^ 40 * 2621913 * 2
def baseEnd_2621913 : Nat := 897534402181270324686365

theorem tailTrace_2621913 : CollatzResearch.WordTrace tailWord_2621913 prefixEnd_2621913 897534402181270324686365 := by
  unfold tailWord_2621913
  simp only [CollatzResearch.WordTrace]
  refine ⟨95629023350264462935358393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63752682233509641956905595 95629023350264462935358393)
  ·
    refine ⟨71721767512698347201518795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95629023350264462935358393 71721767512698347201518795)
    ·
      refine ⟨107582651269047520802278193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71721767512698347201518795 107582651269047520802278193)
      ·
        refine ⟨80686988451785640601708645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107582651269047520802278193 80686988451785640601708645)
        ·
          refine ⟨15128810334709807612820371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80686988451785640601708645 15128810334709807612820371)
          ·
            refine ⟨22693215502064711419230557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15128810334709807612820371 22693215502064711419230557)
            ·
              refine ⟨8509955813274266782211459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22693215502064711419230557 8509955813274266782211459)
              ·
                refine ⟨12764933719911400173317189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509955813274266782211459 12764933719911400173317189)
                ·
                  refine ⟨2393425072483387532496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12764933719911400173317189 2393425072483387532496973)
                  ·
                    refine ⟨897534402181270324686365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393425072483387532496973 897534402181270324686365)
                    ·
                      rfl

theorem cell22_2621913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_2621913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621913 prefixEnd_2621913 := by exact prefixLift 2621913
  have htrace : WordTrace (prefixWord ++ tailWord_2621913) baseStart_2621913 baseEnd_2621913 := by
    simpa [prefixWord, tailWord_2621913, baseEnd_2621913] using wordTrace_append hprefix tailTrace_2621913
  have hstable : (prefixWord ++ tailWord_2621913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621913).length < 2 ^ (prefixWord ++ tailWord_2621913).sum := by decide
  have hdescent : baseEnd_2621913 < baseStart_2621913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621930 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_2621930 : Nat := 118140960795 + 2621930 * 2 ^ 59
def prefixEnd_2621930 : Nat := 4983230072969 + 3 ^ 40 * 2621930 * 2
def baseEnd_2621930 : Nat := 897540221628687947011313

theorem tailTrace_2621930 : CollatzResearch.WordTrace tailWord_2621930 prefixEnd_2621930 897540221628687947011313 := by
  unfold tailWord_2621930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23907410847800718709681811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63753095594135249892484829 23907410847800718709681811)
  ·
    refine ⟨35861116271701078064522717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23907410847800718709681811 35861116271701078064522717)
    ·
      refine ⟨13447918601887904274196019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35861116271701078064522717 13447918601887904274196019)
      ·
        refine ⟨20171877902831856411294029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13447918601887904274196019 20171877902831856411294029)
        ·
          refine ⟨7564454213561946154235261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20171877902831856411294029 7564454213561946154235261)
          ·
            refine ⟨2836670330085729807838223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7564454213561946154235261 2836670330085729807838223)
            ·
              refine ⟨4255005495128594711757335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836670330085729807838223 4255005495128594711757335)
              ·
                refine ⟨6382508242692892067636003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255005495128594711757335 6382508242692892067636003)
                ·
                  refine ⟨9573762364039338101454005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382508242692892067636003 9573762364039338101454005)
                  ·
                    refine ⟨897540221628687947011313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9573762364039338101454005 897540221628687947011313)
                    ·
                      rfl

theorem cell22_2621930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_2621930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621930 prefixEnd_2621930 := by exact prefixLift 2621930
  have htrace : WordTrace (prefixWord ++ tailWord_2621930) baseStart_2621930 baseEnd_2621930 := by
    simpa [prefixWord, tailWord_2621930, baseEnd_2621930] using wordTrace_append hprefix tailTrace_2621930
  have hstable : (prefixWord ++ tailWord_2621930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621930).length < 2 ^ (prefixWord ++ tailWord_2621930).sum := by decide
  have hdescent : baseEnd_2621930 < baseStart_2621930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2621971 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 7]
def baseStart_2621971 : Nat := 118140960795 + 2621971 * 2 ^ 59
def prefixEnd_2621971 : Nat := 4983230072969 + 3 ^ 40 * 2621971 * 2
def baseEnd_2621971 : Nat := 299184752255525835578729

theorem tailTrace_2621971 : CollatzResearch.WordTrace tailWord_2621971 prefixEnd_2621971 299184752255525835578729 := by
  unfold tailWord_2621971
  simp only [CollatzResearch.WordTrace]
  refine ⟨95631138784054338840969767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63754092522702892560646511 95631138784054338840969767)
  ·
    refine ⟨143446708176081508261454651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95631138784054338840969767 143446708176081508261454651)
    ·
      refine ⟨215170062264122262392181977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143446708176081508261454651 215170062264122262392181977)
      ·
        refine ⟨161377546698091696794136483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215170062264122262392181977 161377546698091696794136483)
        ·
          refine ⟨242066320047137545191204725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161377546698091696794136483 242066320047137545191204725)
          ·
            refine ⟨22693717504419144861675443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 242066320047137545191204725 22693717504419144861675443)
            ·
              refine ⟨34040576256628717292513165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22693717504419144861675443 34040576256628717292513165)
              ·
                refine ⟨12765216096235768984692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34040576256628717292513165 12765216096235768984692437)
                ·
                  refine ⟨299184752255525835578729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12765216096235768984692437 299184752255525835578729)
                  ·
                    rfl

theorem cell22_2621971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_2621971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2621971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2621971 prefixEnd_2621971 := by exact prefixLift 2621971
  have htrace : WordTrace (prefixWord ++ tailWord_2621971) baseStart_2621971 baseEnd_2621971 := by
    simpa [prefixWord, tailWord_2621971, baseEnd_2621971] using wordTrace_append hprefix tailTrace_2621971
  have hstable : (prefixWord ++ tailWord_2621971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2621971).length < 2 ^ (prefixWord ++ tailWord_2621971).sum := by decide
  have hdescent : baseEnd_2621971 < baseStart_2621971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2621971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622022 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2622022 : Nat := 118140960795 + 2622022 * 2 ^ 59
def prefixEnd_2622022 : Nat := 4983230072969 + 3 ^ 40 * 2622022 * 2
def baseEnd_2622022 : Nat := 299190571702943457903677

theorem tailTrace_2622022 : CollatzResearch.WordTrace tailWord_2622022 prefixEnd_2622022 299190571702943457903677 := by
  unfold tailWord_2622022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988531215839674204721135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63755332604579716367384213 2988531215839674204721135)
  ·
    refine ⟨4482796823759511307081703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2988531215839674204721135 4482796823759511307081703)
    ·
      refine ⟨6724195235639266960622555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4482796823759511307081703 6724195235639266960622555)
      ·
        refine ⟨10086292853458900440933833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724195235639266960622555 10086292853458900440933833)
        ·
          refine ⟨7564719640094175330700375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10086292853458900440933833 7564719640094175330700375)
          ·
            refine ⟨11347079460141262996050563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7564719640094175330700375 11347079460141262996050563)
            ·
              refine ⟨17020619190211894494075845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347079460141262996050563 17020619190211894494075845)
              ·
                refine ⟨3191366098164730217639221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17020619190211894494075845 3191366098164730217639221)
                ·
                  refine ⟨299190571702943457903677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191366098164730217639221 299190571702943457903677)
                  ·
                    rfl

theorem cell22_2622022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2622022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622022 prefixEnd_2622022 := by exact prefixLift 2622022
  have htrace : WordTrace (prefixWord ++ tailWord_2622022) baseStart_2622022 baseEnd_2622022 := by
    simpa [prefixWord, tailWord_2622022, baseEnd_2622022] using wordTrace_append hprefix tailTrace_2622022
  have hstable : (prefixWord ++ tailWord_2622022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622022).length < 2 ^ (prefixWord ++ tailWord_2622022).sum := by decide
  have hdescent : baseEnd_2622022 < baseStart_2622022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622048 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_2622048 : Nat := 118140960795 + 2622048 * 2 ^ 59
def prefixEnd_2622048 : Nat := 4983230072969 + 3 ^ 40 * 2622048 * 2
def baseEnd_2622048 : Nat := 897580615440174972560951

theorem tailTrace_2622048 : CollatzResearch.WordTrace tailWord_2622048 prefixEnd_2622048 897580615440174972560951 := by
  unfold tailWord_2622048
  simp only [CollatzResearch.WordTrace]
  refine ⟨47816973602387690495761399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63755964803183587327681865 47816973602387690495761399)
  ·
    refine ⟨71725460403581535743642099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47816973602387690495761399 71725460403581535743642099)
    ·
      refine ⟨107588190605372303615463149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71725460403581535743642099 107588190605372303615463149)
      ·
        refine ⟨40345571477014613855798681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107588190605372303615463149 40345571477014613855798681)
        ·
          refine ⟨30259178607760960391849011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40345571477014613855798681 30259178607760960391849011)
          ·
            refine ⟨45388767911641440587773517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30259178607760960391849011 45388767911641440587773517)
            ·
              refine ⟨17020787966865540220415069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45388767911641440587773517 17020787966865540220415069)
              ·
                refine ⟨6382795487574577582655651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17020787966865540220415069 6382795487574577582655651)
                ·
                  refine ⟨9574193231361866373983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382795487574577582655651 9574193231361866373983477)
                  ·
                    refine ⟨897580615440174972560951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9574193231361866373983477 897580615440174972560951)
                    ·
                      rfl

theorem cell22_2622048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_2622048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622048 prefixEnd_2622048 := by exact prefixLift 2622048
  have htrace : WordTrace (prefixWord ++ tailWord_2622048) baseStart_2622048 baseEnd_2622048 := by
    simpa [prefixWord, tailWord_2622048, baseEnd_2622048] using wordTrace_append hprefix tailTrace_2622048
  have hstable : (prefixWord ++ tailWord_2622048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622048).length < 2 ^ (prefixWord ++ tailWord_2622048).sum := by decide
  have hdescent : baseEnd_2622048 < baseStart_2622048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622110 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2622110 : Nat := 118140960795 + 2622110 * 2 ^ 59
def prefixEnd_2622110 : Nat := 4983230072969 + 3 ^ 40 * 2622110 * 2
def baseEnd_2622110 : Nat := 897601839307227477510761

theorem tailTrace_2622110 : CollatzResearch.WordTrace tailWord_2622110 prefixEnd_2622110 897601839307227477510761 := by
  unfold tailWord_2622110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954526066318845697534973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63757472353700510386853189 11954526066318845697534973)
  ·
    refine ⟨4482947274869567136575615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11954526066318845697534973 4482947274869567136575615)
    ·
      refine ⟨6724420912304350704863423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4482947274869567136575615 6724420912304350704863423)
      ·
        refine ⟨10086631368456526057295135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724420912304350704863423 10086631368456526057295135)
        ·
          refine ⟨15129947052684789085942703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086631368456526057295135 15129947052684789085942703)
          ·
            refine ⟨22694920579027183628914055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15129947052684789085942703 22694920579027183628914055)
            ·
              refine ⟨34042380868540775443371083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22694920579027183628914055 34042380868540775443371083)
              ·
                refine ⟨51063571302811163165056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34042380868540775443371083 51063571302811163165056625)
                ·
                  refine ⟨38297678477108372373792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51063571302811163165056625 38297678477108372373792469)
                  ·
                    refine ⟨897601839307227477510761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38297678477108372373792469 897601839307227477510761)
                    ·
                      rfl

theorem cell22_2622110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2622110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622110 prefixEnd_2622110 := by exact prefixLift 2622110
  have htrace : WordTrace (prefixWord ++ tailWord_2622110) baseStart_2622110 baseEnd_2622110 := by
    simpa [prefixWord, tailWord_2622110, baseEnd_2622110] using wordTrace_append hprefix tailTrace_2622110
  have hstable : (prefixWord ++ tailWord_2622110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622110).length < 2 ^ (prefixWord ++ tailWord_2622110).sum := by decide
  have hdescent : baseEnd_2622110 < baseStart_2622110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622112 : List Nat := [2, 1, 1, 4, 4, 2, 2, 6]
def baseStart_2622112 : Nat := 118140960795 + 2622112 * 2 ^ 59
def prefixEnd_2622112 : Nat := 4983230072969 + 3 ^ 40 * 2622112 * 2
def baseEnd_2622112 : Nat := 99733613772011126551195

theorem tailTrace_2622112 : CollatzResearch.WordTrace tailWord_2622112 prefixEnd_2622112 99733613772011126551195 := by
  unfold tailWord_2622112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818140738271759960926295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63757520984362346614568393 47818140738271759960926295)
  ·
    refine ⟨71727211107407639941389443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47818140738271759960926295 71727211107407639941389443)
    ·
      refine ⟨107590816661111459912084165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71727211107407639941389443 107590816661111459912084165)
      ·
        refine ⟨20173278123958398733515781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107590816661111459912084165 20173278123958398733515781)
        ·
          refine ⟨3782489648242199762534209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20173278123958398733515781 3782489648242199762534209)
          ·
            refine ⟨2836867236181649821900657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782489648242199762534209 2836867236181649821900657)
            ·
              refine ⟨2127650427136237366425493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836867236181649821900657 2127650427136237366425493)
              ·
                refine ⟨99733613772011126551195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2127650427136237366425493 99733613772011126551195)
                ·
                  rfl

theorem cell22_2622112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_2622112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622112 prefixEnd_2622112 := by exact prefixLift 2622112
  have htrace : WordTrace (prefixWord ++ tailWord_2622112) baseStart_2622112 baseEnd_2622112 := by
    simpa [prefixWord, tailWord_2622112, baseEnd_2622112] using wordTrace_append hprefix tailTrace_2622112
  have hstable : (prefixWord ++ tailWord_2622112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622112).length < 2 ^ (prefixWord ++ tailWord_2622112).sum := by decide
  have hdescent : baseEnd_2622112 < baseStart_2622112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622140 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_2622140 : Nat := 118140960795 + 2622140 * 2 ^ 59
def prefixEnd_2622140 : Nat := 4983230072969 + 3 ^ 40 * 2622140 * 2
def baseEnd_2622140 : Nat := 299204036306772466420223

theorem tailTrace_2622140 : CollatzResearch.WordTrace tailWord_2622140 prefixEnd_2622140 299204036306772466420223 := by
  unfold tailWord_2622140
  simp only [CollatzResearch.WordTrace]
  refine ⟨47818651360221040351935937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63758201813628053802581249 47818651360221040351935937)
  ·
    refine ⟨35863988520165780263951953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47818651360221040351935937 35863988520165780263951953)
    ·
      refine ⟨26897991390124335197963965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35863988520165780263951953 26897991390124335197963965)
      ·
        refine ⟨10086746771296625699236487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26897991390124335197963965 10086746771296625699236487)
        ·
          refine ⟨15130120156944938548854731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086746771296625699236487 15130120156944938548854731)
          ·
            refine ⟨22695180235417407823282097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15130120156944938548854731 22695180235417407823282097)
            ·
              refine ⟨17021385176563055867461573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22695180235417407823282097 17021385176563055867461573)
              ·
                refine ⟨3191509720605572975149045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17021385176563055867461573 3191509720605572975149045)
                ·
                  refine ⟨299204036306772466420223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191509720605572975149045 299204036306772466420223)
                  ·
                    rfl

theorem cell22_2622140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_2622140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622140 prefixEnd_2622140 := by exact prefixLift 2622140
  have htrace : WordTrace (prefixWord ++ tailWord_2622140) baseStart_2622140 baseEnd_2622140 := by
    simpa [prefixWord, tailWord_2622140, baseEnd_2622140] using wordTrace_append hprefix tailTrace_2622140
  have hstable : (prefixWord ++ tailWord_2622140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622140).length < 2 ^ (prefixWord ++ tailWord_2622140).sum := by decide
  have hdescent : baseEnd_2622140 < baseStart_2622140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622150 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2622150 : Nat := 118140960795 + 2622150 * 2 ^ 59
def prefixEnd_2622150 : Nat := 4983230072969 + 3 ^ 40 * 2622150 * 2
def baseEnd_2622150 : Nat := 897615532124680706510639

theorem tailTrace_2622150 : CollatzResearch.WordTrace tailWord_2622150 prefixEnd_2622150 897615532124680706510639 := by
  unfold tailWord_2622150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988677107825182887866747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63758444966937234941157269 2988677107825182887866747)
  ·
    refine ⟨4483015661737774331800121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2988677107825182887866747 4483015661737774331800121)
    ·
      refine ⟨3362261746303330748850091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4483015661737774331800121 3362261746303330748850091)
      ·
        refine ⟨5043392619454996123275137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362261746303330748850091 5043392619454996123275137)
        ·
          refine ⟨3782544464591247092456353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5043392619454996123275137 3782544464591247092456353)
          ·
            refine ⟨2836908348443435319342265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782544464591247092456353 2836908348443435319342265)
            ·
              refine ⟨2127681261332576489506699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836908348443435319342265 2127681261332576489506699)
              ·
                refine ⟨3191521891998864734260049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127681261332576489506699 3191521891998864734260049)
                ·
                  refine ⟨2393641418999148550695037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191521891998864734260049 2393641418999148550695037)
                  ·
                    refine ⟨897615532124680706510639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393641418999148550695037 897615532124680706510639)
                    ·
                      rfl

theorem cell22_2622150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2622150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622150 prefixEnd_2622150 := by exact prefixLift 2622150
  have htrace : WordTrace (prefixWord ++ tailWord_2622150) baseStart_2622150 baseEnd_2622150 := by
    simpa [prefixWord, tailWord_2622150, baseEnd_2622150] using wordTrace_append hprefix tailTrace_2622150
  have hstable : (prefixWord ++ tailWord_2622150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622150).length < 2 ^ (prefixWord ++ tailWord_2622150).sum := by decide
  have hdescent : baseEnd_2622150 < baseStart_2622150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622170 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_2622170 : Nat := 118140960795 + 2622170 * 2 ^ 59
def prefixEnd_2622170 : Nat := 4983230072969 + 3 ^ 40 * 2622170 * 2
def baseEnd_2622170 : Nat := 897622378533407321010577

theorem tailTrace_2622170 : CollatzResearch.WordTrace tailWord_2622170 prefixEnd_2622170 897622378533407321010577 := by
  unfold tailWord_2622170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23909599227583348956865991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63758931273555597218309309 23909599227583348956865991)
  ·
    refine ⟨35864398841375023435298987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23909599227583348956865991 35864398841375023435298987)
    ·
      refine ⟨53796598262062535152948481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35864398841375023435298987 53796598262062535152948481)
      ·
        refine ⟨40347448696546901364711361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53796598262062535152948481 40347448696546901364711361)
        ·
          refine ⟨30260586522410176023533521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40347448696546901364711361 30260586522410176023533521)
          ·
            refine ⟨22695439891807632017650141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30260586522410176023533521 22695439891807632017650141)
            ·
              refine ⟨8510789959427862006618803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22695439891807632017650141 8510789959427862006618803)
              ·
                refine ⟨12766184939141793009928205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8510789959427862006618803 12766184939141793009928205)
                ·
                  refine ⟨4787319352178172378723077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12766184939141793009928205 4787319352178172378723077)
                  ·
                    refine ⟨897622378533407321010577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787319352178172378723077 897622378533407321010577)
                    ·
                      rfl

theorem cell22_2622170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_2622170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622170 prefixEnd_2622170 := by exact prefixLift 2622170
  have htrace : WordTrace (prefixWord ++ tailWord_2622170) baseStart_2622170 baseEnd_2622170 := by
    simpa [prefixWord, tailWord_2622170, baseEnd_2622170] using wordTrace_append hprefix tailTrace_2622170
  have hstable : (prefixWord ++ tailWord_2622170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622170).length < 2 ^ (prefixWord ++ tailWord_2622170).sum := by decide
  have hdescent : baseEnd_2622170 < baseStart_2622170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622217 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_2622217 : Nat := 118140960795 + 2622217 * 2 ^ 59
def prefixEnd_2622217 : Nat := 4983230072969 + 3 ^ 40 * 2622217 * 2
def baseEnd_2622217 : Nat := 897638467593914865085433

theorem tailTrace_2622217 : CollatzResearch.WordTrace tailWord_2622217 prefixEnd_2622217 897638467593914865085433 := by
  unfold tailWord_2622217
  simp only [CollatzResearch.WordTrace]
  refine ⟨95640111141163122854424905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63760074094108748569616603 95640111141163122854424905)
  ·
    refine ⟨71730083355872342140818679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95640111141163122854424905 71730083355872342140818679)
    ·
      refine ⟨107595125033808513211228019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71730083355872342140818679 107595125033808513211228019)
      ·
        refine ⟨161392687550712769816842029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107595125033808513211228019 161392687550712769816842029)
        ·
          refine ⟨60522257831517288681315761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161392687550712769816842029 60522257831517288681315761)
          ·
            refine ⟨45391693373637966510986821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60522257831517288681315761 45391693373637966510986821)
            ·
              refine ⟨8510942507557118720810029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45391693373637966510986821 8510942507557118720810029)
              ·
                refine ⟨3191603440333919520303761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510942507557118720810029 3191603440333919520303761)
                ·
                  refine ⟨2393702580250439640227821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3191603440333919520303761 2393702580250439640227821)
                  ·
                    refine ⟨897638467593914865085433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393702580250439640227821 897638467593914865085433)
                    ·
                      rfl

theorem cell22_2622217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_2622217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622217 prefixEnd_2622217 := by exact prefixLift 2622217
  have htrace : WordTrace (prefixWord ++ tailWord_2622217) baseStart_2622217 baseEnd_2622217 := by
    simpa [prefixWord, tailWord_2622217, baseEnd_2622217] using wordTrace_append hprefix tailTrace_2622217
  have hstable : (prefixWord ++ tailWord_2622217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622217).length < 2 ^ (prefixWord ++ tailWord_2622217).sum := by decide
  have hdescent : baseEnd_2622217 < baseStart_2622217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622326 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2622326 : Nat := 118140960795 + 2622326 * 2 ^ 59
def prefixEnd_2622326 : Nat := 4983230072969 + 3 ^ 40 * 2622326 * 2
def baseEnd_2622326 : Nat := 299225260173824971370033

theorem tailTrace_2622326 : CollatzResearch.WordTrace tailWord_2622326 prefixEnd_2622326 299225260173824971370033 := by
  unfold tailWord_2622326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977755418610514654383927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63762724465178822980095221 5977755418610514654383927)
  ·
    refine ⟨8966633127915771981575891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5977755418610514654383927 8966633127915771981575891)
    ·
      refine ⟨13449949691873657972363837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966633127915771981575891 13449949691873657972363837)
      ·
        refine ⟨5043731134452621739636439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13449949691873657972363837 5043731134452621739636439)
        ·
          refine ⟨7565596701678932609454659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043731134452621739636439 7565596701678932609454659)
          ·
            refine ⟨11348395052518398914181989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565596701678932609454659 11348395052518398914181989)
            ·
              refine ⟨2127824072347199796409123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11348395052518398914181989 2127824072347199796409123)
              ·
                refine ⟨3191736108520799694613685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127824072347199796409123 3191736108520799694613685)
                ·
                  refine ⟨299225260173824971370033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3191736108520799694613685 299225260173824971370033)
                  ·
                    rfl

theorem cell22_2622326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2622326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622326 prefixEnd_2622326 := by exact prefixLift 2622326
  have htrace : WordTrace (prefixWord ++ tailWord_2622326) baseStart_2622326 baseEnd_2622326 := by
    simpa [prefixWord, tailWord_2622326, baseEnd_2622326] using wordTrace_append hprefix tailTrace_2622326
  have hstable : (prefixWord ++ tailWord_2622326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622326).length < 2 ^ (prefixWord ++ tailWord_2622326).sum := by decide
  have hdescent : baseEnd_2622326 < baseStart_2622326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622356 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_2622356 : Nat := 118140960795 + 2622356 * 2 ^ 59
def prefixEnd_2622356 : Nat := 4983230072969 + 3 ^ 40 * 2622356 * 2
def baseEnd_2622356 : Nat := 897686050134564835860007

theorem tailTrace_2622356 : CollatzResearch.WordTrace tailWord_2622356 prefixEnd_2622356 897686050134564835860007 := by
  unfold tailWord_2622356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47822590443829774796867461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63763453925106366395823281 47822590443829774796867461)
  ·
    refine ⟨8966735708218082774412649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47822590443829774796867461 8966735708218082774412649)
    ·
      refine ⟨6725051781163562080809487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8966735708218082774412649 6725051781163562080809487)
      ·
        refine ⟨10087577671745343121214231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725051781163562080809487 10087577671745343121214231)
        ·
          refine ⟨15131366507618014681821347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10087577671745343121214231 15131366507618014681821347)
          ·
            refine ⟨22697049761427022022732021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15131366507618014681821347 22697049761427022022732021)
            ·
              refine ⟨2127848415133783314631127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22697049761427022022732021 2127848415133783314631127)
              ·
                refine ⟨3191772622700674971946691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127848415133783314631127 3191772622700674971946691)
                ·
                  refine ⟨4787658934051012457920037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191772622700674971946691 4787658934051012457920037)
                  ·
                    refine ⟨897686050134564835860007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4787658934051012457920037 897686050134564835860007)
                    ·
                      rfl

theorem cell22_2622356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_2622356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622356 prefixEnd_2622356 := by exact prefixLift 2622356
  have htrace : WordTrace (prefixWord ++ tailWord_2622356) baseStart_2622356 baseEnd_2622356 := by
    simpa [prefixWord, tailWord_2622356, baseEnd_2622356] using wordTrace_append hprefix tailTrace_2622356
  have hstable : (prefixWord ++ tailWord_2622356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622356).length < 2 ^ (prefixWord ++ tailWord_2622356).sum := by decide
  have hdescent : baseEnd_2622356 < baseStart_2622356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622395 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_2622395 : Nat := 118140960795 + 2622395 * 2 ^ 59
def prefixEnd_2622395 : Nat := 4983230072969 + 3 ^ 40 * 2622395 * 2
def baseEnd_2622395 : Nat := 897699400631581734134887

theorem tailTrace_2622395 : CollatzResearch.WordTrace tailWord_2622395 prefixEnd_2622395 897699400631581734134887 := by
  unfold tailWord_2622395
  simp only [CollatzResearch.WordTrace]
  refine ⟨95646603334518259254404639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63764402223012172836269759 95646603334518259254404639)
  ·
    refine ⟨143469905001777388881606959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95646603334518259254404639 143469905001777388881606959)
    ·
      refine ⟨215204857502666083322410439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143469905001777388881606959 215204857502666083322410439)
      ·
        refine ⟨322807286253999124983615659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215204857502666083322410439 322807286253999124983615659)
        ·
          refine ⟨484210929380998687475423489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322807286253999124983615659 484210929380998687475423489)
          ·
            refine ⟨363158197035749015606567617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484210929380998687475423489 363158197035749015606567617)
            ·
              refine ⟨272368647776811761704925713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363158197035749015606567617 272368647776811761704925713)
              ·
                refine ⟨204276485832608821278694285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272368647776811761704925713 204276485832608821278694285)
                ·
                  refine ⟨76603682187228307979510357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204276485832608821278694285 76603682187228307979510357)
                  ·
                    refine ⟨897699400631581734134887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76603682187228307979510357 897699400631581734134887)
                    ·
                      rfl

theorem cell22_2622395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_2622395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622395 prefixEnd_2622395 := by exact prefixLift 2622395
  have htrace : WordTrace (prefixWord ++ tailWord_2622395) baseStart_2622395 baseEnd_2622395 := by
    simpa [prefixWord, tailWord_2622395, baseEnd_2622395] using wordTrace_append hprefix tailTrace_2622395
  have hstable : (prefixWord ++ tailWord_2622395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622395).length < 2 ^ (prefixWord ++ tailWord_2622395).sum := by decide
  have hdescent : baseEnd_2622395 < baseStart_2622395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622431 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 3, 3]
def baseStart_2622431 : Nat := 118140960795 + 2622431 * 2 ^ 59
def prefixEnd_2622431 : Nat := 4983230072969 + 3 ^ 40 * 2622431 * 2
def baseEnd_2622431 : Nat := 897711724167289640234777

theorem tailTrace_2622431 : CollatzResearch.WordTrace tailWord_2622431 prefixEnd_2622431 897711724167289640234777 := by
  unfold tailWord_2622431
  simp only [CollatzResearch.WordTrace]
  refine ⟨95647916362387837402715147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63765277574925224935143431 95647916362387837402715147)
  ·
    refine ⟨143471874543581756104072721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95647916362387837402715147 143471874543581756104072721)
    ·
      refine ⟨107603905907686317078054541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143471874543581756104072721 107603905907686317078054541)
      ·
        refine ⟨40351464715382368904270453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107603905907686317078054541 40351464715382368904270453)
        ·
          refine ⟨3782949817067097084775355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40351464715382368904270453 3782949817067097084775355)
          ·
            refine ⟨5674424725600645627163033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782949817067097084775355 5674424725600645627163033)
            ·
              refine ⟨4255818544200484220372275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5674424725600645627163033 4255818544200484220372275)
              ·
                refine ⟨6383727816300726330558413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255818544200484220372275 6383727816300726330558413)
                ·
                  refine ⟨2393897931112772373959405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6383727816300726330558413 2393897931112772373959405)
                  ·
                    refine ⟨897711724167289640234777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393897931112772373959405 897711724167289640234777)
                    ·
                      rfl

theorem cell22_2622431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_2622431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622431 prefixEnd_2622431 := by exact prefixLift 2622431
  have htrace : WordTrace (prefixWord ++ tailWord_2622431) baseStart_2622431 baseEnd_2622431 := by
    simpa [prefixWord, tailWord_2622431, baseEnd_2622431] using wordTrace_append hprefix tailTrace_2622431
  have hstable : (prefixWord ++ tailWord_2622431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622431).length < 2 ^ (prefixWord ++ tailWord_2622431).sum := by decide
  have hdescent : baseEnd_2622431 < baseStart_2622431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622482 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2622482 : Nat := 118140960795 + 2622482 * 2 ^ 59
def prefixEnd_2622482 : Nat := 4983230072969 + 3 ^ 40 * 2622482 * 2
def baseEnd_2622482 : Nat := 897729182509542507209621

theorem tailTrace_2622482 : CollatzResearch.WordTrace tailWord_2622482 prefixEnd_2622482 897729182509542507209621 := by
  unfold tailWord_2622482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912444121300768278205425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63766517656802048741881133 23912444121300768278205425)
  ·
    refine ⟨17934333090975576208654069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23912444121300768278205425 17934333090975576208654069)
    ·
      refine ⟨1681343727278960269561319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17934333090975576208654069 1681343727278960269561319)
      ·
        refine ⟨2522015590918440404341979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681343727278960269561319 2522015590918440404341979)
        ·
          refine ⟨3783023386377660606512969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522015590918440404341979 3783023386377660606512969)
          ·
            refine ⟨2837267539783245454884727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783023386377660606512969 2837267539783245454884727)
            ·
              refine ⟨4255901309674868182327091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837267539783245454884727 4255901309674868182327091)
              ·
                refine ⟨6383851964512302273490637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255901309674868182327091 6383851964512302273490637)
                ·
                  refine ⟨2393944486692113352558989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6383851964512302273490637 2393944486692113352558989)
                  ·
                    refine ⟨897729182509542507209621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2393944486692113352558989 897729182509542507209621)
                    ·
                      rfl

theorem cell22_2622482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2622482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622482 prefixEnd_2622482 := by exact prefixLift 2622482
  have htrace : WordTrace (prefixWord ++ tailWord_2622482) baseStart_2622482 baseEnd_2622482 := by
    simpa [prefixWord, tailWord_2622482, baseEnd_2622482] using wordTrace_append hprefix tailTrace_2622482
  have hstable : (prefixWord ++ tailWord_2622482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622482).length < 2 ^ (prefixWord ++ tailWord_2622482).sum := by decide
  have hdescent : baseEnd_2622482 < baseStart_2622482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622489 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 4]
def baseStart_2622489 : Nat := 118140960795 + 2622489 * 2 ^ 59
def prefixEnd_2622489 : Nat := 4983230072969 + 3 ^ 40 * 2622489 * 2
def baseEnd_2622489 : Nat := 299243859584198940761533

theorem tailTrace_2622489 : CollatzResearch.WordTrace tailWord_2622489 prefixEnd_2622489 299243859584198940761533 := by
  unfold tailWord_2622489
  simp only [CollatzResearch.WordTrace]
  refine ⟨95650031796177713308326521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63766687864118475538884347 95650031796177713308326521)
  ·
    refine ⟨71737523847133284981244891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95650031796177713308326521 71737523847133284981244891)
    ·
      refine ⟨107606285770699927471867337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71737523847133284981244891 107606285770699927471867337)
      ·
        refine ⟨80704714328024945603900503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107606285770699927471867337 80704714328024945603900503)
        ·
          refine ⟨121057071492037418405850755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80704714328024945603900503 121057071492037418405850755)
          ·
            refine ⟨181585607238056127608776133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121057071492037418405850755 181585607238056127608776133)
            ·
              refine ⟨34047301357135523926645525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181585607238056127608776133 34047301357135523926645525)
              ·
                refine ⟨1595967251115727684061509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34047301357135523926645525 1595967251115727684061509)
                ·
                  refine ⟨299243859584198940761533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595967251115727684061509 299243859584198940761533)
                  ·
                    rfl

theorem cell22_2622489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_2622489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622489 prefixEnd_2622489 := by exact prefixLift 2622489
  have htrace : WordTrace (prefixWord ++ tailWord_2622489) baseStart_2622489 baseEnd_2622489 := by
    simpa [prefixWord, tailWord_2622489, baseEnd_2622489] using wordTrace_append hprefix tailTrace_2622489
  have hstable : (prefixWord ++ tailWord_2622489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622489).length < 2 ^ (prefixWord ++ tailWord_2622489).sum := by decide
  have hdescent : baseEnd_2622489 < baseStart_2622489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622547 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_2622547 : Nat := 118140960795 + 2622547 * 2 ^ 59
def prefixEnd_2622547 : Nat := 4983230072969 + 3 ^ 40 * 2622547 * 2
def baseEnd_2622547 : Nat := 897751433337904004334421

theorem tailTrace_2622547 : CollatzResearch.WordTrace tailWord_2622547 prefixEnd_2622547 897751433337904004334421 := by
  unfold tailWord_2622547
  simp only [CollatzResearch.WordTrace]
  refine ⟨95652147229967589213937895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63768098153311726142625263 95652147229967589213937895)
  ·
    refine ⟨143478220844951383820906843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95652147229967589213937895 143478220844951383820906843)
    ·
      refine ⟨215217331267427075731360265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143478220844951383820906843 215217331267427075731360265)
      ·
        refine ⟨161412998450570306798520199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215217331267427075731360265 161412998450570306798520199)
        ·
          refine ⟨242119497675855460197780299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161412998450570306798520199 242119497675855460197780299)
          ·
            refine ⟨363179246513783190296670449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242119497675855460197780299 363179246513783190296670449)
            ·
              refine ⟨272384434885337392722502837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363179246513783190296670449 272384434885337392722502837)
              ·
                refine ⟨25536040770500380567734641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272384434885337392722502837 25536040770500380567734641)
                ·
                  refine ⟨19152030577875285425800981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25536040770500380567734641 19152030577875285425800981)
                  ·
                    refine ⟨897751433337904004334421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19152030577875285425800981 897751433337904004334421)
                    ·
                      rfl

theorem cell22_2622547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_2622547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622547 prefixEnd_2622547 := by exact prefixLift 2622547
  have htrace : WordTrace (prefixWord ++ tailWord_2622547) baseStart_2622547 baseEnd_2622547 := by
    simpa [prefixWord, tailWord_2622547, baseEnd_2622547] using wordTrace_append hprefix tailTrace_2622547
  have hstable : (prefixWord ++ tailWord_2622547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622547).length < 2 ^ (prefixWord ++ tailWord_2622547).sum := by decide
  have hdescent : baseEnd_2622547 < baseStart_2622547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622568 : List Nat := [2, 1, 4, 4, 1, 1, 3, 6]
def baseStart_2622568 : Nat := 118140960795 + 2622568 * 2 ^ 59
def prefixEnd_2622568 : Nat := 4983230072969 + 3 ^ 40 * 2622568 * 2
def baseEnd_2622568 : Nat := 99750958007451883284373

theorem tailTrace_2622568 : CollatzResearch.WordTrace tailWord_2622568 prefixEnd_2622568 99750958007451883284373 := by
  unfold tailWord_2622568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47826456581445754900226179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63768608775261006533634905 47826456581445754900226179)
  ·
    refine ⟨71739684872168632350339269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47826456581445754900226179 71739684872168632350339269)
    ·
      refine ⟨13451190913531618565688613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71739684872168632350339269 13451190913531618565688613)
      ·
        refine ⟨2522098296287178481066615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13451190913531618565688613 2522098296287178481066615)
        ·
          refine ⟨3783147444430767721599923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522098296287178481066615 3783147444430767721599923)
          ·
            refine ⟨5674721166646151582399885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783147444430767721599923 5674721166646151582399885)
            ·
              refine ⟨2128020437492306843399957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5674721166646151582399885 2128020437492306843399957)
              ·
                refine ⟨99750958007451883284373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2128020437492306843399957 99750958007451883284373)
                ·
                  rfl

theorem cell22_2622568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_2622568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622568 prefixEnd_2622568 := by exact prefixLift 2622568
  have htrace : WordTrace (prefixWord ++ tailWord_2622568) baseStart_2622568 baseEnd_2622568 := by
    simpa [prefixWord, tailWord_2622568, baseEnd_2622568] using wordTrace_append hprefix tailTrace_2622568
  have hstable : (prefixWord ++ tailWord_2622568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622568).length < 2 ^ (prefixWord ++ tailWord_2622568).sum := by decide
  have hdescent : baseEnd_2622568 < baseStart_2622568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622583 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2622583 : Nat := 118140960795 + 2622583 * 2 ^ 59
def prefixEnd_2622583 : Nat := 4983230072969 + 3 ^ 40 * 2622583 * 2
def baseEnd_2622583 : Nat := 897763756873611910434311

theorem tailTrace_2622583 : CollatzResearch.WordTrace tailWord_2622583 prefixEnd_2622583 897763756873611910434311 := by
  unfold tailWord_2622583
  simp only [CollatzResearch.WordTrace]
  refine ⟨95653460257837167362248403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63768973505224778241498935 95653460257837167362248403)
  ·
    refine ⟨143480190386755751043372605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95653460257837167362248403 143480190386755751043372605)
    ·
      refine ⟨53805071395033406641264727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143480190386755751043372605 53805071395033406641264727)
      ·
        refine ⟨80707607092550109961897091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53805071395033406641264727 80707607092550109961897091)
        ·
          refine ⟨121061410638825164942845637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80707607092550109961897091 121061410638825164942845637)
          ·
            refine ⟨22699014494779718426783557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121061410638825164942845637 22699014494779718426783557)
            ·
              refine ⟨4256065217771197205021917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22699014494779718426783557 4256065217771197205021917)
              ·
                refine ⟨1596024456664198951883219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256065217771197205021917 1596024456664198951883219)
                ·
                  refine ⟨2394036684996298427824829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596024456664198951883219 2394036684996298427824829)
                  ·
                    refine ⟨897763756873611910434311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394036684996298427824829 897763756873611910434311)
                    ·
                      rfl

theorem cell22_2622583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2622583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622583 prefixEnd_2622583 := by exact prefixLift 2622583
  have htrace : WordTrace (prefixWord ++ tailWord_2622583) baseStart_2622583 baseEnd_2622583 := by
    simpa [prefixWord, tailWord_2622583, baseEnd_2622583] using wordTrace_append hprefix tailTrace_2622583
  have hstable : (prefixWord ++ tailWord_2622583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622583).length < 2 ^ (prefixWord ++ tailWord_2622583).sum := by decide
  have hdescent : baseEnd_2622583 < baseStart_2622583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622596 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_2622596 : Nat := 118140960795 + 2622596 * 2 ^ 59
def prefixEnd_2622596 : Nat := 4983230072969 + 3 ^ 40 * 2622596 * 2
def baseEnd_2622596 : Nat := 299256069013094736619757

theorem tailTrace_2622596 : CollatzResearch.WordTrace tailWord_2622596 prefixEnd_2622596 299256069013094736619757 := by
  unfold tailWord_2622596
  simp only [CollatzResearch.WordTrace]
  refine ⟨47826967203395035291235821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63769289604526713721647761 47826967203395035291235821)
  ·
    refine ⟨17935112701273138234213433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47826967203395035291235821 17935112701273138234213433)
    ·
      refine ⟨13451334525954853675660075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17935112701273138234213433 13451334525954853675660075)
      ·
        refine ⟨20177001788932280513490113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451334525954853675660075 20177001788932280513490113)
        ·
          refine ⟨15132751341699210385117585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20177001788932280513490113 15132751341699210385117585)
          ·
            refine ⟨11349563506274407788838189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15132751341699210385117585 11349563506274407788838189)
            ·
              refine ⟨4256086314852902920814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11349563506274407788838189 4256086314852902920814321)
              ·
                refine ⟨3192064736139677190610741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256086314852902920814321 3192064736139677190610741)
                ·
                  refine ⟨299256069013094736619757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192064736139677190610741 299256069013094736619757)
                  ·
                    rfl

theorem cell22_2622596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_2622596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622596 prefixEnd_2622596 := by exact prefixLift 2622596
  have htrace : WordTrace (prefixWord ++ tailWord_2622596) baseStart_2622596 baseEnd_2622596 := by
    simpa [prefixWord, tailWord_2622596, baseEnd_2622596] using wordTrace_append hprefix tailTrace_2622596
  have hstable : (prefixWord ++ tailWord_2622596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622596).length < 2 ^ (prefixWord ++ tailWord_2622596).sum := by decide
  have hdescent : baseEnd_2622596 < baseStart_2622596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622624 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_2622624 : Nat := 118140960795 + 2622624 * 2 ^ 59
def prefixEnd_2622624 : Nat := 4983230072969 + 3 ^ 40 * 2622624 * 2
def baseEnd_2622624 : Nat := 299259264003833823386395

theorem tailTrace_2622624 : CollatzResearch.WordTrace tailWord_2622624 prefixEnd_2622624 299259264003833823386395 := by
  unfold tailWord_2622624
  simp only [CollatzResearch.WordTrace]
  refine ⟨47827477825344315682245463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63769970433792420909660617 47827477825344315682245463)
  ·
    refine ⟨71741216738016473523368195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47827477825344315682245463 71741216738016473523368195)
    ·
      refine ⟨107611825107024710285052293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71741216738016473523368195 107611825107024710285052293)
      ·
        refine ⟨20177217207567133178447305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107611825107024710285052293 20177217207567133178447305)
        ·
          refine ⟨15132912905675349883835479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20177217207567133178447305 15132912905675349883835479)
          ·
            refine ⟨22699369358513024825753219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15132912905675349883835479 22699369358513024825753219)
            ·
              refine ⟨34049054037769537238629829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22699369358513024825753219 34049054037769537238629829)
              ·
                refine ⟨6384197632081788232243093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34049054037769537238629829 6384197632081788232243093)
                ·
                  refine ⟨299259264003833823386395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6384197632081788232243093 299259264003833823386395)
                  ·
                    rfl

theorem cell22_2622624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_2622624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622624 prefixEnd_2622624 := by exact prefixLift 2622624
  have htrace : WordTrace (prefixWord ++ tailWord_2622624) baseStart_2622624 baseEnd_2622624 := by
    simpa [prefixWord, tailWord_2622624, baseEnd_2622624] using wordTrace_append hprefix tailTrace_2622624
  have hstable : (prefixWord ++ tailWord_2622624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622624).length < 2 ^ (prefixWord ++ tailWord_2622624).sum := by decide
  have hdescent : baseEnd_2622624 < baseStart_2622624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622639 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_2622639 : Nat := 118140960795 + 2622639 * 2 ^ 59
def prefixEnd_2622639 : Nat := 4983230072969 + 3 ^ 40 * 2622639 * 2
def baseEnd_2622639 : Nat := 897782926818046431034139

theorem tailTrace_2622639 : CollatzResearch.WordTrace tailWord_2622639 prefixEnd_2622639 897782926818046431034139 := by
  unfold tailWord_2622639
  simp only [CollatzResearch.WordTrace]
  refine ⟨95655502745634288926286971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63770335163756192617524647 95655502745634288926286971)
  ·
    refine ⟨143483254118451433389430457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95655502745634288926286971 143483254118451433389430457)
    ·
      refine ⟨107612440588838575042072843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143483254118451433389430457 107612440588838575042072843)
      ·
        refine ⟨161418660883257862563109265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107612440588838575042072843 161418660883257862563109265)
        ·
          refine ⟨121063995662443396922331949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161418660883257862563109265 121063995662443396922331949)
          ·
            refine ⟨45398998373416273845874481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121063995662443396922331949 45398998373416273845874481)
            ·
              refine ⟨34049248780062205384405861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45398998373416273845874481 34049248780062205384405861)
              ·
                refine ⟨6384234146261663509576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34049248780062205384405861 6384234146261663509576099)
                ·
                  refine ⟨9576351219392495264364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6384234146261663509576099 9576351219392495264364149)
                  ·
                    refine ⟨897782926818046431034139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9576351219392495264364149 897782926818046431034139)
                    ·
                      rfl

theorem cell22_2622639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_2622639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622639 prefixEnd_2622639 := by exact prefixLift 2622639
  have htrace : WordTrace (prefixWord ++ tailWord_2622639) baseStart_2622639 baseEnd_2622639 := by
    simpa [prefixWord, tailWord_2622639, baseEnd_2622639] using wordTrace_append hprefix tailTrace_2622639
  have hstable : (prefixWord ++ tailWord_2622639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622639).length < 2 ^ (prefixWord ++ tailWord_2622639).sum := by decide
  have hdescent : baseEnd_2622639 < baseStart_2622639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622731 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 5]
def baseStart_2622731 : Nat := 118140960795 + 2622731 * 2 ^ 59
def prefixEnd_2622731 : Nat := 4983230072969 + 3 ^ 40 * 2622731 * 2
def baseEnd_2622731 : Nat := 299271473432729619244619

theorem tailTrace_2622731 : CollatzResearch.WordTrace tailWord_2622731 prefixEnd_2622731 299271473432729619244619 := by
  unfold tailWord_2622731
  simp only [CollatzResearch.WordTrace]
  refine ⟨95658858261300988638636047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63772572174200659092424031 95658858261300988638636047)
  ·
    refine ⟨143488287391951482957954071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95658858261300988638636047 143488287391951482957954071)
    ·
      refine ⟨215232431087927224436931107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143488287391951482957954071 215232431087927224436931107)
      ·
        refine ⟨322848646631890836655396661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215232431087927224436931107 322848646631890836655396661)
        ·
          refine ⟨30267060621739765936443437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322848646631890836655396661 30267060621739765936443437)
          ·
            refine ⟨11350147733152412226166289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30267060621739765936443437 11350147733152412226166289)
            ·
              refine ⟨8512610799864309169624717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11350147733152412226166289 8512610799864309169624717)
              ·
                refine ⟨3192229049949115938609269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8512610799864309169624717 3192229049949115938609269)
                ·
                  refine ⟨299271473432729619244619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192229049949115938609269 299271473432729619244619)
                  ·
                    rfl

theorem cell22_2622731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].length) (baseStart_2622731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622731 prefixEnd_2622731 := by exact prefixLift 2622731
  have htrace : WordTrace (prefixWord ++ tailWord_2622731) baseStart_2622731 baseEnd_2622731 := by
    simpa [prefixWord, tailWord_2622731, baseEnd_2622731] using wordTrace_append hprefix tailTrace_2622731
  have hstable : (prefixWord ++ tailWord_2622731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622731).length < 2 ^ (prefixWord ++ tailWord_2622731).sum := by decide
  have hdescent : baseEnd_2622731 < baseStart_2622731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622752 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_2622752 : Nat := 118140960795 + 2622752 * 2 ^ 59
def prefixEnd_2622752 : Nat := 4983230072969 + 3 ^ 40 * 2622752 * 2
def baseEnd_2622752 : Nat := 897821609027351802958793

theorem tailTrace_2622752 : CollatzResearch.WordTrace tailWord_2622752 prefixEnd_2622752 897821609027351802958793 := by
  unfold tailWord_2622752
  simp only [CollatzResearch.WordTrace]
  refine ⟨47829812097112454612575255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63773082796149939483433673 47829812097112454612575255)
  ·
    refine ⟨71744718145668681918862883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47829812097112454612575255 71744718145668681918862883)
    ·
      refine ⟨107617077218503022878294325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71744718145668681918862883 107617077218503022878294325)
      ·
        refine ⟨10089100989234658394840093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107617077218503022878294325 10089100989234658394840093)
        ·
          refine ⟨3783412870962996898065035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10089100989234658394840093 3783412870962996898065035)
          ·
            refine ⟨5675119306444495347097553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783412870962996898065035 5675119306444495347097553)
            ·
              refine ⟨4256339479833371510323165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675119306444495347097553 4256339479833371510323165)
              ·
                refine ⟨1596127304937514316371187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256339479833371510323165 1596127304937514316371187)
                ·
                  refine ⟨2394190957406271474556781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596127304937514316371187 2394190957406271474556781)
                  ·
                    refine ⟨897821609027351802958793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394190957406271474556781 897821609027351802958793)
                    ·
                      rfl

theorem cell22_2622752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_2622752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622752 prefixEnd_2622752 := by exact prefixLift 2622752
  have htrace : WordTrace (prefixWord ++ tailWord_2622752) baseStart_2622752 baseEnd_2622752 := by
    simpa [prefixWord, tailWord_2622752, baseEnd_2622752] using wordTrace_append hprefix tailTrace_2622752
  have hstable : (prefixWord ++ tailWord_2622752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622752).length < 2 ^ (prefixWord ++ tailWord_2622752).sum := by decide
  have hdescent : baseEnd_2622752 < baseStart_2622752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622765 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2622765 : Nat := 118140960795 + 2622765 * 2 ^ 59
def prefixEnd_2622765 : Nat := 4983230072969 + 3 ^ 40 * 2622765 * 2
def baseEnd_2622765 : Nat := 299275353064341367461251

theorem tailTrace_2622765 : CollatzResearch.WordTrace tailWord_2622765 prefixEnd_2622765 299275353064341367461251 := by
  unfold tailWord_2622765
  simp only [CollatzResearch.WordTrace]
  refine ⟨95660098343177812445373749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63773398895451874963582499 95660098343177812445373749)
  ·
    refine ⟨8968134219672919916753789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95660098343177812445373749 8968134219672919916753789)
    ·
      refine ⟨3363050332377344968782671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968134219672919916753789 3363050332377344968782671)
      ·
        refine ⟨5044575498566017453174007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363050332377344968782671 5044575498566017453174007)
        ·
          refine ⟨7566863247849026179761011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044575498566017453174007 7566863247849026179761011)
          ·
            refine ⟨11350294871773539269641517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566863247849026179761011 11350294871773539269641517)
            ·
              refine ⟨4256360576915077226115569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11350294871773539269641517 4256360576915077226115569)
              ·
                refine ⟨3192270432686307919586677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256360576915077226115569 3192270432686307919586677)
                ·
                  refine ⟨299275353064341367461251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192270432686307919586677 299275353064341367461251)
                  ·
                    rfl

theorem cell22_2622765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2622765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622765 prefixEnd_2622765 := by exact prefixLift 2622765
  have htrace : WordTrace (prefixWord ++ tailWord_2622765) baseStart_2622765 baseEnd_2622765 := by
    simpa [prefixWord, tailWord_2622765, baseEnd_2622765] using wordTrace_append hprefix tailTrace_2622765
  have hstable : (prefixWord ++ tailWord_2622765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622765).length < 2 ^ (prefixWord ++ tailWord_2622765).sum := by decide
  have hdescent : baseEnd_2622765 < baseStart_2622765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622846 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2622846 : Nat := 118140960795 + 2622846 * 2 ^ 59
def prefixEnd_2622846 : Nat := 4983230072969 + 3 ^ 40 * 2622846 * 2
def baseEnd_2622846 : Nat := 897853787148366891108505

theorem tailTrace_2622846 : CollatzResearch.WordTrace tailWord_2622846 prefixEnd_2622846 897853787148366891108505 := by
  unfold tailWord_2622846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957881581985545409884049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63775368437256242186048261 11957881581985545409884049)
  ·
    refine ⟨8968411186489159057413037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11957881581985545409884049 8968411186489159057413037)
    ·
      refine ⟨3363154194933434646529889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968411186489159057413037 3363154194933434646529889)
      ·
        refine ⟨2522365646200075984897417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3363154194933434646529889 2522365646200075984897417)
        ·
          refine ⟨1891774234650056988673063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2522365646200075984897417 1891774234650056988673063)
          ·
            refine ⟨2837661351975085483009595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891774234650056988673063 2837661351975085483009595)
            ·
              refine ⟨4256492027962628224514393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837661351975085483009595 4256492027962628224514393)
              ·
                refine ⟨3192369020971971168385795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256492027962628224514393 3192369020971971168385795)
                ·
                  refine ⟨4788553531457956752578693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192369020971971168385795 4788553531457956752578693)
                  ·
                    refine ⟨897853787148366891108505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4788553531457956752578693 897853787148366891108505)
                    ·
                      rfl

theorem cell22_2622846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2622846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622846 prefixEnd_2622846 := by exact prefixLift 2622846
  have htrace : WordTrace (prefixWord ++ tailWord_2622846) baseStart_2622846 baseEnd_2622846 := by
    simpa [prefixWord, tailWord_2622846, baseEnd_2622846] using wordTrace_append hprefix tailTrace_2622846
  have hstable : (prefixWord ++ tailWord_2622846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622846).length < 2 ^ (prefixWord ++ tailWord_2622846).sum := by decide
  have hdescent : baseEnd_2622846 < baseStart_2622846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622853 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2622853 : Nat := 118140960795 + 2622853 * 2 ^ 59
def prefixEnd_2622853 : Nat := 4983230072969 + 3 ^ 40 * 2622853 * 2
def baseEnd_2622853 : Nat := 897856183391421206183483

theorem tailTrace_2622853 : CollatzResearch.WordTrace tailWord_2622853 prefixEnd_2622853 897856183391421206183483 := by
  unfold tailWord_2622853
  simp only [CollatzResearch.WordTrace]
  refine ⟨95663307966859003474577213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63775538644572668983051475 95663307966859003474577213)
  ·
    refine ⟨35873740487572126302966455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95663307966859003474577213 35873740487572126302966455)
    ·
      refine ⟨53810610731358189454449683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35873740487572126302966455 53810610731358189454449683)
      ·
        refine ⟨80715916097037284181674525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53810610731358189454449683 80715916097037284181674525)
        ·
          refine ⟨30268468536388981568127947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80715916097037284181674525 30268468536388981568127947)
          ·
            refine ⟨45402702804583472352191921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30268468536388981568127947 45402702804583472352191921)
            ·
              refine ⟨34052027103437604264143941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45402702804583472352191921 34052027103437604264143941)
              ·
                refine ⟨6384755081894550799526989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34052027103437604264143941 6384755081894550799526989)
                ·
                  refine ⟨2394283155710456549822621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6384755081894550799526989 2394283155710456549822621)
                  ·
                    refine ⟨897856183391421206183483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2394283155710456549822621 897856183391421206183483)
                    ·
                      rfl

theorem cell22_2622853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2622853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622853 prefixEnd_2622853 := by exact prefixLift 2622853
  have htrace : WordTrace (prefixWord ++ tailWord_2622853) baseStart_2622853 baseEnd_2622853 := by
    simpa [prefixWord, tailWord_2622853, baseEnd_2622853] using wordTrace_append hprefix tailTrace_2622853
  have hstable : (prefixWord ++ tailWord_2622853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622853).length < 2 ^ (prefixWord ++ tailWord_2622853).sum := by decide
  have hdescent : baseEnd_2622853 < baseStart_2622853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2622883 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 5]
def baseStart_2622883 : Nat := 118140960795 + 2622883 * 2 ^ 59
def prefixEnd_2622883 : Nat := 4983230072969 + 3 ^ 40 * 2622883 * 2
def baseEnd_2622883 : Nat := 299288817668170375977797

theorem tailTrace_2622883 : CollatzResearch.WordTrace tailWord_2622883 prefixEnd_2622883 299288817668170375977797 := by
  unfold tailWord_2622883
  simp only [CollatzResearch.WordTrace]
  refine ⟨95664402156750318598169303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63776268104500212398779535 95664402156750318598169303)
  ·
    refine ⟨143496603235125477897253955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95664402156750318598169303 143496603235125477897253955)
    ·
      refine ⟨215244904852688216845880933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143496603235125477897253955 215244904852688216845880933)
      ·
        refine ⟨40358419659879040658602675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 215244904852688216845880933 40358419659879040658602675)
        ·
          refine ⟨60537629489818560987904013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40358419659879040658602675 60537629489818560987904013)
          ·
            refine ⟨22701611058681960370464005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60537629489818560987904013 22701611058681960370464005)
            ·
              refine ⟨4256552073502867569462001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22701611058681960370464005 4256552073502867569462001)
              ·
                refine ⟨3192414055127150677096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256552073502867569462001 3192414055127150677096501)
                ·
                  refine ⟨299288817668170375977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192414055127150677096501 299288817668170375977797)
                  ·
                    rfl

theorem cell22_2622883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].length) (baseStart_2622883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2622883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2622883 prefixEnd_2622883 := by exact prefixLift 2622883
  have htrace : WordTrace (prefixWord ++ tailWord_2622883) baseStart_2622883 baseEnd_2622883 := by
    simpa [prefixWord, tailWord_2622883, baseEnd_2622883] using wordTrace_append hprefix tailTrace_2622883
  have hstable : (prefixWord ++ tailWord_2622883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2622883).length < 2 ^ (prefixWord ++ tailWord_2622883).sum := by decide
  have hdescent : baseEnd_2622883 < baseStart_2622883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2622883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
